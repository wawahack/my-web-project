#!/usr/bin/env python3
"""Headshot x store - ร้านขายไฟล์โค้ดดิจิทัล (Flask + SQLite)

แอดมินอัปโหลดไฟล์อะไรก็ได้เข้าสินค้า (.js .css .py .cpp .json .zip ฯลฯ)
ลูกค้าจ่ายผ่านพร้อมเพย์ แนบสลิป แอดมินอนุมัติ แล้วโหลดไฟล์ได้จากหน้าออเดอร์

รัน:  python app.py          (ทดลอง)      python app.py seed   (ใส่สินค้าตัวอย่าง)
      gunicorn app:app       (ใช้งานจริง)
"""
import hmac
import io
import os
import re
import secrets
import sqlite3
import sys
import tempfile
import time
import zipfile
import zlib
from datetime import datetime, timedelta, timezone
from functools import wraps
from contextlib import contextmanager

from flask import (Flask, Response, abort, flash, g, jsonify, redirect, render_template,
                   request, send_file, send_from_directory, session, url_for)
from markupsafe import Markup, escape

BASE = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("DB_PATH", os.path.join(BASE, "shop.db"))
DATA_DIR = os.environ.get("UPLOAD_DIR", os.path.join(BASE, "uploads"))
FILES_DIR = os.path.join(DATA_DIR, "files")
SLIPS_DIR = os.path.join(DATA_DIR, "slips")
QR_DIR = os.path.join(DATA_DIR, "qr")
SHOP_NAME = os.environ.get("SHOP_NAME", "Headshot x store")
PROMPTPAY_ID = re.sub(r"\D", "", os.environ.get("PROMPTPAY_ID", ""))
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
HOLD_MIN = int(os.environ.get("HOLD_MINUTES", "30"))
MAX_UPLOAD_MB = int(os.environ.get("MAX_UPLOAD_MB", "200"))
BEHIND_PROXY = os.environ.get("BEHIND_PROXY") == "1"  # เปิดเมื่อรันหลัง cloudflared/nginx เท่านั้น
SLIP_MAX = 6 * 1024 * 1024
# หมวดเป็นข้อความที่แอดมินพิมพ์เอง (แสดงเป็นตัวอักษรใหญ่บนปก) ค่าเก่าแบบรหัสจะถูกแปลงเป็นข้อความตอนเริ่มระบบ
LEGACY_CATS = {"js": "JS", "css": "CSS", "py": "PYTHON", "cpp": "C++", "web": "WEB", "other": "CODE"}
SUGGEST_CATS = ["JS", "CSS", "PYTHON", "C++", "HTML", "BOT"]
TONE_ALIASES = {
    "js": ("js", "javascript", "node", "nodejs", "ts", "typescript", "react", "vue", "json"),
    "css": ("css", "scss", "sass", "tailwind", "style"),
    "py": ("py", "python", "django", "flask", "ai", "ml"),
    "cpp": ("c", "c++", "cpp", "c#", "cs", "java", "rust", "go"),
    "web": ("web", "html", "ui", "ux", "php", "wordpress"),
}
STATUS_TH = {"pending": "รอชำระเงิน", "verifying": "รอตรวจสลิป", "paid": "ชำระแล้ว",
             "cancelled": "ยกเลิก", "expired": "หมดเวลา"}
for _d in (FILES_DIR, SLIPS_DIR, QR_DIR):
    os.makedirs(_d, exist_ok=True)


def safe_eq(a, b):
    """เทียบข้อความแบบเวลาคงที่ รองรับภาษาไทย (hmac.compare_digest กับ str จะพังถ้ามีตัวอักษรนอก ASCII)"""
    return hmac.compare_digest(str(a).encode("utf-8"), str(b).encode("utf-8"))


def _secret_key():
    k = os.environ.get("SECRET_KEY")
    if k:
        return k
    p = os.path.join(BASE, ".secret_key")
    if not os.path.exists(p):
        with open(p, "w") as f:
            f.write(secrets.token_hex(32))
        os.chmod(p, 0o600)
    with open(p) as f:
        return f.read().strip()


app = Flask(__name__)
app.secret_key = _secret_key()
app.config.update(
    MAX_CONTENT_LENGTH=MAX_UPLOAD_MB * 1024 * 1024,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("SECURE_COOKIES") == "1",
)

SCHEMA = """
CREATE TABLE IF NOT EXISTS products(
  id INTEGER PRIMARY KEY AUTOINCREMENT, cat TEXT NOT NULL DEFAULT 'other', name TEXT NOT NULL,
  tag TEXT NOT NULL DEFAULT '', description TEXT NOT NULL DEFAULT '', preview TEXT NOT NULL DEFAULT '',
  price INTEGER NOT NULL, was INTEGER, stock INTEGER, active INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS files(
  id INTEGER PRIMARY KEY AUTOINCREMENT, product_id INTEGER NOT NULL, stored TEXT NOT NULL,
  name TEXT NOT NULL, size INTEGER NOT NULL, created TEXT NOT NULL);
CREATE INDEX IF NOT EXISTS ix_files ON files(product_id);
CREATE TABLE IF NOT EXISTS orders(
  id TEXT PRIMARY KEY, token TEXT NOT NULL, contact TEXT NOT NULL, total INTEGER NOT NULL,
  status TEXT NOT NULL, slip TEXT, created TEXT NOT NULL, expires TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS order_items(
  order_id TEXT NOT NULL, product_id INTEGER NOT NULL, price INTEGER NOT NULL);
CREATE INDEX IF NOT EXISTS ix_items ON order_items(order_id);
CREATE INDEX IF NOT EXISTS ix_items_p ON order_items(product_id);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT NOT NULL DEFAULT '');
"""


# ---------- database ----------
def tone_of(cat):
    """เลือกสีปกจากข้อความหมวด คำที่รู้จักได้สีประจำภาษา คำอื่นได้สีคงที่ตามตัวอักษร"""
    k = re.sub(r"\s+", "", cat.lower())
    for tone, names in TONE_ALIASES.items():
        if k in names:
            return tone
    return "h%d" % (zlib.crc32(k.encode("utf-8")) % 6)


def now():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")


def db():
    if "db" not in g:
        c = sqlite3.connect(DB_PATH, timeout=10, isolation_level=None)
        c.row_factory = sqlite3.Row
        c.execute("PRAGMA journal_mode=WAL")
        g.db = c
    return g.db


@app.teardown_appcontext
def close_db(_):
    c = g.pop("db", None)
    if c:
        c.close()


def init_db():
    c = sqlite3.connect(DB_PATH)
    c.executescript(SCHEMA)
    for old, new in LEGACY_CATS.items():
        c.execute("UPDATE products SET cat=? WHERE cat=?", (new, old))
    c.commit()
    c.close()


@contextmanager
def tx():
    d = db()
    d.execute("BEGIN IMMEDIATE")
    try:
        yield d
        d.execute("COMMIT")
    except BaseException:
        d.execute("ROLLBACK")
        raise


def get_pay(d=None):
    """ตั้งค่าช่องทางรับเงิน: bank, acc_no, acc_name, note, qr_file"""
    return {r["key"]: r["value"] for r in (d or db()).execute("SELECT key, value FROM settings")}


def set_setting(d, k, v):
    d.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (k, v))


def qr_name(pay):
    n = pay.get("qr_file", "")
    return n if n and os.path.isfile(os.path.join(QR_DIR, n)) else ""


def expire_orders():
    db().execute("UPDATE orders SET status='expired' WHERE status='pending' AND expires<?", (now(),))


# ---------- PromptPay ----------
def _crc16(s):
    crc = 0xFFFF
    for b in s.encode():
        crc ^= b << 8
        for _ in range(8):
            crc = ((crc << 1) ^ 0x1021) & 0xFFFF if crc & 0x8000 else (crc << 1) & 0xFFFF
    return f"{crc:04X}"


def _tlv(t, v):
    return f"{t}{len(v):02d}{v}"


def promptpay_payload(pid, amount):
    """ข้อความ QR พร้อมเพย์: เบอร์โทร 10 หลัก, เลขบัตร ปชช. 13 หลัก หรือ e-Wallet ID 15 หลัก (เช่น TrueMoney Wallet)"""
    if len(pid) == 10 and pid.startswith("0"):
        acc = _tlv("01", "0066" + pid[1:])
    elif len(pid) == 13:
        acc = _tlv("02", pid)
    elif len(pid) == 15:
        acc = _tlv("03", pid)
    else:
        return ""
    body = (_tlv("00", "01") + _tlv("01", "12")
            + _tlv("29", _tlv("00", "A000000677010111") + acc)
            + _tlv("53", "764") + _tlv("54", f"{amount:.2f}") + _tlv("58", "TH") + "6304")
    return body + _crc16(body)


# ---------- helpers ----------
@app.context_processor
def inject():
    if "csrf" not in session:
        session["csrf"] = secrets.token_hex(16)
    return dict(shop=SHOP_NAME, csrf=session["csrf"], status_th=STATUS_TH)


def brand():
    """ชื่อร้านแบบ HTML ปลอดภัย ตัว x ตรงกลางจะถูกไฮไลต์"""
    return Markup(re.sub(r"(?i)\s+x\s+", " <b>x</b> ", str(escape(SHOP_NAME))))


app.jinja_env.globals["brand"] = brand


@app.template_filter("fsize")
def fsize(n):
    n = float(n)
    for u in ("B", "KB", "MB", "GB"):
        if n < 1024 or u == "GB":
            return f"{n:.0f} {u}" if u == "B" else f"{n:.1f} {u}"
        n /= 1024


@app.after_request
def headers(r):
    r.headers["X-Content-Type-Options"] = "nosniff"
    r.headers["Referrer-Policy"] = "no-referrer"  # token อยู่ใน URL ห้ามหลุดไปเว็บอื่น
    if request.path.startswith(("/order", "/admin", "/api", "/pay")):
        r.headers["Cache-Control"] = "no-store"
    return r


_hits = {}


def client_ip():
    """IP ลูกค้าจริง (หลัง proxy ทุกคนจะมาจาก 127.0.0.1 ต้องอ่านจาก header ไม่งั้นตัวจำกัดจำนวนครั้งจะนับรวมทุกคน)"""
    if BEHIND_PROXY:
        ip = request.headers.get("CF-Connecting-IP") or request.headers.get("X-Forwarded-For", "").split(",")[0].strip()
        if ip:
            return ip[:64]
    return request.remote_addr or "?"


def too_many(key, limit, window):
    t = time.time()
    h = [x for x in _hits.get(key, []) if t - x < window]
    h.append(t)
    _hits[key] = h
    return len(h) > limit


def clean_name(n):
    n = os.path.basename((n or "").replace("\\", "/"))
    n = re.sub(r'[\x00-\x1f<>:"|?*]', "_", n).strip(" .")
    return n[:150] or "file"


def used_count(d, pid):
    return d.execute("SELECT COUNT(*) FROM order_items i JOIN orders o ON o.id=i.order_id "
                     "WHERE i.product_id=? AND o.status IN ('pending','verifying','paid')", (pid,)).fetchone()[0]


def product_dict(d, r):
    files = d.execute("SELECT name, size FROM files WHERE product_id=? ORDER BY id", (r["id"],)).fetchall()
    sold = d.execute("SELECT COUNT(*) FROM order_items i JOIN orders o ON o.id=i.order_id "
                     "WHERE i.product_id=? AND o.status='paid'", (r["id"],)).fetchone()[0]
    left = None if r["stock"] is None else max(0, r["stock"] - used_count(d, r["id"]))
    return dict(id=r["id"], cat=r["cat"], tone=tone_of(r["cat"]), name=r["name"], tag=r["tag"], desc=r["description"],
                preview=r["preview"], price=r["price"], was=r["was"], left=left, sold=sold,
                files=[[f["name"], f["size"]] for f in files])


def save_upload(d, pid, f):
    name = clean_name(f.filename)
    if not f.filename:
        return False
    stored = secrets.token_hex(16)
    path = os.path.join(FILES_DIR, stored)
    f.save(path)
    d.execute("INSERT INTO files(product_id,stored,name,size,created) VALUES(?,?,?,?,?)",
              (pid, stored, name, os.path.getsize(path), now()))
    return True


def send_stored(f):
    path = os.path.join(FILES_DIR, f["stored"])
    if not os.path.isfile(path):
        abort(404)
    return send_file(path, as_attachment=True, download_name=f["name"], mimetype="application/octet-stream")


# ---------- public ----------
@app.get("/")
def home():
    with open(os.path.join(BASE, "static", "index.html"), encoding="utf-8") as f:
        html = f.read()
    html = html.replace("{{SHOP_TITLE}}", str(escape(SHOP_NAME))).replace("{{SHOP_BRAND}}", str(brand()))
    return Response(html, mimetype="text/html")


@app.get("/api/products")
def api_products():
    expire_orders()
    d = db()
    rows = d.execute("SELECT * FROM products WHERE active=1 AND EXISTS("
                     "SELECT 1 FROM files WHERE product_id=products.id) ORDER BY id DESC").fetchall()
    return jsonify([product_dict(d, r) for r in rows])


@app.post("/api/orders")
def api_create_order():
    if too_many("order:" + client_ip(), 10, 600):
        return jsonify(error="สั่งซื้อถี่เกินไป รอสักครู่แล้วลองใหม่"), 429
    data = request.get_json(silent=True) or {}
    contact = str(data.get("contact", "")).strip()
    if not 3 <= len(contact) <= 100:
        return jsonify(error="กรอก LINE ID หรืออีเมลหรือเบอร์โทรสำหรับติดต่อ"), 400
    try:
        pids = list(dict.fromkeys(int(x) for x in (data.get("items") or [])[:20]))
    except (TypeError, ValueError):
        return jsonify(error="ข้อมูลตะกร้าไม่ถูกต้อง"), 400
    if not pids:
        return jsonify(error="ตะกร้าว่าง"), 400
    expire_orders()
    oid, token = secrets.token_hex(4).upper(), secrets.token_hex(16)
    try:
        with tx() as d:
            total, rows = 0, []
            for pid in pids:
                p = d.execute("SELECT * FROM products WHERE id=? AND active=1 AND EXISTS("
                              "SELECT 1 FROM files WHERE product_id=products.id)", (pid,)).fetchone()
                if not p:
                    raise ValueError("มีสินค้าที่ไม่พร้อมขายแล้ว")
                if p["stock"] is not None and used_count(d, pid) >= p["stock"]:
                    raise ValueError(f"\"{p['name']}\" หมดแล้ว")
                total += p["price"]
                rows.append((oid, pid, p["price"]))
            exp = (datetime.now(timezone.utc) + timedelta(minutes=HOLD_MIN)).strftime("%Y-%m-%dT%H:%M:%S")
            d.execute("INSERT INTO orders(id,token,contact,total,status,created,expires) VALUES(?,?,?,?,?,?,?)",
                      (oid, token, contact, total, "pending", now(), exp))
            d.executemany("INSERT INTO order_items VALUES(?,?,?)", rows)
    except ValueError as e:
        return jsonify(error=str(e)), 409
    return jsonify(url=f"/order/{oid}?t={token}"), 201


def load_order(oid):
    o = db().execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
    if not o or not safe_eq(request.values.get("t", ""), o["token"]):
        abort(404)
    return o


@app.get("/order/<oid>")
def order_page(oid):
    expire_orders()
    o = load_order(oid)
    d = db()
    items = d.execute("SELECT p.id, p.name, i.price FROM order_items i JOIN products p ON p.id=i.product_id "
                      "WHERE i.order_id=? ORDER BY p.id", (oid,)).fetchall()
    files = {}
    if o["status"] == "paid":
        for it in items:
            files[it["id"]] = d.execute("SELECT id, name, size FROM files WHERE product_id=? ORDER BY id",
                                        (it["id"],)).fetchall()
    pay = get_pay(d)
    qr = qr_name(pay)
    # ถ้าแอดมินอัปโหลด QR ไว้ใช้รูปนั้น ถ้าไม่มีและตั้ง PROMPTPAY_ID ไว้ค่อยสร้าง QR ให้เป็นตัวสำรอง
    payload = promptpay_payload(PROMPTPAY_ID, o["total"]) if o["status"] in ("pending", "verifying") and not qr else ""
    return render_template("order.html", o=o, items=items, files=files, payload=payload, pay=pay, qr=qr)


@app.get("/pay/qr")
def pay_qr():
    n = qr_name(get_pay())
    if not n:
        abort(404)
    mime = {"jpg": "image/jpeg", "png": "image/png", "webp": "image/webp"}[n.rsplit(".", 1)[-1]]
    return send_from_directory(QR_DIR, n, mimetype=mime)


@app.get("/order/<oid>/status")
def order_status(oid):
    expire_orders()
    return jsonify(status=load_order(oid)["status"])


@app.get("/order/<oid>/file/<int:fid>")
def order_file(oid, fid):
    o = load_order(oid)
    if o["status"] != "paid":
        abort(403)
    f = db().execute("SELECT f.* FROM files f JOIN order_items i ON i.product_id=f.product_id "
                     "WHERE i.order_id=? AND f.id=?", (oid, fid)).fetchone()
    if not f:
        abort(404)
    return send_stored(f)


@app.get("/order/<oid>/zip")
def order_zip(oid):
    o = load_order(oid)
    if o["status"] != "paid":
        abort(403)
    d = db()
    tmp = tempfile.TemporaryFile()
    used = set()
    with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as z:
        for it in d.execute("SELECT p.id, p.name FROM order_items i JOIN products p ON p.id=i.product_id "
                            "WHERE i.order_id=? ORDER BY p.id", (oid,)).fetchall():
            folder = clean_name(it["name"])
            for f in d.execute("SELECT * FROM files WHERE product_id=? ORDER BY id", (it["id"],)).fetchall():
                path = os.path.join(FILES_DIR, f["stored"])
                if not os.path.isfile(path):
                    continue
                arc, n = f"{folder}/{f['name']}", 1
                while arc in used:
                    n += 1
                    arc = f"{folder}/({n}) {f['name']}"
                used.add(arc)
                z.write(path, arc)
    tmp.seek(0)
    return send_file(tmp, as_attachment=True, download_name=f"order-{oid}.zip", mimetype="application/zip")


def _image_ext(head):
    if head.startswith(b"\xff\xd8\xff"):
        return "jpg"
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return "png"
    if head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return "webp"
    return None


@app.post("/order/<oid>/slip")
def upload_slip(oid):
    request.max_content_length = SLIP_MAX  # สลิปจำกัด 6MB (ไฟล์สินค้าของแอดมินใช้เพดานใหญ่กว่า)
    expire_orders()
    o = load_order(oid)
    back = redirect(f"/order/{oid}?t={o['token']}")
    if o["status"] not in ("pending", "verifying"):
        flash("ออเดอร์นี้ไม่รับสลิปแล้ว ถ้าโอนเงินไปแล้วให้ติดต่อแอดมิน")
        return back
    f = request.files.get("slip")
    blob = f.read() if f else b""
    ext = _image_ext(blob[:16])
    if not ext:
        flash("ไฟล์ต้องเป็นรูป JPG, PNG หรือ WEBP ไม่เกิน 6MB")
        return back
    name = f"{oid}-{secrets.token_hex(6)}.{ext}"
    with open(os.path.join(SLIPS_DIR, name), "wb") as out:
        out.write(blob)
    if o["slip"]:
        try:
            os.remove(os.path.join(SLIPS_DIR, o["slip"]))
        except OSError:
            pass
    db().execute("UPDATE orders SET slip=?, status='verifying' WHERE id=?", (name, oid))
    flash("ส่งสลิปแล้ว รอแอดมินตรวจสอบ หน้านี้จะอัปเดตเองเมื่ออนุมัติ")
    return back


@app.errorhandler(413)
def too_big(_):
    flash("ไฟล์ใหญ่เกินกำหนด")
    return redirect(request.referrer or "/"), 303


# ---------- admin ----------
def admin_required(f):
    @wraps(f)
    def w(*a, **k):
        if not session.get("admin"):
            return redirect(url_for("admin_login"))
        if request.method == "POST" and not safe_eq(request.form.get("csrf", ""), session.get("csrf", "")):
            abort(400)
        return f(*a, **k)
    return w


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        if not ADMIN_PASSWORD:
            flash("ยังไม่ได้ตั้ง ADMIN_PASSWORD ในเซิร์ฟเวอร์")
        elif too_many("login:" + client_ip(), 5, 600):
            flash("ลองรหัสผิดหลายครั้ง รอ 10 นาทีแล้วลองใหม่")
        elif safe_eq(request.form.get("password", ""), ADMIN_PASSWORD):
            session.clear()
            session["admin"] = True
            return redirect(url_for("admin"))
        else:
            flash("รหัสผ่านไม่ถูกต้อง")
    return render_template("admin_login.html")


@app.post("/admin/logout")
@admin_required
def admin_logout():
    session.clear()
    return redirect(url_for("admin_login"))


@app.get("/admin")
@admin_required
def admin():
    expire_orders()
    d = db()
    st = request.args.get("status", "")
    q = "SELECT * FROM orders" + (" WHERE status=?" if st in STATUS_TH else "") + " ORDER BY created DESC LIMIT 100"
    orders = []
    for o in d.execute(q, (st,) if st in STATUS_TH else ()).fetchall():
        its = d.execute("SELECT p.name FROM order_items i JOIN products p ON p.id=i.product_id WHERE i.order_id=?",
                        (o["id"],)).fetchall()
        orders.append((o, ", ".join(i["name"] for i in its)))
    products = []
    for p in d.execute("SELECT * FROM products ORDER BY id DESC").fetchall():
        files = d.execute("SELECT id, name, size FROM files WHERE product_id=? ORDER BY id", (p["id"],)).fetchall()
        sold = d.execute("SELECT COUNT(*) FROM order_items i JOIN orders o ON o.id=i.order_id "
                         "WHERE i.product_id=? AND o.status='paid'", (p["id"],)).fetchone()[0]
        products.append((p, files, sold))
    counts = {r["status"]: r["n"] for r in d.execute("SELECT status, COUNT(*) n FROM orders GROUP BY status")}
    revenue = d.execute("SELECT COALESCE(SUM(total),0) t FROM orders WHERE status='paid'").fetchone()["t"]
    return render_template("admin.html", orders=orders, products=products, counts=counts,
                           revenue=revenue, cur=st, pay=get_pay(d), qr=qr_name(get_pay(d)), cat_suggest=list(dict.fromkeys(SUGGEST_CATS + [p["cat"] for p, _, _ in products])),
                           blank=dict(id="", name="", tag="", description="", preview="",
                                      price="", was=None, stock=None, cat="", active=1))


@app.post("/admin/order/<oid>/<action>")
@admin_required
def admin_order(oid, action):
    with tx() as d:
        o = d.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
        if not o or action not in ("approve", "cancel"):
            abort(404)
        if o["status"] not in ("pending", "verifying"):
            flash(f"ออเดอร์ {oid} สถานะ \"{STATUS_TH[o['status']]}\" แล้ว แก้ไขไม่ได้")
        elif action == "approve":
            d.execute("UPDATE orders SET status='paid' WHERE id=?", (oid,))
            flash(f"อนุมัติออเดอร์ {oid} แล้ว ลูกค้าโหลดไฟล์ได้จากหน้าออเดอร์")
        else:
            d.execute("UPDATE orders SET status='cancelled' WHERE id=?", (oid,))
            flash(f"ยกเลิกออเดอร์ {oid} แล้ว")
    return redirect(request.referrer or url_for("admin"))


@app.post("/admin/payment")
@admin_required
def admin_payment():
    f = request.form
    up = request.files.get("qr")
    err = None
    with tx() as d:
        cur = get_pay(d)
        old = cur.get("qr_file", "")
        if up and up.filename:
            blob = up.read(SLIP_MAX + 1)
            ext = _image_ext(blob[:16])
            if not ext or len(blob) > SLIP_MAX:
                err = "ไฟล์ QR ต้องเป็นรูป JPG, PNG หรือ WEBP ไม่เกิน 6MB (ไม่ได้เปลี่ยนรูป QR)"
            else:
                name = f"qr-{secrets.token_hex(8)}.{ext}"
                with open(os.path.join(QR_DIR, name), "wb") as out:
                    out.write(blob)
                set_setting(d, "qr_file", name)
                if old:
                    try:
                        os.remove(os.path.join(QR_DIR, old))
                    except OSError:
                        pass
        elif f.get("remove_qr") and old:
            set_setting(d, "qr_file", "")
            try:
                os.remove(os.path.join(QR_DIR, old))
            except OSError:
                pass
        for k, mx in (("bank", 60), ("acc_no", 40), ("acc_name", 80), ("note", 400)):
            set_setting(d, k, f.get(k, "").strip()[:mx])
    flash(err or "บันทึกช่องทางรับเงินแล้ว")
    return redirect(url_for("admin") + "#payment")


@app.get("/admin/slip/<oid>")
@admin_required
def admin_slip(oid):
    o = db().execute("SELECT slip FROM orders WHERE id=?", (oid,)).fetchone()
    if not o or not o["slip"]:
        abort(404)
    return send_from_directory(SLIPS_DIR, o["slip"])


@app.get("/admin/file/<int:fid>")
@admin_required
def admin_file(fid):
    f = db().execute("SELECT * FROM files WHERE id=?", (fid,)).fetchone()
    if not f:
        abort(404)
    return send_stored(f)


def _int(v, default=None):
    try:
        return int(str(v).strip())
    except ValueError:
        return default


@app.post("/admin/product")
@admin_required
def admin_product():
    f = request.form
    name, price = f.get("name", "").strip(), _int(f.get("price"))
    if not name or not price or price < 1:
        flash("ต้องมีชื่อสินค้าและราคามากกว่า 0")
        return redirect(url_for("admin") + "#products")
    vals = ((f.get("cat", "").strip()[:20] or "CODE"), name, f.get("tag", "").strip()[:30],
            f.get("description", "").strip(), f.get("preview", "").strip()[:3000],
            price, _int(f.get("was")) or None, _int(f.get("stock")), 1 if f.get("active") else 0)
    pid = _int(f.get("id"))
    added = 0
    with tx() as d:
        if pid and d.execute("SELECT 1 FROM products WHERE id=?", (pid,)).fetchone():
            d.execute("UPDATE products SET cat=?,name=?,tag=?,description=?,preview=?,price=?,was=?,stock=?,active=? "
                      "WHERE id=?", vals + (pid,))
        else:
            pid = d.execute("INSERT INTO products(cat,name,tag,description,preview,price,was,stock,active) "
                            "VALUES(?,?,?,?,?,?,?,?,?)", vals).lastrowid
        for up in request.files.getlist("files"):
            added += 1 if save_upload(d, pid, up) else 0
    flash(f"บันทึกสินค้าแล้ว" + (f" เพิ่มไฟล์ {added} ไฟล์" if added else ""))
    return redirect(url_for("admin") + "#products")


@app.post("/admin/file/<int:fid>/delete")
@admin_required
def admin_file_delete(fid):
    with tx() as d:
        f = d.execute("SELECT * FROM files WHERE id=?", (fid,)).fetchone()
        if f:
            d.execute("DELETE FROM files WHERE id=?", (fid,))
            try:
                os.remove(os.path.join(FILES_DIR, f["stored"]))
            except OSError:
                pass
            flash(f"ลบไฟล์ {f['name']} แล้ว (ลูกค้าที่จ่ายแล้วจะไม่เห็นไฟล์นี้อีก)")
    return redirect(url_for("admin") + "#products")


# ---------- seed / run ----------
SAMPLES = [
    ("JS", "Debounce + Throttle Utils", "ยอดนิยม", 29, None,
     "ฟังก์ชันที่ใช้บ่อยสุด กันช่องค้นหายิง API รัวๆ พร้อมตัวอย่างใช้งาน",
     "function debounce(fn, ms = 300) {\n  let t;\n  return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); };\n}",
     [("utils.js", "export function debounce(fn, ms = 300) {\n  let t;\n  return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); };\n}\n\nexport function throttle(fn, ms = 300) {\n  let last = 0;\n  return (...a) => { const n = Date.now(); if (n - last >= ms) { last = n; fn(...a); } };\n}\n"),
      ("README.md", "# Debounce + Throttle\n\nimport { debounce } from './utils.js'\n")]),
    ("CSS", "Neon Button Pack", "ใหม่", 19, 39,
     "ปุ่ม 6 สไตล์ ใช้ CSS ล้วน ไม่ต้องมี JS",
     ".btn-neon {\n  border: 2px solid #ff4d3d;\n  box-shadow: 0 0 12px #ff4d3d88;\n}",
     [("buttons.css", ".btn-neon{padding:10px 22px;border:2px solid #ff4d3d;border-radius:10px;color:#fff;background:#0000;box-shadow:0 0 12px #ff4d3d88}\n.btn-neon:hover{background:#ff4d3d}\n"),
      ("demo.html", "<!doctype html><link rel=stylesheet href=buttons.css><button class=btn-neon>Click</button>\n")]),
    ("PYTHON", "Bulk File Renamer", "", 49, None,
     "เปลี่ยนชื่อไฟล์ทั้งโฟลเดอร์เป็นลำดับเลข ใส่คำนำหน้าได้ รันได้ทันทีด้วย Python 3",
     "def rename_all(folder, prefix='img'):\n    files = sorted(p for p in Path(folder).iterdir() if p.is_file())",
     [("rename_files.py", "from pathlib import Path\nimport sys\n\ndef rename_all(folder, prefix='img'):\n    files = sorted(p for p in Path(folder).iterdir() if p.is_file())\n    for i, p in enumerate(files, 1):\n        p.rename(p.with_name(f'{prefix}_{i:03d}{p.suffix}'))\n\nif __name__ == '__main__':\n    rename_all(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else 'img')\n"),
      ("config.json", '{"prefix": "img", "pad": 3}\n')]),
    ("C++", "Fast Input Template (C++)", "สายแข่งโค้ด", 39, None,
     "เทมเพลต C++ สำหรับแข่งโปรแกรมมิ่ง อ่านข้อมูลเร็ว พร้อมแมโครที่ใช้บ่อย",
     "ios::sync_with_stdio(false);\ncin.tie(nullptr);",
     [("template.cpp", "#include <bits/stdc++.h>\nusing namespace std;\n\nint main() {\n    ios::sync_with_stdio(false);\n    cin.tie(nullptr);\n    int n; cin >> n;\n    cout << n << \"\\n\";\n}\n")]),
]


def seed():
    init_db()
    c = sqlite3.connect(DB_PATH)
    if c.execute("SELECT COUNT(*) FROM products").fetchone()[0]:
        print("มีสินค้าอยู่แล้ว ข้ามการ seed")
        return
    for cat, name, tag, price, was, desc, prev, files in SAMPLES:
        pid = c.execute("INSERT INTO products(cat,name,tag,description,preview,price,was) VALUES(?,?,?,?,?,?,?)",
                        (cat, name, tag, desc, prev, price, was)).lastrowid
        for fname, content in files:
            stored = secrets.token_hex(16)
            with open(os.path.join(FILES_DIR, stored), "w", encoding="utf-8") as fh:
                fh.write(content)
            c.execute("INSERT INTO files(product_id,stored,name,size,created) VALUES(?,?,?,?,?)",
                      (pid, stored, fname, len(content.encode()), now()))
    c.commit()
    c.close()
    print("เพิ่มสินค้าตัวอย่าง 4 ชิ้นพร้อมไฟล์แล้ว ลบหรือซ่อนได้ในหลังบ้าน")


init_db()

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "seed":
        seed()
    else:
        if not ADMIN_PASSWORD:
            print("คำเตือน: ยังไม่ได้ตั้ง ADMIN_PASSWORD จะเข้าหลังบ้านไม่ได้")
        app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "5000")), debug=False)
