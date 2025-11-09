import os
import sys
import time
import json
import socket
import struct
import threading
from functools import wraps
from datetime import datetime
from ipaddress import IPv4Address
from collections import deque

# Flask 框架與安全庫
from flask import Flask, render_template_string, request, session, redirect, url_for, flash, jsonify
from flask_bcrypt import Bcrypt

# ====================================================================
# I. 配置與全域變數
# ====================================================================

# --- 服務配置 ---
# Flask Web 服務配置
FLASK_HOST = os.environ.get('FLASK_HOST', '0.0.0.0')
FLASK_PORT = int(os.environ.get('FLASK_PORT', 443))
FLASK_SECRET_KEY = os.environ.get('FLASK_SECRET_KEY', 'default_secret_key_please_change_this')
# SSL 憑證路徑 (需要在運行目錄下準備 cert.pem 和 key.pem)
CERT_FILE = os.environ.get('CERT_FILE', 'cert.pem')
KEY_FILE = os.environ.get('KEY_FILE', 'key.pem')

# DNS 服務配置
DNS_HOST = os.environ.get('DNS_HOST', '0.0.0.0')
DNS_PORT = int(os.environ.get('DNS_PORT', 53))
# 初始預設值和環境變數獲取
UPSTREAM_DNS_DEFAULT = '1.1.1.1'
UPSTREAM_DNS = os.environ.get('UPSTREAM_DNS', UPSTREAM_DNS_DEFAULT)
DNS_TIMEOUT = float(os.environ.get('DNS_TIMEOUT', 3.0))

# 持久化檔案路徑
REWRITE_FILE = 'rewrite_domains.json'
CREDENTIALS_FILE = 'web_credentials.json'
UPSTREAM_FILE = 'upstream_dns.json'  # 獨立的上游 DNS 配置文件

BLOCK_TARGET_IP_DEFAULT = '0.0.0.0'

# --- 運行時變數 ---
domains_lock = threading.Lock()
stats_lock = threading.Lock()
credentials_lock = threading.Lock()
cache_lock = threading.Lock()
upstream_lock = threading.Lock()

REWRITE_MAP = {}
BLOCK_TARGET_IP = BLOCK_TARGET_IP_DEFAULT

# DNS 快取
DNS_CACHE = {}
MAX_CACHE_SIZE = 10000
CACHE_DEFAULT_TTL = 300  # 預設 TTL（秒）

# 服務狀態與統計
SERVICE_STATUS = {
    "dns_status": "PENDING",
    "dns_error": None,
    "flask_status": "PENDING",
    "flask_error": None,
    "rewrites_loaded": 0
}

TRAFFIC_STATS = {
    "start_time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    "total_queries": 0,
    "forward_count": 0,
    "hijack_count": 0,
    "block_count": 0,
    "error_count": 0,
    "cache_hit_count": 0,
    "cache_miss_count": 0,
}

# 日誌配置
LOG_LEVELS = {'DEBUG', 'INFO', 'WARNING', 'ERROR', 'FATAL', 'REWRITE', 'FORWARD', 'BLOCK', 'CACHE'}
MAX_LOGS = 100
log_queue = deque(maxlen=MAX_LOGS)

# Web 憑證
WEB_USERNAME = os.environ.get('WEB_USERNAME', 'admin')
WEB_PASSWORD_HASH = os.environ.get('WEB_PASSWORD_HASH', None)

# --- Flask 實例化與 Bcrypt 初始化 ---
app = Flask(__name__)
app.secret_key = FLASK_SECRET_KEY
bcrypt = Bcrypt(app)


# ====================================================================
# II. 輔助函數 (日誌、檔案操作、DNS 協議)
# ====================================================================

def log_message(message, level='INFO'):
    """
    將日誌消息安全地放入 deque 循環緩衝區，並寫入控制台。
    使用 append() 確保新的日誌在列表的末尾。
    """
    if level not in LOG_LEVELS:
        level = 'INFO'

    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    full_message = f"[{timestamp}][{level.upper()}] {message}"
    print(full_message, file=sys.stderr)

    log_queue.append({'message': full_message, 'level': level.upper()})


def is_valid_ip(ip_str, allow_reserved=False):
    """檢查字串是否為有效的 IPv4 地址。"""
    try:
        ip = IPv4Address(ip_str)
        if allow_reserved:
            return True
        return not (ip.is_private or ip.is_reserved or ip.is_loopback or ip.is_multicast)
    except:
        return False


def format_domain_for_map(domain):
    """格式化域名為小寫，並確保以點結束，用於內部 Map Key。"""
    if not domain: return ""
    domain = domain.lower().strip()
    if not domain.endswith('.'): domain += '.'
    return domain


# --- 管理員憑證持久化邏輯 ---
def save_credentials(username, password_hash):
    """儲存 Web 介面登入憑證到檔案。"""
    global WEB_USERNAME
    global WEB_PASSWORD_HASH
    if not username or not password_hash:
        log_message("[Web] 嘗試儲存空憑證，操作被阻止。", level='ERROR')
        return False
    data_to_save = {
        "username": username,
        "password_hash": password_hash.decode('utf-8') if isinstance(password_hash, bytes) else password_hash
    }
    try:
        with credentials_lock:
            with open(CREDENTIALS_FILE, 'w') as f:
                json.dump(data_to_save, f, indent=4)
            WEB_USERNAME = username
            WEB_PASSWORD_HASH = data_to_save["password_hash"]
        log_message(f"[Web] Web 管理憑證已更新並永久儲存到 {CREDENTIALS_FILE}。", level='WARNING')
        return True
    except Exception as e:
        log_message(f"[Web] 儲存 Web 憑證失敗: {e}", level='ERROR')
        return False


def load_credentials():
    """從檔案載入 Web 介面登入憑證或生成預設憑證。"""
    global WEB_USERNAME
    global WEB_PASSWORD_HASH
    if os.path.exists(CREDENTIALS_FILE):
        try:
            with open(CREDENTIALS_FILE, 'r') as f:
                data = json.load(f)
            with credentials_lock:
                WEB_USERNAME = data.get("username", WEB_USERNAME)
                WEB_PASSWORD_HASH = data.get("password_hash", WEB_PASSWORD_HASH)
            log_message(f"[Web] 成功從檔案載入 Web 憑證，用戶名: {WEB_USERNAME}", level='INFO')
        except json.JSONDecodeError:
            log_message(f"[Web] 憑證檔案 {CREDENTIALS_FILE} 格式錯誤。", level='FATAL')
        except Exception as e:
            log_message(f"[Web] 載入憑證時發生錯誤: {e}", level='FATAL')

    # 如果未設定雜湊密碼，則設定預設密碼
    if not WEB_PASSWORD_HASH:
        default_password = 'admin123'
        hashed_default_password = bcrypt.generate_password_hash(default_password).decode('utf-8')
        if save_credentials(WEB_USERNAME, hashed_default_password):
            log_message(f"[Web] ⚠️ 警告: 正在使用預設密碼 ('{default_password}')。請儘快透過 Web 介面修改。",
                        level='WARNING')
        else:
            log_message(f"[Web] ❌ 錯誤: 無法儲存預設憑證。", level='FATAL')
    if isinstance(WEB_PASSWORD_HASH, bytes):
        WEB_PASSWORD_HASH = WEB_PASSWORD_HASH.decode('utf-8')


# --- 重寫規則持久化邏輯 ---
def save_rewrite_domains(new_map, new_block_target_ip=None):
    """儲存重寫規則和全局 BLOCK IP 到檔案。"""
    global REWRITE_MAP
    global BLOCK_TARGET_IP
    data_to_save = {
        "block_target_ip": new_block_target_ip if new_block_target_ip is not None else BLOCK_TARGET_IP,
        "domains": {}
    }
    for domain, entry in new_map.items():
        entry_type = entry['type']
        ip_to_save = None if entry_type == 'BLOCK' else entry['ip']
        data_to_save["domains"][domain] = {"type": entry_type, "ip": ip_to_save}
    try:
        with domains_lock:
            with open(REWRITE_FILE, 'w') as f:
                json.dump(data_to_save, f, indent=4)
            REWRITE_MAP = new_map
            if new_block_target_ip is not None:
                BLOCK_TARGET_IP = new_block_target_ip
            SERVICE_STATUS["rewrites_loaded"] = len(REWRITE_MAP)
        log_message(f"[Config] 成功儲存 {len(REWRITE_MAP)} 條重寫規則。全局 BLOCK IP: {BLOCK_TARGET_IP}", level='INFO')
        return True
    except Exception as e:
        log_message(f"[Config] 儲存重寫規則失敗: {e}", level='ERROR')
        return False


def load_rewrite_domains():
    """從檔案載入重寫規則和全局 BLOCK IP。"""
    global REWRITE_MAP
    global BLOCK_TARGET_IP
    if not os.path.exists(REWRITE_FILE):
        save_rewrite_domains({})
        return
    try:
        with open(REWRITE_FILE, 'r') as f:
            data = json.load(f)
        loaded_map = {}
        loaded_block_ip = data.get("block_target_ip", BLOCK_TARGET_IP_DEFAULT)
        if not is_valid_ip(loaded_block_ip, allow_reserved=True):
            loaded_block_ip = BLOCK_TARGET_IP_DEFAULT
        for domain, entry in data.get("domains", {}).items():
            entry_type = entry.get('type')
            ip = entry.get('ip')
            if entry_type == 'BLOCK':
                ip = loaded_block_ip
            if not ip or not is_valid_ip(ip, allow_reserved=True):
                if entry_type == 'HIJACK': continue
            domain_key = format_domain_for_map(domain)
            loaded_map[domain_key] = {'type': entry_type, 'ip': ip}
        with domains_lock:
            REWRITE_MAP = loaded_map
            BLOCK_TARGET_IP = loaded_block_ip
            SERVICE_STATUS["rewrites_loaded"] = len(REWRITE_MAP)
        log_message(f"[Config] 成功載入 {len(REWRITE_MAP)} 條重寫規則。", level='INFO')
    except Exception as e:
        log_message(f"[Config] 載入重寫規則時發生錯誤: {e}", level='FATAL')


# --- 上游 DNS 持久化邏輯 ---

def save_upstream_dns(new_upstream_ip):
    """儲存新的上游 DNS IP 到檔案。"""
    global UPSTREAM_DNS
    if not is_valid_ip(new_upstream_ip, allow_reserved=False):
        log_message(f"[Config] 嘗試儲存無效的上游 DNS IP: {new_upstream_ip}", level='ERROR')
        return False

    data_to_save = {"upstream_dns": new_upstream_ip}
    try:
        with upstream_lock:
            with open(UPSTREAM_FILE, 'w') as f:
                json.dump(data_to_save, f, indent=4)
            UPSTREAM_DNS = new_upstream_ip

        # 清除快取，確保新查詢使用新的上游 DNS
        clear_all_cache(log_message_flag=False)
        log_message(f"[Config] 🚀 上游 DNS IP 已更新並永久儲存為: {UPSTREAM_DNS}。快取已清除。", level='WARNING')
        return True
    except Exception as e:
        log_message(f"[Config] 儲存上游 DNS 失敗: {e}", level='ERROR')
        return False


def load_upstream_dns():
    """從檔案載入上游 DNS IP。"""
    global UPSTREAM_DNS
    if not os.path.exists(UPSTREAM_FILE):
        # 如果檔案不存在，使用環境變數或預設值並儲存
        save_upstream_dns(UPSTREAM_DNS)
        return
    try:
        with open(UPSTREAM_FILE, 'r') as f:
            data = json.load(f)
        loaded_ip = data.get("upstream_dns", UPSTREAM_DNS_DEFAULT)
        if not is_valid_ip(loaded_ip, allow_reserved=False):  # 不允許保留地址作為上游 DNS
            loaded_ip = UPSTREAM_DNS_DEFAULT
            log_message(f"[Config] 載入的上游 DNS IP 無效，使用預設值: {loaded_ip}", level='WARNING')

        with upstream_lock:
            UPSTREAM_DNS = loaded_ip
        log_message(f"[Config] 成功從檔案載入上游 DNS IP: {UPSTREAM_DNS}", level='INFO')
    except Exception as e:
        log_message(f"[Config] 載入上游 DNS 配置時發生錯誤: {e}。使用當前值: {UPSTREAM_DNS}", level='FATAL')


# --- DNS 封包解析與構造 ---
def decode_domain_name(data, offset):
    """從 DNS 封包中解析域名。"""
    domain = []
    start_offset = offset
    while True:
        length = data[offset]
        offset += 1
        if length == 0: break
        # 處理指針壓縮
        if (length & 0xC0) == 0xC0:
            pointer = ((length & 0x3F) << 8) | data[offset]
            offset += 1
            pointed_domain, _ = decode_domain_name(data, pointer)
            domain.append(pointed_domain.rstrip('.'))
            return ".".join(domain) + '.', start_offset + 2
        # 處理正常標籤
        if length > 63 or offset + length > len(data):
            log_message("[DNS] 域名解析錯誤：長度無效或越界。", level='ERROR')
            return "", len(data)
        label = data[offset:offset + length].decode('utf-8', errors='ignore')
        domain.append(label)
        offset += length
    return ".".join(domain) + '.', offset


def extract_info_from_query(data):
    """從 DNS 查詢封包中提取查詢 ID, 域名和 QType。"""
    try:
        query_id = struct.unpack('!H', data[:2])[0]
        query_count = struct.unpack('!H', data[4:6])[0]
        if query_count != 1:
            return None, None, None, "多查詢或無查詢"
        domain_name, offset = decode_domain_name(data, 12)
        qtype = struct.unpack('!H', data[offset:offset + 2])[0]
        return query_id, domain_name, qtype, None
    except Exception as e:
        return None, None, None, f"解析失敗: {e}"


def extract_ttl_from_response(response_data):
    """從上游 DNS 回應中提取 TTL，如果失敗則使用預設值。"""
    return CACHE_DEFAULT_TTL


def construct_response(query_data, domain, target_ip, rcode=0, ttl=60):
    """構造一個簡單的 A 記錄 DNS 響應。"""
    # 標頭 (設置為響應, AA=0, RA=1)
    header_bytes = bytearray(query_data[:2])
    header_bytes.append(query_data[2] | 0x80)  # 設置 QR=1
    header_bytes.append((query_data[3] & 0xF0) | rcode)
    header_bytes += query_data[4:6]  # QDCOUNT (1)

    # ANCOUNT (回答區段數量)
    header_bytes += struct.pack('!H', 1 if rcode == 0 and target_ip else 0)

    header_bytes += struct.pack('!HH', 0, 0)  # NSCOUNT, ARCOUNT
    response_data = header_bytes

    # 查詢區段 (QNAME, QTYPE, QCLASS)
    offset = 12
    while True:
        length = query_data[offset]
        offset += length + 1
        if (length & 0xC0) == 0xC0:
            offset += 1
            break
        if length == 0: break
    qname_end_offset = offset + 4
    response_data += query_data[12:qname_end_offset]

    # 回答區段 (Answer Section) - 僅在成功時添加
    if rcode == 0 and target_ip:
        # NAME (指針到 0x0C)
        response_data += b'\xc0\x0c'
        # TYPE=A (1), CLASS=IN (1)
        response_data += struct.pack('!HH', 1, 1)
        # TTL (秒)
        response_data += struct.pack('!I', ttl)
        # RDLENGTH (4 bytes for IPv4)
        response_data += struct.pack('!H', 4)
        # RDATA (IP 地址)
        response_data += socket.inet_aton(target_ip)
    return bytes(response_data)


# --- DNS 快取邏輯 ---
def get_cache_response(query_id, domain_name, qtype):
    """檢查快取，如果命中且未過期，返回響應。"""
    cache_key = (domain_name, qtype)
    with cache_lock:
        cache_entry = DNS_CACHE.get(cache_key)
        if cache_entry:
            if time.time() < cache_entry['expires']:
                log_message(f"[Cache] ✅ 命中快取: {domain_name}", level='CACHE')
                with stats_lock:
                    TRAFFIC_STATS["cache_hit_count"] += 1
                response = bytearray(cache_entry['response'])
                # 更新 ID 以匹配當前查詢
                response[:2] = struct.pack('!H', query_id)
                return bytes(response)
            else:
                del DNS_CACHE[cache_key]
                log_message(f"[Cache] ❌ 快取過期並移除: {domain_name}", level='CACHE')
        with stats_lock:
            TRAFFIC_STATS["cache_miss_count"] += 1
        return None


def set_cache_response(domain_name, qtype, response_data):
    """將上游 DNS 響應寫入快取。"""
    cache_key = (domain_name, qtype)
    ttl = extract_ttl_from_response(response_data)
    expires = time.time() + ttl
    with cache_lock:
        DNS_CACHE[cache_key] = {'response': response_data, 'expires': expires}
        # 實施 LRU 或簡單的容量限制清理
        if len(DNS_CACHE) > MAX_CACHE_SIZE:
            # 找到最舊的 (最早過期的) 條目移除
            oldest_key = min(DNS_CACHE, key=lambda k: DNS_CACHE[k]['expires'])
            del DNS_CACHE[oldest_key]
            log_message(f"[Cache] 超出限制，移除最舊條目: {oldest_key[0]}", level='WARNING')
    log_message(f"[Cache] 💾 寫入快取: {domain_name}, TTL: {ttl}s", level='CACHE')


def forward_query(query_data, domain_name, qtype):
    """將 DNS 查詢轉發給上游 DNS 服務器。"""
    # 使用最新的 UPSTREAM_DNS
    current_upstream = UPSTREAM_DNS
    try:
        upstream_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        upstream_sock.settimeout(DNS_TIMEOUT)
        upstream_sock.sendto(query_data, (current_upstream, 53))
        response, _ = upstream_sock.recvfrom(512)

        # 僅快取成功的 A 記錄查詢
        if qtype == 1:
            set_cache_response(domain_name, qtype, response)

        with stats_lock:
            TRAFFIC_STATS["forward_count"] += 1
        return response
    except socket.timeout:
        log_message(f"[DNS] 轉發超時至上游 DNS ({current_upstream})。", level='ERROR')
    except Exception as e:
        log_message(f"[DNS] 轉發查詢失敗: {e}", level='ERROR')
    with stats_lock:
        TRAFFIC_STATS["error_count"] += 1
    return None


# ====================================================================
# III. DNS 服務核心處理邏輯
# ====================================================================

def handle_query(data, addr):
    """處理單個 DNS 查詢。"""
    with stats_lock:
        TRAFFIC_STATS["total_queries"] += 1
    query_id, domain_name, qtype, error_msg = extract_info_from_query(data)

    if error_msg:
        log_message(f"[DNS] 查詢包解析失敗: {error_msg}", level='ERROR')
        with stats_lock: TRAFFIC_STATS["error_count"] += 1
        return None

    log_message(f"[DNS] 接收查詢: {domain_name} (Type={qtype}, from {addr[0]})", level='DEBUG')

    # 1. 檢查重寫規則
    with domains_lock:
        target_entry = REWRITE_MAP.get(domain_name, None)

    if target_entry:
        entry_type = target_entry['type']
        target_ip = target_entry['ip']

        # 只處理 A 記錄重寫，其他類型放行
        if qtype == 1:
            if entry_type == 'HIJACK':
                response = construct_response(data, domain_name, target_ip, rcode=0)
                log_message(f"[DNS] 💥 劫持命中: {domain_name} -> {target_ip}", level='REWRITE')
                with stats_lock:
                    TRAFFIC_STATS["hijack_count"] += 1
                return response
            elif entry_type == 'BLOCK':
                response = construct_response(data, domain_name, target_ip, rcode=0)
                log_message(f"[DNS] 🚫 禁止命中: {domain_name} -> {target_ip}", level='BLOCK')
                with stats_lock:
                    TRAFFIC_STATS["block_count"] += 1
                return response

    # 2. 檢查快取 (僅對 A 記錄檢查)
    if qtype == 1:
        cached_response = get_cache_response(query_id, domain_name, qtype)
        if cached_response:
            return cached_response

    # 3. 轉發查詢
    # 使用最新的 UPSTREAM_DNS 進行日誌記錄
    log_message(f"[DNS] ➡️ 轉發查詢: {domain_name} (Type={qtype}) -> {UPSTREAM_DNS}", level='FORWARD')
    return forward_query(data, domain_name, qtype)


def start_dns_server():
    """啟動 DNS 伺服器線程的主函數。"""
    load_rewrite_domains()
    load_upstream_dns()  # 載入上游 DNS IP
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind((DNS_HOST, DNS_PORT))
        SERVICE_STATUS["dns_status"] = "RUNNING"
        # 使用最新的 UPSTREAM_DNS 進行日誌記錄
        log_message(f"[DNS Thread] DNS Proxy 運行於 {DNS_HOST}:{DNS_PORT}，上游 DNS: {UPSTREAM_DNS}", level='INFO')

        while True:
            try:
                # 阻塞接收查詢
                data, addr = sock.recvfrom(512)
                # 為每個查詢啟動一個新線程，避免 I/O 阻塞主線程
                threading.Thread(target=_process_query_thread, args=(sock, data, addr)).start()
            except Exception as e:
                log_message(f"[DNS] 主循環錯誤: {e}", level='ERROR')
    except Exception as e:
        SERVICE_STATUS["dns_status"] = "FAILED"
        SERVICE_STATUS["dns_error"] = str(e)
        log_message(f"[DNS] ❌ 致命錯誤，無法啟動 DNS 服務: {e}", level='FATAL')
    finally:
        log_message("[DNS Thread] Service stopped.")


def _process_query_thread(sock, data, addr):
    """在單獨線程中處理查詢並發送響應。"""
    response = handle_query(data, addr)
    if response:
        try:
            sock.sendto(response, addr)
        except Exception as e:
            log_message(f"[DNS] 發送響應失敗: {e}", level='ERROR')


# ====================================================================
# IV. Flask Web 伺服器邏輯
# ====================================================================

# --- 認證裝飾器 ---
def requires_auth(f):
    """要求用戶登入才能訪問的裝飾器。"""

    @wraps(f)
    def decorated(*args, **kwargs):
        if 'logged_in' not in session:
            flash("請先登入才能訪問管理介面。", 'error')
            return redirect(url_for('login'))
        return f(*args, **kwargs)

    return decorated


# --- 輔助函數：獲取日誌列表與域名列表 ---
def get_log_entries():
    """獲取格式化的日誌列表。"""
    # log_queue 返回的是 [舊, ..., 新] 的列表
    return list(log_queue)


def get_domain_lists():
    """獲取當前的劫持和禁止域名列表。"""
    with domains_lock:
        current_map = REWRITE_MAP.copy()
        current_block_ip = BLOCK_TARGET_IP
    hijack_list = []
    block_list = []
    for domain_with_dot, data in current_map.items():
        domain = domain_with_dot.rstrip('.')
        entry_type = data.get('type')
        ip = data.get('ip')
        if entry_type == 'HIJACK':
            hijack_list.append({'domain': domain, 'ip': ip})
        elif entry_type == 'BLOCK':
            # Block 列表顯示全局 BLOCK IP
            display_ip = current_block_ip
            block_list.append({'domain': domain, 'ip': display_ip})
    return hijack_list, block_list, current_block_ip


def clear_cache_by_domain(domain):
    """根據域名清除快取。"""
    if not domain: return False
    domain_key = format_domain_for_map(domain)
    removed_count = 0
    with cache_lock:
        keys_to_remove = [k for k in DNS_CACHE if k[0] == domain_key]
        for key in keys_to_remove:
            del DNS_CACHE[key]
            removed_count += 1
    if removed_count > 0:
        log_message(f"因重寫規則變動，已清除 {domain} 的 {removed_count} 條快取。", level='CACHE')
    return True


def clear_all_cache(log_message_flag=True):
    """清除所有快取。"""
    global DNS_CACHE
    with cache_lock:
        count = len(DNS_CACHE)
        DNS_CACHE = {}
    if log_message_flag:
        log_message(f"已清除所有 {count} 條 DNS 快取。", level='CACHE')
    return True


# --- 路由定義 ---

@app.route('/login', methods=['GET', 'POST'])
def login():
    """登入頁面與邏輯。"""
    if request.method == 'POST':
        username = request.form['username']
        password = request.form['password']

        # 確保在比較前載入最新的憑證
        load_credentials()

        if username == WEB_USERNAME and WEB_PASSWORD_HASH and bcrypt.check_password_hash(WEB_PASSWORD_HASH, password):
            session['logged_in'] = True
            flash('登入成功!', 'success')
            return redirect(url_for('index'))
        else:
            flash('用戶名或密碼錯誤。', 'error')

    # 使用通用的 HTML 模板渲染登入頁面
    return render_template_string(HTML_TEMPLATE,
                                  is_log_page=False,
                                  is_login_page=True,
                                  SERVICE_STATUS=SERVICE_STATUS,
                                  WEB_USERNAME=WEB_USERNAME)


@app.route('/logout')
@requires_auth
def logout():
    """登出邏輯。"""
    session.pop('logged_in', None)
    flash('您已登出。', 'info')
    return redirect(url_for('login'))


@app.route('/')
@requires_auth
def index():
    """儀表板主頁面。"""
    # 確保獲取最新的上游 DNS 狀態
    load_upstream_dns()

    hijack_list, block_list, current_block_ip = get_domain_lists()

    # 為模板準備統計數據
    with stats_lock:
        stats = TRAFFIC_STATS.copy()

    with cache_lock:
        cache_size = len(DNS_CACHE)

    return render_template_string(HTML_TEMPLATE,
                                  is_log_page=False,
                                  is_login_page=False,
                                  SERVICE_STATUS=SERVICE_STATUS,
                                  TRAFFIC_STATS=stats,
                                  BLOCK_TARGET_IP=current_block_ip,
                                  hijack_list=hijack_list,
                                  block_list=block_list,
                                  DNS_CACHE_SIZE=cache_size,
                                  MAX_CACHE_SIZE=MAX_CACHE_SIZE,
                                  UPSTREAM_DNS=UPSTREAM_DNS,
                                  DNS_HOST=DNS_HOST,
                                  DNS_PORT=DNS_PORT,
                                  FLASK_HOST=FLASK_HOST,
                                  FLASK_PORT=FLASK_PORT,
                                  WEB_USERNAME=WEB_USERNAME,
                                  CREDENTIALS_FILE=CREDENTIALS_FILE,
                                  UPSTREAM_FILE=UPSTREAM_FILE
                                  )


@app.route('/update_upstream_dns', methods=['POST'])
@requires_auth
def update_upstream_dns():
    """更新上游 DNS 服務器 IP。"""
    new_ip = request.form.get('upstream_dns_ip', '').strip()
    if not is_valid_ip(new_ip, allow_reserved=False):
        flash(f"無效的上游 DNS IP 地址: {new_ip}。請輸入公共 IP。", 'error')
        return redirect(url_for('index'))

    if save_upstream_dns(new_ip):
        flash(f"上游 DNS 伺服器已成功更新為 {new_ip}，所有快取已清除。", 'success')
    else:
        flash("更新上游 DNS IP 失敗。", 'error')

    return redirect(url_for('index'))


@app.route('/logs')
@requires_auth
def logs():
    """日誌頁面，包含 AJAX 輪詢邏輯。"""
    return render_template_string(HTML_TEMPLATE,
                                  is_log_page=True,
                                  MAX_LOGS=MAX_LOGS
                                  )


@app.route('/api/logs', methods=['GET'])
@requires_auth
def get_latest_logs():
    """API 接口：獲取最新的日誌條目 (JSON 格式)。"""
    # get_log_entries() 返回的是 [舊, ..., 新] 的列表
    return jsonify(get_log_entries())


@app.route('/update_block_ip', methods=['POST'])
@requires_auth
def update_block_ip():
    """更新全局 BLOCK IP。"""
    new_ip = request.form.get('block_target_ip', '').strip()
    if not is_valid_ip(new_ip, allow_reserved=True):
        flash(f"無效的 IP 地址: {new_ip}。", 'error')
        return redirect(url_for('index'))

    # 必須先讀取現有地圖，因為 save_rewrite_domains 需要完整的 map
    current_map = REWRITE_MAP.copy()
    if save_rewrite_domains(current_map, new_block_target_ip=new_ip):
        flash(f"全局 BLOCK IP 已成功更新為 {new_ip}。", 'success')
    else:
        flash("更新全局 BLOCK IP 失敗。", 'error')

    return redirect(url_for('index'))


@app.route('/add_domain', methods=['POST'])
@requires_auth
def add_domain():
    """新增 HIJACK 或 BLOCK 規則。"""
    domain = request.form.get('domain', '').strip()
    ip = request.form.get('ip', '').strip()
    action_type = request.form.get('action_type', '').upper()

    if not domain or action_type not in ['HIJACK', 'BLOCK']:
        flash("無效的輸入或操作類型。", 'error')
        return redirect(url_for('index'))

    # 格式化域名
    domain_key = format_domain_for_map(domain)

    if action_type == 'HIJACK':
        if not is_valid_ip(ip, allow_reserved=True):
            flash(f"劫持操作需要一個有效的 IP 地址，但收到: {ip}", 'error')
            return redirect(url_for('index'))
    elif action_type == 'BLOCK':
        ip = BLOCK_TARGET_IP  # BLOCK 規則強制使用全局 IP

    # 複製現有規則地圖，準備新增
    current_map = REWRITE_MAP.copy()
    current_map[domain_key] = {'type': action_type, 'ip': ip}

    if save_rewrite_domains(current_map):
        clear_cache_by_domain(domain_key)
        flash(f"規則已成功新增: {action_type} {domain} -> {ip}", 'success')
    else:
        flash("新增規則失敗。", 'error')

    return redirect(url_for('index'))


@app.route('/delete_domain', methods=['POST'])
@requires_auth
def delete_domain():
    """刪除 HIJACK 或 BLOCK 規則。"""
    domain = request.form.get('domain', '').strip()
    if not domain:
        flash("無效的域名。", 'error')
        return redirect(url_for('index'))

    domain_key = format_domain_for_map(domain)
    current_map = REWRITE_MAP.copy()

    if domain_key in current_map:
        del current_map[domain_key]
        if save_rewrite_domains(current_map):
            clear_cache_by_domain(domain_key)
            flash(f"規則已成功刪除: {domain}", 'warning')
        else:
            flash("刪除規則失敗。", 'error')
    else:
        flash(f"域名 {domain} 不存在規則中。", 'error')

    return redirect(url_for('index'))


@app.route('/clear_cache', methods=['POST'])
@requires_auth
def clear_cache_route():
    """處理清除所有快取的請求。"""
    clear_all_cache(log_message_flag=True)
    flash("所有 DNS 快取已清除。", 'success')
    return redirect(url_for('index'))


@app.route('/update_credentials', methods=['POST'])
@requires_auth
def update_credentials():
    """更新 Web 介面登入憑證。"""
    username = request.form.get('username', '').strip()
    password = request.form.get('password', '').strip()

    if not username or not password or len(password) < 6:
        flash("用戶名和密碼不能為空，且密碼長度必須至少為 6 位。", 'error')
        return redirect(url_for('index'))

    try:
        # 使用 Bcrypt 雜湊密碼
        hashed_password = bcrypt.generate_password_hash(password)
        if save_credentials(username, hashed_password):
            # 迫使用戶重新登入
            session.pop('logged_in', None)
            flash('憑證已成功更新並儲存! 請使用新憑證重新登入。', 'success')
            return redirect(url_for('login'))
        else:
            flash("更新憑證失敗，請檢查權限。", 'error')
    except Exception as e:
        flash(f"更新憑證時發生錯誤: {e}", 'error')

    return redirect(url_for('index'))


# ====================================================================
# V. HTML 模板
# ====================================================================

HTML_TEMPLATE = """
<!doctype html>
<html lang="zh-TW">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>DNS Proxy & Hijack 管理介面 {% if is_log_page %} - 系統日誌{% elif is_login_page %} - 登入{% endif %}</title>
    <style>
        /* CSS 樣式定義 */
        :root {
            --bg-color: #1e1e1e; --fg-color: #d4d4d4; --log-bg-color: #1a1a1a; --header-color: #569cd6; --border-color: #383838; --font-mono: Consolas, "Courier New", monospace; --success-color: #4CAF50; --danger-color: #f44747; --warning-color: #ffd700; --button-bg: #3c3c3c; --button-hover: #505050; --block-color: #ff8c00; --login-bg: #2d2d2d; --cache-color: #9370DB; --hijack-color: #c8ffc8; --config-color: #90ee90;
        }

        body { background-color: var(--bg-color); color: var(--fg-color); font-family: var(--font-mono); padding: 20px; margin: 0; font-size: 14px; }
        a { color: var(--header-color); text-decoration: none; } a:hover { text-decoration: underline; }
        .container { max-width: 1200px; margin: auto; }
        h1 { color: var(--header-color); border-bottom: 2px solid var(--header-color); padding-bottom: 10px; margin-bottom: 15px; font-size: 1.8em; }
        h2 { color: var(--fg-color); border-bottom: 1px solid var(--border-color); padding-bottom: 5px; margin-top: 25px; font-size: 1.4em; }
        .status-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 20px; margin-top: 15px; }
        .status-card { background-color: var(--log-bg-color); padding: 15px; border-radius: 6px; border-left: 5px solid var(--header-color); box-shadow: 0 2px 4px rgba(0, 0, 0, 0.3); }
        .status-card h3 { margin-top: 0; margin-bottom: 10px; color: var(--header-color); font-size: 1.1em; }
        .status-badge { display: inline-block; padding: 4px 8px; border-radius: 4px; font-weight: bold; font-size: 0.9em; }
        .status-running { background-color: var(--success-color); color: var(--bg-color); }
        .status-failed { background-color: var(--danger-color); color: white; }
        .status-pending { background-color: var(--warning-color); color: var(--bg-color); }
        .error-message { color: var(--danger-color); font-size: 0.9em; margin-top: 5px; }
        .stats-card { border-left: 5px solid var(--warning-color); }
        .stat-item { margin: 5px 0; display: flex; justify-content: space-between; }
        .stat-item span:last-child { font-weight: bold; color: var(--success-color); }
        .stat-error span:last-child { color: var(--danger-color); }
        .stat-block span:last-child { color: var(--block-color); }
        .stat-cache span:last-child { color: var(--cache-color); }
        .management-section { display: grid; grid-template-columns: 1fr 1fr; gap: 20px; margin-top: 20px; }
        @media (max-width: 900px) { .management-section { grid-template-columns: 1fr; } }
        .card-management { background-color: var(--log-bg-color); padding: 20px; border-radius: 6px; box-shadow: 0 2px 4px rgba(0, 0, 0, 0.3); border: 1px solid var(--border-color); }
        .card-management h3 { color: var(--warning-color); margin-top: 0; border-bottom: 1px dashed var(--border-color); padding-bottom: 10px; }
        .card-management.hijack h3 { color: var(--hijack-color); }
        .card-management.block h3 { color: var(--block-color); }
        .card-management.upstream h3 { color: var(--config-color); } 
        .form-control { background-color: var(--bg-color); border: 1px solid var(--border-color); color: var(--fg-color); padding: 8px; border-radius: 4px; width: 250px; margin-right: 10px; box-sizing: border-box; }
        .short-control { width: 150px; }
        .full-width { width: 100%; }
        .form-group { margin-bottom: 15px; }
        .form-inline { display: flex; align-items: center; margin-bottom: 15px; }
        .btn { padding: 8px 15px; border: none; border-radius: 4px; cursor: pointer; font-weight: bold; transition: background-color 0.2s; text-align: center; }
        .btn-primary { background-color: var(--button-bg); color: var(--fg-color); }
        .btn-primary:hover { background-color: var(--button-hover); }
        .btn-danger { background-color: #8B0000; color: white; font-weight: normal; font-size: 0.8em; padding: 4px 8px; }
        .btn-danger:hover { background-color: #b00000; }
        .btn-success { background-color: var(--success-color); color: white; }
        .btn-success:hover { background-color: #38761d; }
        .btn-block-add { background-color: var(--block-color); color: var(--bg-color); }
        .btn-block-add:hover { background-color: #d87000; }
        .btn-config { background-color: var(--config-color); color: var(--bg-color); } 
        .btn-config:hover { background-color: #79d279; }
        .domain-list { list-style: none; padding: 0; max-height: 250px; overflow-y: auto; border: 1px solid var(--border-color); margin-top: 10px; border-radius: 4px; }
        .domain-list li { padding: 5px 10px; border-bottom: 1px dashed #282828; display: flex; justify-content: space-between; align-items: center; }
        .domain-list li span:first-child { width: 40%; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
        .domain-list li span:nth-child(2) { width: 35%; font-size: 0.95em; }
        .domain-list.hijack-list li span:nth-child(2) { color: var(--hijack-color); }
        .domain-list.block-list li span:nth-child(2) { color: var(--block-color); }
        .domain-list li:nth-child(even) { background-color: #1c1c1c; }
        .domain-list li:last-child { border-bottom: none; }
        .flash-message { padding: 10px; margin-bottom: 15px; border-radius: 4px; font-weight: bold; }
        .flash-success { background-color: #38761d; color: white; }
        .flash-error { background-color: #ff0000; color: white; }
        .flash-warning { background-color: var(--warning-color); color: var(--bg-color); }
        .log-filter { margin-bottom: 15px; display: flex; gap: 10px; align-items: center; }
        .log-container { background-color: var(--log-bg-color); border: 1px solid var(--border-color); max-height: 70vh; overflow-y: scroll; padding: 10px; font-size: 0.9em; white-space: pre-wrap; }
        .log-line { line-height: 1.5; padding: 2px 0; word-break: break-all; }
        .log-level-error, .log-level-fatal { color: var(--danger-color); font-weight: bold; }
        .log-level-warning { color: var(--warning-color); }
        .log-level-rewrite, .log-level-hijack { color: var(--hijack-color); }
        .log-level-block { color: var(--block-color); }
        .log-level-forward { color: var(--header-color); }
        .log-level-cache { color: var(--cache-color); }
        .nav { margin-bottom: 20px; display: flex; gap: 15px; border-bottom: 1px solid var(--border-color); padding-bottom: 10px; }
        .login-card { background-color: var(--login-bg); padding: 30px; border-radius: 8px; max-width: 400px; margin: 50px auto; box-shadow: 0 4px 8px rgba(0, 0, 0, 0.5); border-top: 3px solid var(--header-color); }
        .login-card h2 { border: none; text-align: center; }
        .login-card input[type="text"], .login-card input[type="password"] { width: 100%; margin-bottom: 15px; }
    </style>
</head>
<body>

<div class="container">

    {# 登入頁面 #}
    {% if is_login_page %}
        <div class="login-card">
            <h2>🔐 登入管理介面</h2>
            {% with messages = get_flashed_messages(with_categories=true) %}
                {% if messages %}
                    {% for category, message in messages %}
                        <div class="flash-message flash-{{ category }}">{{ message }}</div>
                    {% endfor %}
                {% endif %}
            {% endwith %}
            <form method="POST" action="{{ url_for('login') }}">
                <div class="form-group">
                    <input type="text" name="username" placeholder="用戶名 (預設: admin)" required class="form-control full-width">
                </div>
                <div class="form-group">
                    <input type="password" name="password" placeholder="密碼 (預設: admin123)" required class="form-control full-width">
                </div>
                <button type="submit" class="btn btn-primary full-width">登入</button>
            </form>
            <p style="margin-top: 20px; font-size: 0.8em; text-align: center; color: #777;">使用 HTTPS 連接到 {{ FLASK_HOST }}:{{ FLASK_PORT }}</p>
        </div>
    {% endif %}

    {% if session.get('logged_in') %}
    <div class="nav">
        <a href="{{ url_for('index') }}" class="btn btn-primary">🏠 主頁面</a>
        <a href="{{ url_for('logs') }}" class="btn btn-primary">📜 系統日誌</a>
        <a href="{{ url_for('logout') }}" class="btn btn-primary">🚪 登出</a>
    </div>
    {% endif %}


    {% if session.get('logged_in') and not is_login_page %}
        <h1>{% if is_log_page %}系統日誌{% else %}DNS Proxy 管理儀表板{% endif %}</h1>

        {% with messages = get_flashed_messages(with_categories=true) %}
            {% if messages %}
                {% for category, message in messages %}
                    <div class="flash-message flash-{{ category }}">{{ message }}</div>
                {% endfor %}
            {% endif %}
        {% endwith %}


        {% if not is_log_page %}

            {# 狀態與統計 #}
            <h2>📈 服務狀態與流量統計</h2>
            <div class="status-grid">

                {# DNS 狀態卡片 #}
                <div class="status-card">
                    <h3>DNS 服務狀態</h3>
                    {% set dns_status = SERVICE_STATUS.dns_status %}
                    <span class="status-badge status-{{ dns_status.lower() }}">
                        {% if dns_status == 'RUNNING' %}🟢 運行中{% elif dns_status == 'FAILED' %}🔴 失敗{% else %}🟡 等待中{% endif %}
                    </span>
                    {% if SERVICE_STATUS.dns_error %}
                        <p class="error-message">錯誤: {{ SERVICE_STATUS.dns_error }}</p>
                    {% endif %}
                    <p>綁定地址: <code>{{ DNS_HOST }}:{{ DNS_PORT }}</code></p>
                    <p>上游 DNS: <code>{{ UPSTREAM_DNS }}:53</code></p>
                </div>

                {# Web 狀態卡片 #}
                <div class="status-card">
                    <h3>Web 管理狀態</h3>
                    {% set flask_status = SERVICE_STATUS.flask_status %}
                    <span class="status-badge status-{{ flask_status.lower() }}">
                        {% if flask_status == 'RUNNING' %}🟢 運行中{% elif flask_status == 'FAILED' %}🔴 失敗{% else %}🟡 等待中{% endif %}
                    </span>
                    {% if SERVICE_STATUS.flask_error %}
                        <p class="error-message">錯誤: {{ SERVICE_STATUS.flask_error }}</p>
                    {% endif %}
                    <p>Web 地址: <code>{{ FLASK_HOST }}:{{ FLASK_PORT }} (HTTPS)</code></p>
                    <p>認證用戶: <code>{{ WEB_USERNAME }}</code></p>
                </div>

                {# 流量統計卡片 #}
                <div class="status-card stats-card">
                    <h3>流量統計 (自 {{ TRAFFIC_STATS.start_time }})</h3>
                    {% set total_queries = TRAFFIC_STATS.total_queries %}
                    <div class="stat-item"><span>總查詢數:</span> <span>{{ "{:,}".format(total_queries) }}</span></div>
                    <div class="stat-item stat-cache"><span>快取命中:</span> <span>{{ "{:,}".format(TRAFFIC_STATS.cache_hit_count) }} ({{ "{:.2f}%".format(TRAFFIC_STATS.cache_hit_count / total_queries * 100) if total_queries else '0.00%' }})</span></div>
                    <div class="stat-item"><span>轉發查詢:</span> <span>{{ "{:,}".format(TRAFFIC_STATS.forward_count) }}</span></div>
                    <div class="stat-item stat-block"><span>🚫 禁止次數:</span> <span>{{ "{:,}".format(TRAFFIC_STATS.block_count) }}</span></div>
                    <div class="stat-item stat-error"><span>❌ 錯誤次數:</span> <span>{{ "{:,}".format(TRAFFIC_STATS.error_count) }}</span></div>
                </div>

                {# 配置統計卡片 #}
                <div class="status-card stats-card">
                    <h3>重寫與快取配置</h3>
                    <div class="stat-item stat-block"><span>全局 BLOCK IP:</span> <span>{{ BLOCK_TARGET_IP }}</span></div>
                    <div class="stat-item"><span>已載入規則數:</span> <span>{{ SERVICE_STATUS.rewrites_loaded }}</span></div>
                    <div class="stat-item stat-cache"><span>當前快取條目:</span> <span>{{ "{:,}".format(DNS_CACHE_SIZE) }} / {{ "{:,}".format(MAX_CACHE_SIZE) }}</span></div>

                    <form method="POST" action="{{ url_for('clear_cache_route') }}" style="margin-top: 10px;">
                        <button type="submit" class="btn btn-primary full-width" onclick="return confirm('確定要清除所有 DNS 快取嗎？')">🧹 清除所有 DNS 快取</button>
                    </form>
                </div>

            </div>

            {# 上游 DNS 配置區塊 #}
            <h2>⚙️ 核心配置管理</h2>
            <div class="management-section">
                <div class="card-management upstream">
                    <h3>🌐 上游 DNS 伺服器設定</h3>
                    <form method="POST" action="{{ url_for('update_upstream_dns') }}" class="form-inline">
                        <label>當前上游 IP: </label>
                        <input type="text" name="upstream_dns_ip" value="{{ UPSTREAM_DNS }}" placeholder="輸入新的上游 DNS IP" required class="form-control short-control">
                        <button type="submit" class="btn btn-config" onclick="return confirm('確定要將上游 DNS 更改為 ' + document.getElementsByName('upstream_dns_ip')[0].value + ' 並清除所有快取嗎？')">💾 更新上游 DNS</button>
                    </form>
                </div>

                {# 認證資訊修改 #}
                <div class="card-management">
                    <h3>🔑 管理員憑證修改</h3>
                    <form method="POST" action="{{ url_for('update_credentials') }}">
                        <div class="form-group">
                            <label>新用戶名:</label>
                            <input type="text" name="username" placeholder="新的管理員用戶名" required class="form-control short-control">
                        </div>
                        <div class="form-group">
                            <label>新密碼:</label>
                            <input type="password" name="password" placeholder="新的管理員密碼 (至少 6 位)" required class="form-control short-control">
                        </div>
                        <button type="submit" class="btn btn-warning">💾 更新憑證並永久儲存</button>
                    </form>
                </div>
            </div>


            {# 域名管理 #}
            <h2>⚙️ 域名重寫與禁止管理</h2>

            <div class="management-section">

                {# HIJACK 劫持管理 #}
                <div class="card-management hijack">
                    <h3>🟢 域名劫持 (HIJACK List, {{ hijack_list | length }} 條)</h3>

                    <form method="POST" action="{{ url_for('add_domain') }}" class="form-inline">
                        <input type="text" name="domain" placeholder="輸入域名" required class="form-control">
                        <input type="text" name="ip" placeholder="目標 IP" required class="form-control short-control">
                        <input type="hidden" name="action_type" value="HIJACK">
                        <button type="submit" class="btn btn-success">➕ 新增劫持</button>
                    </form>

                    <ul class="domain-list hijack-list">
                        {% for item in hijack_list %}
                            <li>
                                <span>{{ item.domain }}</span>
                                <span>➡️ {{ item.ip }}</span>
                                <form method="POST" action="{{ url_for('delete_domain') }}" style="display: inline;">
                                    <input type="hidden" name="domain" value="{{ item.domain }}">
                                    <button type="submit" class="btn btn-danger">刪除</button>
                                </form>
                            </li>
                        {% else %}
                            <li>目前無劫持規則。</li>
                        {% endfor %}
                    </ul>
                </div>

                {# BLOCK 禁止管理 #}
                <div class="card-management block">
                    <h3>🚫 域名禁止 (BLOCK List, {{ block_list | length }} 條)</h3>

                    <form method="POST" action="{{ url_for('update_block_ip') }}" class="form-inline">
                        <label>全局 BLOCK IP: </label>
                        <input type="text" name="block_target_ip" value="{{ BLOCK_TARGET_IP }}" required class="form-control short-control" style="width: 120px;">
                        <button type="submit" class="btn btn-primary">更新全局IP</button>
                    </form>

                    <form method="POST" action="{{ url_for('add_domain') }}" class="form-inline">
                        <input type="text" name="domain" placeholder="輸入域名" required class="form-control">
                        <input type="hidden" name="ip" value="{{ BLOCK_TARGET_IP }}"> 
                        <input type="hidden" name="action_type" value="BLOCK">
                        <button type="submit" class="btn btn-block-add">➕ 新增禁止</button>
                    </form>

                    <ul class="domain-list block-list">
                        {% for item in block_list %}
                            <li>
                                <span>{{ item.domain }}</span>
                                <span>➡️ {{ item.ip }}</span>
                                <form method="POST" action="{{ url_for('delete_domain') }}" style="display: inline;">
                                    <input type="hidden" name="domain" value="{{ item.domain }}">
                                    <button type="submit" class="btn btn-danger">刪除</button>
                                </form>
                            </li>
                        {% else %}
                            <li>目前無禁止規則。</li>
                        {% endfor %}
                    </ul>
                </div>
            </div>


        {% else %}

            {# 日誌頁面 #}
            <h2>📜 實時系統日誌 (最近 {{ MAX_LOGS }} 條)</h2>
            <div class="log-filter">
                <p>ℹ️ **日誌頁面已啟用 1 秒 AJAX 輪詢**。日誌列表排序：**舊的在頂部，新的在底部**。如果滾動到最底部，會自動跟隨最新日誌。</p>
            </div>

            {# 日誌容器 #}
            <div id="log-container" class="log-container">
                <p>正在載入日誌...</p>
            </div>

        {% endif %}
    {% endif %}

</div>

{# --- AJAX 輪詢 JavaScript 區塊：新的在下，舊的在上 (滾動到底部) --- #}
{% if is_log_page %}
<script>
    const refreshInterval = 1000; // 1 秒
    const logContainer = document.getElementById('log-container');
    const SCROLL_TOLERANCE = 10; // 滾動容忍值 (像素)

    // 輔助函數：將日誌 JSON 轉換為 HTML 格式
    function renderLogs(logs) {
        let html = '';
        logs.forEach(entry => {
            const levelClass = 'log-level-' + entry.level.toLowerCase();
            // logs 順序是 [舊, ..., 新]
            html += `<div class="log-line ${levelClass}">${entry.message}</div>`;
        });
        return html;
    }

    // 核心函數：非同步獲取並更新日誌
    async function fetchAndUpdateLogs() {

        // 1. 檢查用戶是否正在查看最新的日誌 (滾動條在底部附近)
        const isNearBottom = logContainer.scrollHeight - logContainer.clientHeight <= logContainer.scrollTop + SCROLL_TOLERANCE;

        try {
            const response = await fetch('{{ url_for("get_latest_logs") }}');

            if (response.status === 401) {
                // 登入超時或未認證，跳轉到登入頁
                window.location.href = '{{ url_for("login") }}';
                return; 
            }
            if (!response.ok) {
                 console.error("Failed to fetch logs. Status:", response.status);
                 logContainer.innerHTML = '<div class="log-level-error">錯誤: 無法從伺服器載入日誌。</div>' + logContainer.innerHTML;
                 return; 
            }

            const logs = await response.json();

            // 2. 渲染新日誌內容 (logs 順序為 舊 -> 新)
            logContainer.innerHTML = renderLogs(logs);

            // 3. 保持滾動位置：如果用戶之前在底部附近，則將滾動條移至新底部
            if (isNearBottom && logs.length > 0) {
                logContainer.scrollTop = logContainer.scrollHeight;
            }

        } catch (error) {
            console.error("Error during log update:", error);
        }
    }

    // 頁面載入時先執行一次，然後設置定時器
    document.addEventListener('DOMContentLoaded', function() {
        // 只有在日誌頁面才啟動輪詢
        if (document.querySelector('#log-container')) {
            fetchAndUpdateLogs(); // 立即執行一次
            // 設置定時輪詢
            setInterval(fetchAndUpdateLogs, refreshInterval);
        }
    });
</script>
{% endif %}


</body>
</html>
"""

# ====================================================================
# VI. 程式入口點
# ====================================================================

if __name__ == '__main__':
    # 載入 Web 憑證（如果不存在則創建預設值）
    load_credentials()

    # 設置 Flask 狀態為 RUNNING
    SERVICE_STATUS["flask_status"] = "RUNNING"
    log_message(f"[Web Thread] Flask Web 服務將運行於 {FLASK_HOST}:{FLASK_PORT} (HTTPS)", level='INFO')

    # 啟動 DNS 服務器線程
    dns_thread = threading.Thread(target=start_dns_server)
    dns_thread.daemon = True
    dns_thread.start()

    # 啟動 Flask Web 服務
    try:
        # 使用 HTTPS 運行
        app.run(host=FLASK_HOST, port=FLASK_PORT, debug=False, ssl_context=(CERT_FILE, KEY_FILE))
    except FileNotFoundError:
        SERVICE_STATUS["flask_status"] = "FAILED"
        SERVICE_STATUS[
            "flask_error"] = f"SSL 憑證檔案 ({CERT_FILE} 或 {KEY_FILE}) 找不到。請確保檔案存在或使用非 HTTPS 模式。"
        log_message(SERVICE_STATUS["flask_error"], level='FATAL')
        # 如果 SSL 失敗，嘗試使用 HTTP 運行 (僅用於調試)
        log_message("❌ 無法啟動 HTTPS。嘗試以 HTTP 模式運行於 443 埠。", level='WARNING')
        try:
            app.run(host=FLASK_HOST, port=443, debug=False)
        except Exception as e:
            SERVICE_STATUS["flask_error"] = f"Flask 服務啟動失敗: {e}"
            log_message(SERVICE_STATUS["flask_error"], level='FATAL')
    except Exception as e:
        SERVICE_STATUS["flask_status"] = "FAILED"
        SERVICE_STATUS["flask_error"] = f"Flask 服務啟動失敗: {e}"
        log_message(SERVICE_STATUS["flask_error"], level='FATAL')