/**
 * 烽火/中兴 CPE 状态小组件 - Egern Widget
 *
 * 环境变量:
 *   CPE_HOST  FH管理地址，默认 192.168.8.1
 *   CPE_USER  FH登录用户名，默认 useradmin
 *   CPE_PASS  FH登录密码，默认 空
 *   CPE_API   FH API前缀，'api'(LG6121F) 或 'fh_api'(其他型号)，默认自动检测
 *   ZTE_HOST  ZTE管理地址，默认 192.168.0.1
 *   ZTE_PASS  ZTE管理密码（留空则用免登录 token 读取数据）
 *   CPE_TYPE  强制设备类型: 'fh' | 'zte' | 'auto'（默认 auto）
 *
 * FH 参考: github.com/Curtion/fiberhome-cpe-lg6121f-sms-notice
 * ZTE 参考: github.com/MavisTok/ZTE_Desktop_Status
 */

// ==================== 配置 ====================

function getConfig(ctx) {
  return {
    host:    ctx.env.CPE_HOST  || '192.168.8.1',
    user:    ctx.env.CPE_USER  || 'useradmin',
    pass:    ctx.env.CPE_PASS  || '',
    api:     ctx.env.CPE_API   || '',
    zteHost: ctx.env.ZTE_HOST  || '192.168.0.1',
    ztePass: ctx.env.ZTE_PASS  || '',
    cpeType: ctx.env.CPE_TYPE  || 'auto',
  };
}

// ==================== AES-128-CBC ====================

// AES S-Box
const SBOX = [
  99,124,119,123,242,107,111,197,48,1,103,43,254,215,171,118,
  202,130,201,125,250,89,71,240,173,212,162,175,156,164,114,192,
  183,253,147,38,54,63,247,204,52,165,229,241,113,216,49,21,
  4,199,35,195,24,150,5,154,7,18,128,226,235,39,178,117,
  9,131,44,26,27,110,90,160,82,59,214,179,41,227,47,132,
  83,209,0,237,32,252,177,91,106,203,190,57,74,76,88,207,
  208,239,170,251,67,77,51,133,69,249,2,127,80,60,159,168,
  81,163,64,143,146,157,56,245,188,182,218,33,16,255,243,210,
  205,12,19,236,95,151,68,23,196,167,126,61,100,93,25,115,
  96,129,79,220,34,42,144,136,70,238,184,20,222,94,11,219,
  224,50,58,10,73,6,36,92,194,211,172,98,145,149,228,121,
  231,200,55,109,141,213,78,169,108,86,244,234,101,122,174,8,
  186,120,37,46,28,166,180,198,232,221,116,31,75,189,139,138,
  112,62,181,102,72,3,246,14,97,53,87,185,134,193,29,158,
  225,248,152,17,105,217,142,148,155,30,135,233,206,85,40,223,
  140,161,137,13,191,230,66,104,65,153,45,15,176,84,187,22,
];

// AES S-Box 逆表（解密用）
const SBOX_INV = new Uint8Array(256);
(function() { for (let i = 0; i < 256; i++) SBOX_INV[SBOX[i]] = i; })();

const RCON = [0,1,2,4,8,16,32,64,128,27,54];

function gmul(a, b) {
  let p = 0;
  for (let i = 0; i < 8; i++) {
    if (b & 1) p ^= a;
    const h = a & 0x80;
    a = (a << 1) & 0xff;
    if (h) a ^= 0x1b;
    b >>= 1;
  }
  return p;
}

function keyExpansion(key16) {
  const w = [...key16];
  for (let i = 4; i < 44; i++) {
    let t = w.slice((i-1)*4, i*4);
    if (i % 4 === 0) {
      t = [t[1],t[2],t[3],t[0]].map(b => SBOX[b]);
      t[0] ^= RCON[i/4];
    }
    const p = w.slice((i-4)*4, (i-3)*4);
    w.push(...t.map((v,j) => v ^ p[j]));
  }
  return w;
}

// state: col-major [col0row0, col0row1, col0row2, col0row3, col1row0, ...]
function bytes2state(b) {
  const s = new Array(16);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) s[c*4+r] = b[r*4+c];
  return s;
}
function state2bytes(s) {
  const b = new Array(16);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) b[r*4+c] = s[c*4+r];
  return b;
}
function ark(s, rk, r) { return s.map((b,i) => b ^ rk[r*16+i]); }

function encBlock(blk, rk) {
  let s = bytes2state(blk);
  s = ark(s, rk, 0);
  for (let r = 1; r <= 10; r++) {
    s = s.map(b => SBOX[b]);
    // shiftRows
    const t = s.slice();
    t[1]=s[5];t[5]=s[9];t[9]=s[13];t[13]=s[1];
    t[2]=s[10];t[10]=s[2];t[6]=s[14];t[14]=s[6];
    t[3]=s[15];t[7]=s[3];t[11]=s[7];t[15]=s[11];
    s = t;
    if (r < 10) {
      const m = s.slice();
      for (let c = 0; c < 4; c++) {
        const [a,b,d,e] = [s[c*4],s[c*4+1],s[c*4+2],s[c*4+3]];
        m[c*4]  =gmul(a,2)^gmul(b,3)^d^e;
        m[c*4+1]=a^gmul(b,2)^gmul(d,3)^e;
        m[c*4+2]=a^b^gmul(d,2)^gmul(e,3);
        m[c*4+3]=gmul(a,3)^b^d^gmul(e,2);
      }
      s = m;
    }
    s = ark(s, rk, r);
  }
  return state2bytes(s);
}

function decBlock(blk, rk) {
  let s = bytes2state(blk);
  s = ark(s, rk, 10);
  for (let r = 9; r >= 0; r--) {
    // inv shiftRows
    const t = s.slice();
    t[1]=s[13];t[5]=s[1];t[9]=s[5];t[13]=s[9];
    t[2]=s[10];t[10]=s[2];t[6]=s[14];t[14]=s[6];
    t[3]=s[7];t[7]=s[11];t[11]=s[15];t[15]=s[3];
    s = t;
    s = s.map(b => SBOX_INV[b]);
    s = ark(s, rk, r);
    if (r > 0) {
      const m = s.slice();
      for (let c = 0; c < 4; c++) {
        const [a,b,d,e] = [s[c*4],s[c*4+1],s[c*4+2],s[c*4+3]];
        m[c*4]  =gmul(a,14)^gmul(b,11)^gmul(d,13)^gmul(e,9);
        m[c*4+1]=gmul(a,9)^gmul(b,14)^gmul(d,11)^gmul(e,13);
        m[c*4+2]=gmul(a,13)^gmul(b,9)^gmul(d,14)^gmul(e,11);
        m[c*4+3]=gmul(a,11)^gmul(b,13)^gmul(d,9)^gmul(e,14);
      }
      s = m;
    }
  }
  return state2bytes(s);
}

// 固定 IV: 字节 112..127 = "pqrstuvwxyz{|}~\x7f"
const AES_IV = Array.from({length:16}, (_,i) => i+112);

function strToBytes(s) {
  // UTF-8 encode
  const r = [];
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c < 0x80) { r.push(c); }
    else if (c < 0x800) { r.push(0xc0|(c>>6), 0x80|(c&0x3f)); }
    else { r.push(0xe0|(c>>12), 0x80|((c>>6)&0x3f), 0x80|(c&0x3f)); }
  }
  return r;
}

function bytesToHex(b) {
  return b.map(x => x.toString(16).padStart(2,'0')).join('');
}

function hexToBytes(h) {
  const b = [];
  for (let i = 0; i < h.length; i += 2) b.push(parseInt(h.slice(i,i+2), 16));
  return b;
}

function bytesToStr(b) {
  let s = '';
  for (let i = 0; i < b.length; i++) {
    const c = b[i];
    if (c < 0x80) { s += String.fromCharCode(c); }
    else if ((c & 0xe0) === 0xc0) { s += String.fromCharCode(((c&0x1f)<<6)|(b[++i]&0x3f)); }
    else { s += String.fromCharCode(((c&0x0f)<<12)|((b[++i]&0x3f)<<6)|(b[++i]&0x3f)); }
  }
  return s;
}

/** AES-128-CBC PKCS7 加密 → 小写 hex */
function aesCbcEncryptHex(plaintext, keyStr) {
  const data = strToBytes(plaintext);
  const pad  = 16 - (data.length % 16);
  const padded = [...data, ...new Array(pad).fill(pad)];
  const key  = strToBytes(keyStr).slice(0,16);
  const rk   = keyExpansion(key);
  let prev   = AES_IV.slice();
  let hex    = '';
  for (let i = 0; i < padded.length; i += 16) {
    const blk = padded.slice(i, i+16).map((b,j) => b ^ prev[j]);
    const enc = encBlock(blk, rk);
    prev = enc;
    hex += bytesToHex(enc);
  }
  return hex;
}

/** hex → AES-128-CBC 解密 → 字符串 */
function aesCbcDecryptHex(hexStr, keyStr) {
  const data = hexToBytes(hexStr.toLowerCase());
  const key  = strToBytes(keyStr).slice(0,16);
  const rk   = keyExpansion(key);
  let prev   = AES_IV.slice();
  const out  = [];
  for (let i = 0; i < data.length; i += 16) {
    const blk = data.slice(i, i+16);
    const dec = decBlock(blk, rk).map((b,j) => b ^ prev[j]);
    prev = blk;
    out.push(...dec);
  }
  // 去 PKCS7 padding
  const pad = out[out.length-1];
  return bytesToStr(out.slice(0, out.length - pad));
}

// ==================== HTTP 工具 ====================

const COMMON_HEADERS = {
  'X-Requested-With': 'XMLHttpRequest',
  'Accept': 'application/json, text/plain, */*',
};

function referer(host) {
  return { ...COMMON_HEADERS, 'Referer': `http://${host}/main.html` };
}

/** GET 请求，若返回 HTML 或非 JSON 则抛出登录错误 */
async function fhGet(ctx, cfg, path) {
  const resp = await ctx.http.get(`http://${cfg.host}${path}`, { headers: referer(cfg.host) });
  const text = await resp.text();
  const t = text.trim();
  if (t.startsWith('<') || t === '' || t === '0') throw new Error('AUTH_REQUIRED');
  try {
    return JSON.parse(t);
  } catch {
    // 非 JSON（如加密 hex 或错误文本）→ 需要登录
    throw new Error('AUTH_REQUIRED');
  }
}

/**
 * POST 加密请求
 * body = hex(AES-CBC({"dataObj":dataObj,"ajaxmethod":method,"sessionid":sid}))
 * 返回解密后的对象，或登录响应的纯文本（字符串）
 */
async function fhPost(ctx, cfg, path, method, dataObj, sid) {
  const payload = JSON.stringify({ dataObj: dataObj ?? null, ajaxmethod: method, sessionid: sid });
  const body    = aesCbcEncryptHex(payload, sid.substring(0, 16));
  const resp    = await ctx.http.post(`http://${cfg.host}${path}`, {
    headers: {
      ...referer(cfg.host),
      'Content-Type': 'application/json; charset=UTF-8',
      'Origin': `http://${cfg.host}`,
    },
    body,
  });
  const text = await resp.text();
  // 登录响应是明文 "0|..." 格式
  if (/^[0-9]\|/.test(text.trim()) || /^[0-9]$/.test(text.trim())) return text.trim();
  // 其他响应是加密 hex
  try {
    const dec = aesCbcDecryptHex(text.trim(), sid.substring(0, 16));
    return JSON.parse(dec);
  } catch {
    return {};
  }
}

// ==================== API 路径自动检测 ====================

async function detectApiBase(ctx, cfg) {
  if (cfg.api) return `/${cfg.api}/tmp`;
  // 尝试 /api 和 /fh_api，取先响应的
  for (const base of ['/api/tmp', '/fh_api/tmp']) {
    try {
      const r = await ctx.http.get(
        `http://${cfg.host}${base}/FHNCAPIS?ajaxmethod=get_refresh_sessionid`,
        { headers: referer(cfg.host) }
      );
      const t = await r.text();
      if (t.includes('sessionid')) {
        cfg._apiBase = base;
        return base;
      }
    } catch (_) {}
  }
  return '/fh_api/tmp';
}

// ==================== 登录与 Session ====================

async function getSessionId(ctx, cfg) {
  const base = cfg._apiBase || await detectApiBase(ctx, cfg);
  const data = await fhGet(ctx, cfg, `${base}/FHNCAPIS?ajaxmethod=get_refresh_sessionid`);
  if (!data.sessionid) throw new Error('无法获取 sessionid');
  return data.sessionid;
}

/**
 * 登录流程:
 * 1. get_refresh_sessionid → sid
 * 2. POST DO_WEB_LOGIN (AES-CBC 加密)
 * 3. 验证登录: 尝试 get_header_info，成功则登录有效
 *    （设备响应为大块加密 hex，不能依赖 "0|..." 明文格式）
 */
async function login(ctx, cfg) {
  const sid = await getSessionId(ctx, cfg);
  const base = cfg._apiBase;

  // 尝试 /api/sign/DO_WEB_LOGIN (LG6121F)，回退到 /fh_api/tmp/FHNCAPIS
  const loginPaths = [
    `${base.replace('/tmp','')}/sign/DO_WEB_LOGIN`,
    `${base}/FHNCAPIS?_${Math.random().toString().slice(2)}`,
  ];

  for (const path of loginPaths) {
    try {
      await fhPost(ctx, cfg, path, 'DO_WEB_LOGIN',
        { username: cfg.user, password: cfg.pass }, sid);
      // 不解析响应码——设备返回大块加密数据而非 "0|..."
      // 验证方式：尝试获取 header_info，若成功则认为已登录
      try {
        const check = await fhGet(ctx, cfg, `${base}/FHAPIS?ajaxmethod=get_header_info`);
        if (check && typeof check === 'object') return; // 登录成功
      } catch (e) {
        if (e.message === 'AUTH_REQUIRED') continue; // 此路径失败，换下一个
        // 其他错误（网络等）也认为登录成功，继续执行
        return;
      }
    } catch (_) {}
  }
  throw new Error('登录失败: 请检查 CPE_USER / CPE_PASS 配置');
}

// ==================== ZTE ubus API ====================

const ZTE_ANON = '00000000000000000000000000000000';

/** 中兴 ubus JSON-RPC 批量请求 */
async function ztePost(ctx, cfg, calls, token) {
  const tok = token || ZTE_ANON;
  const body = JSON.stringify(calls.map((c, i) => ({
    jsonrpc: '2.0', id: i + 1, method: 'call',
    params: [tok, c.obj, c.fn, c.args || {}],
  })));
  const resp = await ctx.http.post(
    `http://${cfg.zteHost}/ubus/?t=${Date.now()}`,
    { headers: { 'Content-Type': 'application/json' }, body }
  );
  const text = await resp.text();
  const arr = JSON.parse(text);
  return arr.map(r => (r.result?.[0] === 0 ? r.result[1] : null));
}

/** SHA-256 纯 JS 实现（用于 ZTE 登录密码哈希）*/
function sha256(msgStr) {
  const K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,
  ];
  const bytes = [];
  for (let i = 0; i < msgStr.length; i++) {
    const c = msgStr.charCodeAt(i);
    if (c < 0x80) bytes.push(c);
    else if (c < 0x800) bytes.push(0xc0|(c>>6), 0x80|(c&0x3f));
    else bytes.push(0xe0|(c>>12), 0x80|((c>>6)&0x3f), 0x80|(c&0x3f));
  }
  bytes.push(0x80);
  while ((bytes.length % 64) !== 56) bytes.push(0);
  const bitLen = (msgStr.length * 8);
  bytes.push(0,0,0,0, (bitLen>>>24)&0xff,(bitLen>>>16)&0xff,(bitLen>>>8)&0xff,bitLen&0xff);
  let [h0,h1,h2,h3,h4,h5,h6,h7] = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  const rotr = (x,n) => (x>>>n)|(x<<(32-n));
  for (let i = 0; i < bytes.length; i += 64) {
    const w = new Uint32Array(64);
    for (let j = 0; j < 16; j++) w[j] = (bytes[i+j*4]<<24)|(bytes[i+j*4+1]<<16)|(bytes[i+j*4+2]<<8)|bytes[i+j*4+3];
    for (let j = 16; j < 64; j++) {
      const s0 = rotr(w[j-15],7)^rotr(w[j-15],18)^(w[j-15]>>>3);
      const s1 = rotr(w[j-2],17)^rotr(w[j-2],19)^(w[j-2]>>>10);
      w[j] = (w[j-16]+s0+w[j-7]+s1) >>> 0;
    }
    let [a,b,c,d,e,f,g,h] = [h0,h1,h2,h3,h4,h5,h6,h7];
    for (let j = 0; j < 64; j++) {
      const S1 = rotr(e,6)^rotr(e,11)^rotr(e,25);
      const ch = (e&f)^(~e&g);
      const t1 = (h+S1+ch+K[j]+w[j]) >>> 0;
      const S0 = rotr(a,2)^rotr(a,13)^rotr(a,22);
      const maj = (a&b)^(a&c)^(b&c);
      const t2 = (S0+maj) >>> 0;
      [h,g,f,e,d,c,b,a] = [g,f,e,(d+t1)>>>0,c,b,a,(t1+t2)>>>0];
    }
    h0=(h0+a)>>>0; h1=(h1+b)>>>0; h2=(h2+c)>>>0; h3=(h3+d)>>>0;
    h4=(h4+e)>>>0; h5=(h5+f)>>>0; h6=(h6+g)>>>0; h7=(h7+h)>>>0;
  }
  return [h0,h1,h2,h3,h4,h5,h6,h7].map(v=>v.toString(16).padStart(8,'0')).join('').toUpperCase();
}

/** ZTE 登录（若 ztePass 为空则使用匿名 token）*/
async function zteLogin(ctx, cfg) {
  if (!cfg.ztePass) return ZTE_ANON;
  const [[info]] = [await ztePost(ctx, cfg, [{ obj:'zwrt_web', fn:'web_login_info', args:{} }])];
  const salt = info?.zte_web_sault || '';
  const h1 = sha256(cfg.ztePass);
  const h2 = sha256(h1 + salt);
  const [[res]] = [await ztePost(ctx, cfg, [{ obj:'zwrt_web', fn:'web_login', args:{ password: h2 } }])];
  if (!res?.ubus_rpc_session) throw new Error('ZTE 登录失败');
  return res.ubus_rpc_session;
}

/** ZTE 数据获取 */
async function fetchZteData(ctx, cfg) {
  const cachedTok = ctx.storage.get('zte_token') || ZTE_ANON;
  let tok = cachedTok;

  const calls = [
    { obj:'zte_nwinfo_api',   fn:'nwinfo_get_netinfo',  args:{} },
    { obj:'zwrt_data',        fn:'get_wwandst',         args:{ source_module:'web', cid:1, type:4 } },
    { obj:'zwrt_data',        fn:'get_wwaniface',       args:{ source_module:'web', cid:1, connect_status:'' } },
  ];

  let [nw, spd, iface] = await ztePost(ctx, cfg, calls, tok);

  // 若 token 过期，重新登录
  if (!nw) {
    tok = await zteLogin(ctx, cfg);
    ctx.storage.set('zte_token', tok);
    [nw, spd, iface] = await ztePost(ctx, cfg, calls, tok);
  }

  nw = nw || {}; spd = spd || {}; iface = iface || {};

  // 优先取 5G 字段，回退 LTE
  const band   = nw.nr5g_action_band  || nw.wan_active_band || nw.lte_band || null;
  const pci    = nw.nr5g_pci          || nw.lte_pci         || null;
  const rsrp   = parseFloat(nw.nr5g_rsrp   || nw.lte_rsrp)  || null;
  const rsrq   = parseFloat(nw.nr5g_rsrq   || nw.lte_rsrq)  || null;
  const sinr   = parseFloat(nw.nr5g_sinr   || nw.nr5g_snr || nw.lte_sinr || nw.lte_snr) || null;
  const rssi   = parseFloat(nw.lte_rssi)   || null;
  const cellId = nw.nr5g_cell_id || nw.lte_cell_id || null;

  return {
    brand: 'ZTE',
    wan: {
      ip:         iface.ipv4_address || '--',
      gateway:    '--',
      dns:        iface.ipv4_dns_prefer || '--',
      connType:   nw.network_type || 'CPE',
      carrier:    nw.network_provider_fullname || '',
      connected:  iface.connect_status === 'connected' || iface.connect_status === 1,
      onlineDevs: 0,
    },
    traffic: {
      txBytes: Number(spd.real_tx_bytes || spd.total_tx_bytes) || 0,
      rxBytes: Number(spd.real_rx_bytes || spd.total_rx_bytes) || 0,
      txSpeed: Number(spd.real_tx_speed) || 0,
      rxSpeed: Number(spd.real_rx_speed) || 0,
    },
    signal: {
      band:       band ? String(band).replace(/^N/i,'') : null,
      pci:        pci != null ? String(pci) : null,
      rsrp, rsrq, sinr, rssi,
      power:      null,
      cqi:        null,
      qci:        null,
      cellId:     cellId ? String(cellId) : null,
      signalLevel: Number(nw.signalbar) || null,
    },
  };
}

// ==================== 设备类型检测 ====================

/**
 * 检测连接的是 FH 还是 ZTE 设备
 * 结果缓存在 storage，避免每次都探测
 */
async function detectDevice(ctx, cfg) {
  if (cfg.cpeType === 'fh')  return 'fh';
  if (cfg.cpeType === 'zte') return 'zte';

  const cached = ctx.storage.get('device_type');
  if (cached === 'fh' || cached === 'zte') return cached;

  // 先探 FH（sessionid 接口）
  for (const base of ['/api/tmp', '/fh_api/tmp']) {
    try {
      const r = await ctx.http.get(
        `http://${cfg.host}${base}/FHNCAPIS?ajaxmethod=get_refresh_sessionid`,
        { headers: { 'X-Requested-With': 'XMLHttpRequest' } }
      );
      const t = await r.text();
      if (t.includes('sessionid')) {
        cfg._apiBase = base;
        ctx.storage.set('device_type', 'fh');
        return 'fh';
      }
    } catch (_) {}
  }

  // 再探 ZTE（ubus 匿名接口）
  try {
    const [nw] = await ztePost(ctx, cfg, [{ obj:'zte_nwinfo_api', fn:'nwinfo_get_netinfo', args:{} }]);
    if (nw && nw.network_type !== undefined) {
      ctx.storage.set('device_type', 'zte');
      return 'zte';
    }
  } catch (_) {}

  // 默认 FH
  return 'fh';
}

// ==================== 数据获取 ====================

/**
 * 通用 POST 数据请求（带session自动刷新）
 * 每次POST前重新获取sessionid（官方实现要求）
 */
async function postData(ctx, cfg, method, dataObj) {
  const sid = await getSessionId(ctx, cfg);
  const base = cfg._apiBase;
  return await fhPost(ctx, cfg, `${base}/FHAPIS`, method, dataObj, sid);
}

const NETWORK_MODE_MAP = {
  '0':'2G', '1':'3G', '2':'4G LTE', '3':'5G NSA', '4':'5G SA', '5':'5G',
};

async function fetchFhData(ctx, cfg) {
  // 确保 API base 已检测
  if (!cfg._apiBase) await detectApiBase(ctx, cfg);

  const base = cfg._apiBase;

  // 直接尝试获取数据；若需要登录再登录（避免依赖 IS_LOGGED_IN 端点）
  let h = {};
  const needsLogin = async () => {
    await login(ctx, cfg);
    try { h = await fhGet(ctx, cfg, `${base}/FHAPIS?ajaxmethod=get_header_info`); } catch (_) {}
  };
  try {
    h = await fhGet(ctx, cfg, `${base}/FHAPIS?ajaxmethod=get_header_info`);
    // 验证返回值是否包含预期字段；若没有说明未登录
    if (!h || typeof h !== 'object' || (!h.NetworkMode && !h.SPN && !h.SignalLevel)) {
      await needsLogin();
    }
  } catch (e) {
    if (e.message === 'AUTH_REQUIRED') await needsLogin();
    // 其他网络错误保持 h = {} 继续渲染
  }

  // POST 获取 NR 信号详情（多个候选方法名，取第一个成功的）
  let nr = {};
  for (const method of ['get_nr_cell_info', 'get_cell_info', 'get_signal_info', 'get_lte_info']) {
    try {
      const r = await postData(ctx, cfg, method, null);
      if (r && typeof r === 'object' && !Array.isArray(r)) { nr = r; break; }
    } catch (_) {}
  }

  // POST 获取 WAN 信息
  let wan = {};
  for (const method of ['get_wan_info', 'get_network_info', 'get_waninfo', 'wan_status']) {
    try {
      const r = await postData(ctx, cfg, method, null);
      if (r && typeof r === 'object' && (r.ipaddr || r.ip || r.wan_ip)) { wan = r; break; }
    } catch (_) {}
  }

  const mode = String(h.NetworkMode ?? '');

  const pick = (a, b) => { const v = a ?? b; return v != null ? Number(v) : null; };

  return {
    wan: {
      ip:        wan.ipaddr || wan.ip || wan.wan_ip || '--',
      gateway:   wan.gateway || wan.wan_gateway || '--',
      dns:       wan.dns || wan.wan_dns || '--',
      connType:  NETWORK_MODE_MAP[mode] || h.WanInterface || 'CPE',
      carrier:   h.SPN || '',
      connected: h.connetStatus === 1 || h.cellularConnetStatus === 1,
      onlineDevs: Number(h.OnlineDevNum) || 0,
    },
    traffic: {
      txBytes: Number(h.TotalBytesSent) || 0,
      rxBytes: Number(h.TotalBytesReceived) || 0,
    },
    signal: {
      band:   String(nr.BAND  ?? h.BAND  ?? '').replace(/^N/i,'') || null,
      pci:    nr.PCI   != null ? String(nr.PCI)   : (h.PCI   != null ? String(h.PCI)   : null),
      rsrp:   pick(nr.RSRP,  h.RSRP),
      rsrq:   pick(nr.RSRQ,  h.RSRQ),
      sinr:   pick(nr.SINR,  h.SINR),
      rssi:   pick(nr.RSSI,  h.RSSI),
      power:  pick(nr.Power, h.Power),
      cqi:    nr.CQI != null ? String(nr.CQI) : (h.CQI != null ? String(h.CQI) : null),
      qci:    nr.QCI != null ? String(nr.QCI) : (h.QCI != null ? String(h.QCI) : null),
      cellId: String(nr.CellId ?? nr.CELLID ?? nr['CELL ID'] ?? h.CellId ?? '') || null,
      signalLevel: Number(h.SignalLevel) || null,
    },
    brand: 'FH',
  };
}

async function fetchAllData(ctx, cfg) {
  const type = await detectDevice(ctx, cfg);
  if (type === 'zte') return await fetchZteData(ctx, cfg);
  return await fetchFhData(ctx, cfg);
}

// ==================== 速率计算 ====================

function calcSpeed(ctx, traffic) {
  // ZTE 直接提供实时速率（单位 Bps）
  if (traffic.txSpeed != null || traffic.rxSpeed != null) {
    return { up: traffic.txSpeed || 0, down: traffic.rxSpeed || 0 };
  }
  const now  = Date.now();
  const prev = ctx.storage.getJSON('prev_traffic');
  ctx.storage.setJSON('prev_traffic', { ...traffic, ts: now });
  if (!prev?.ts) return { up:0, down:0 };
  const dt = (now - prev.ts) / 1000;
  if (dt <= 0 || dt > 300) return { up:0, down:0 };
  return {
    up:   Math.max(0, (traffic.txBytes - prev.txBytes) / dt),
    down: Math.max(0, (traffic.rxBytes - prev.rxBytes) / dt),
  };
}

function formatSpeed(bps) {
  if (bps < 1024)     return bps.toFixed(0) + ' B/s';
  if (bps < 1048576)  return (bps / 1024).toFixed(1) + ' KB/s';
  return (bps / 1048576).toFixed(2) + ' MB/s';
}

// ==================== 信号强度颜色 ====================

function rsrpColor(v) {
  if (v == null) return '#95A5A6';
  if (v >= -80)  return '#2ECC71';
  if (v >= -90)  return '#A8D835';
  if (v >= -100) return '#F7B731';
  if (v >= -110) return '#FC5C65';
  return '#B03A2E';
}
function sinrColor(v) {
  if (v == null) return '#95A5A6';
  if (v >= 20) return '#2ECC71';
  if (v >= 13) return '#A8D835';
  if (v >= 5)  return '#F7B731';
  if (v >= 0)  return '#FC5C65';
  return '#B03A2E';
}
function signalLabel(v) {
  if (v == null) return '未知';
  if (v >= -80)  return '极好';
  if (v >= -90)  return '良好';
  if (v >= -100) return '一般';
  if (v >= -110) return '差';
  return '极差';
}

// ==================== 颜色 ====================

const C = {
  bg1:'#0F1923', bg2:'#162736',
  title:'#5EC4E8', label:'#7A8FA0', value:'#E8ECF0',
  up:'#FF6B6B', down:'#51CF66', accent:'#5EC4E8', dim:'#4A5C6A',
};

// ==================== 组件 ====================

const dot = (rsrp, sz=10) => ({ type:'stack', width:sz, height:sz, borderRadius:sz/2, backgroundColor:rsrpColor(rsrp) });

const infoRow = (icon, label, value, vc) => ({
  type:'stack', direction:'row', alignItems:'center', gap:5,
  children:[
    { type:'image', src:`sf-symbol:${icon}`, color:C.accent, width:12, height:12 },
    { type:'text', text:label, font:{size:'caption2'}, textColor:C.label },
    { type:'spacer' },
    { type:'text', text:String(value ?? '--'), font:{size:'caption2',weight:'medium',family:'Menlo'}, textColor:vc||C.value, maxLines:1, minScale:0.6 },
  ],
});

const sigRow = (label, value, vc) => ({
  type:'stack', direction:'row', alignItems:'center',
  children:[
    { type:'text', text:label, font:{size:'caption2'}, textColor:C.label, width:46 },
    { type:'text', text:String(value ?? '--'), font:{size:'caption2',weight:'semibold',family:'Menlo'}, textColor:vc||C.value },
  ],
});

const speedBlock = (dir, bps, color) => {
  const isUp = dir === 'up';
  return {
    type:'stack', direction:'column', alignItems:'center', gap:2,
    flex:1, backgroundColor:C.bg2, borderRadius:8, padding:[6,4],
    children:[
      { type:'stack', direction:'row', alignItems:'center', gap:4, children:[
        { type:'image', src:`sf-symbol:arrow.${isUp?'up':'down'}.circle.fill`, color, width:12, height:12 },
        { type:'text', text:isUp?'上行':'下行', font:{size:'caption2'}, textColor:C.label },
      ]},
      { type:'text', text:formatSpeed(bps), font:{size:'caption1',weight:'bold',family:'Menlo'}, textColor:color, maxLines:1, minScale:0.5 },
    ],
  };
};

const brandBadge = (brand) => ({
  type:'text', text:brand, font:{size:'caption2',weight:'bold'},
  textColor: brand==='ZTE' ? '#F7B731' : '#5EC4E8',
  backgroundColor: brand==='ZTE' ? '#2A2000' : '#0A1E2E',
  padding:[1,5], borderRadius:4,
});

const titleRow = (wan, sig, sz, brand) => ({
  type:'stack', direction:'row', alignItems:'center', gap:6,
  children:[
    { type:'image', src:'sf-symbol:antenna.radiowaves.left.and.right', color:C.title, width:sz, height:sz },
    { type:'text', text:wan.carrier||wan.connType, font:{size:'headline',weight:'bold'}, textColor:C.title },
    { type:'spacer' },
    brandBadge(brand || 'FH'),
    dot(sig.rsrp, 10),
    { type:'text', text:sig.band?`N${sig.band}`:wan.connType, font:{size:'caption2',weight:'medium'}, textColor:C.dim, backgroundColor:C.bg2, padding:[2,6], borderRadius:4 },
  ],
});

// ==================== Widget 构建 ====================

const BG = { type:'linear', colors:[C.bg1,'#0D1520'], startPoint:{x:0,y:0}, endPoint:{x:0.5,y:1} };

function buildSmall(wan, speed, sig, brand) {
  const f = (v,u) => v != null ? `${v} ${u}` : '--';
  return {
    type:'widget', backgroundGradient:BG, padding:12, gap:6,
    children:[
      { type:'stack', direction:'row', alignItems:'center', gap:6, children:[
        { type:'image', src:'sf-symbol:antenna.radiowaves.left.and.right', color:C.title, width:15, height:15 },
        { type:'text', text:wan.carrier||wan.connType, font:{size:'caption1',weight:'bold'}, textColor:C.title, maxLines:1, minScale:0.7 },
        { type:'spacer' },
        brandBadge(brand || 'FH'),
        dot(sig.rsrp, 10),
      ]},
      infoRow('dot.radiowaves.right', 'BAND', sig.band?`N${sig.band}`:'--'),
      infoRow('cellularbars', 'RSRP', f(sig.rsrp,'dBm'), rsrpColor(sig.rsrp)),
      infoRow('waveform',     'SINR', f(sig.sinr,'dB'),  sinrColor(sig.sinr)),
      { type:'spacer' },
      { type:'stack', direction:'row', gap:6, children:[speedBlock('up',speed.up,C.up), speedBlock('down',speed.down,C.down)] },
    ],
  };
}

function buildMedium(wan, speed, sig, brand) {
  const f = (v,u) => v != null ? `${v} ${u}` : '--';
  return {
    type:'widget', backgroundGradient:BG, padding:14, gap:6,
    children:[
      titleRow(wan, sig, 17, brand),
      { type:'stack', direction:'row', gap:12, flex:1, children:[
        { type:'stack', direction:'column', gap:4, flex:1, children:[
          infoRow('dot.radiowaves.right', 'BAND', sig.band?`N${sig.band}`:'--'),
          infoRow('number',    'PCI',  sig.pci  ?? '--'),
          infoRow('cellularbars', 'RSRP', f(sig.rsrp,'dBm'), rsrpColor(sig.rsrp)),
          infoRow('waveform',  'SINR', f(sig.sinr,'dB'),  sinrColor(sig.sinr)),
          infoRow('chart.bar', 'RSRQ', f(sig.rsrq,'dB')),
          infoRow('antenna.radiowaves.left.and.right', 'RSSI', f(sig.rssi,'dBm')),
        ]},
        { type:'stack', direction:'column', gap:6, width:104, children:[
          speedBlock('up',speed.up,C.up),
          speedBlock('down',speed.down,C.down),
          { type:'stack', direction:'row', alignItems:'center', justifyContent:'center', gap:4, children:[
            dot(sig.rsrp, 8),
            { type:'text', text:signalLabel(sig.rsrp), font:{size:'caption2'}, textColor:rsrpColor(sig.rsrp) },
          ]},
        ]},
      ]},
    ],
  };
}

function buildLarge(wan, speed, sig, brand) {
  const f = (v,u) => v != null ? `${v} ${u}` : '--';
  return {
    type:'widget', backgroundGradient:BG, padding:16, gap:8,
    children:[
      titleRow(wan, sig, 22, brand),
      { type:'stack', direction:'row', gap:12, children:[speedBlock('up',speed.up,C.up), speedBlock('down',speed.down,C.down)] },
      { type:'stack', height:1, backgroundColor:C.bg2 },
      { type:'stack', direction:'column', gap:5, children:[
        { type:'stack', direction:'row', alignItems:'center', gap:6, children:[
          dot(sig.rsrp, 12),
          { type:'text', text:`信号质量: ${signalLabel(sig.rsrp)}`, font:{size:'caption1',weight:'semibold'}, textColor:rsrpColor(sig.rsrp) },
        ]},
        { type:'stack', direction:'row', gap:8, children:[
          { type:'stack', direction:'column', gap:5, flex:1, children:[
            sigRow('BAND',  sig.band?`N${sig.band}`:'--'),
            sigRow('PCI',   sig.pci  ?? '--'),
            sigRow('RSRP',  f(sig.rsrp,'dBm'), rsrpColor(sig.rsrp)),
            sigRow('RSRQ',  f(sig.rsrq,'dB')),
          ]},
          { type:'stack', direction:'column', gap:5, flex:1, children:[
            sigRow('SINR',  f(sig.sinr,'dB'),  sinrColor(sig.sinr)),
            sigRow('RSSI',  f(sig.rssi,'dBm')),
            sigRow('Power', f(sig.power,'dBm')),
            sigRow('CQI',   sig.cqi ?? '--'),
          ]},
        ]},
        wan.ip !== '--' ? infoRow('network', 'WAN IP', wan.ip) : null,
        sig.cellId ? infoRow('number', 'Cell ID', sig.cellId) : null,
        sig.qci    ? sigRow('QCI', sig.qci) : null,
      ].filter(Boolean)},
      { type:'stack', height:1, backgroundColor:C.bg2 },
      { type:'stack', direction:'row', alignItems:'center', gap:6, children:[
        wan.carrier ? { type:'text', text:wan.carrier, font:{size:'caption2'}, textColor:C.label } : null,
        { type:'spacer' },
        wan.onlineDevs > 0 ? { type:'text', text:`${wan.onlineDevs}台在线`, font:{size:'caption2'}, textColor:C.dim } : null,
        { type:'date', date:new Date().toISOString(), format:'time', font:{size:'caption2'}, textColor:C.dim },
      ].filter(Boolean)},
    ],
  };
}

function buildAccessory(speed, sig) {
  return {
    type:'widget',
    children:[{ type:'stack', direction:'row', alignItems:'center', gap:4, children:[
      dot(sig.rsrp, 8),
      { type:'text', text:`↑${formatSpeed(speed.up)} ↓${formatSpeed(speed.down)}`, font:{size:'caption2',weight:'medium',family:'Menlo'} },
    ]}],
  };
}

function buildError(msg) {
  return {
    type:'widget', backgroundGradient:BG, padding:16,
    children:[
      { type:'stack', direction:'row', alignItems:'center', gap:6, children:[
        { type:'image', src:'sf-symbol:exclamationmark.triangle.fill', color:'#FF6B6B', width:18, height:18 },
        { type:'text', text:'FH/ZTE CPE', font:{size:'headline',weight:'bold'}, textColor:C.title },
      ]},
      { type:'spacer' },
      { type:'text', text:msg, font:{size:'caption1'}, textColor:'#FF6B6B' },
      { type:'text', text:'请设置 CPE_HOST/ZTE_HOST 及账号密码', font:{size:'caption2'}, textColor:C.dim },
    ],
  };
}

// ==================== 主入口 ====================

export default async function(ctx) {
  const cfg = getConfig(ctx);
  try {
    const { wan, traffic, signal, brand } = await fetchAllData(ctx, cfg);
    const speed = calcSpeed(ctx, traffic);
    const f = ctx.widgetFamily;
    if (f==='accessoryRectangular'||f==='accessoryInline'||f==='accessoryCircular')
      return buildAccessory(speed, signal);
    if (f==='systemLarge'||f==='systemExtraLarge')
      return buildLarge(wan, speed, signal, brand);
    if (f==='systemMedium')
      return buildMedium(wan, speed, signal, brand);
    return buildSmall(wan, speed, signal, brand);
  } catch(e) {
    return buildError(e.message || '连接失败');
  }
}
