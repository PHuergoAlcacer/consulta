'use strict';
(() => {
const $ = id => document.getElementById(id);
const subtle = crypto.subtle, td = new TextDecoder(), tdu = new TextDecoder('utf-16le');
const dv = b => new DataView(b.buffer, b.byteOffset, b.byteLength);
const cat = (...a) => { const o = new Uint8Array(a.reduce((s, x) => s + x.length, 0)); let p = 0; for (const x of a) { o.set(x, p); p += x.length; } return o; };
const le32 = n => { const o = new Uint8Array(4); dv(o).setUint32(0, n, true); return o; };
const b64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
const hex = s => Uint8Array.from(s.match(/../g).map(v => parseInt(v, 16)));
const sha = async (a, b) => new Uint8Array(await subtle.digest(a, b));

/* ---------- Contenedor CFB (OLE) ---------- */
function cfb(d) {
  const h = dv(d), ss = 1 << h.getUint16(30, true), ms = 1 << h.getUint16(32, true), END = 0xFFFFFFFA;
  const sec = i => d.subarray(ss + i * ss, ss + (i + 1) * ss), k = ss / 4;
  const ids = []; for (let i = 0; i < 109; i++) ids.push(h.getUint32(76 + 4 * i, true));
  let ds = h.getUint32(68, true);
  for (let n = h.getUint32(72, true); n > 0; n--) { const s = dv(sec(ds)); for (let i = 0; i < k - 1; i++) ids.push(s.getUint32(4 * i, true)); ds = s.getUint32(4 * (k - 1), true); }
  const fat = []; for (const f of ids) if (f < END) { const s = dv(sec(f)); for (let i = 0; i < k; i++) fat.push(s.getUint32(4 * i, true)); }
  const chain = st => { const o = []; while (st < END && o.length <= fat.length) { o.push(st); st = fat[st]; } return o; };
  const read = st => cat(...chain(st).map(sec));
  const dir = read(h.getUint32(48, true)), dd = dv(dir), ents = [];
  for (let i = 0; i < dir.length; i += 128) {
    const nl = dd.getUint16(i + 64, true);
    ents.push({ name: tdu.decode(dir.subarray(i, i + Math.max(nl - 2, 0))), type: dir[i + 66], start: dd.getUint32(i + 116, true), size: dd.getUint32(i + 120, true) });
  }
  const mini = read(ents[0].start).subarray(0, ents[0].size), mf = [];
  for (const i of chain(h.getUint32(60, true))) { const s = dv(sec(i)); for (let j = 0; j < k; j++) mf.push(s.getUint32(4 * j, true)); }
  const cutoff = h.getUint32(56, true), out = {};
  for (const e of ents) if (e.type === 2) {
    if (e.size < cutoff) { const p = []; let s = e.start; while (s < END) { p.push(mini.subarray(s * ms, (s + 1) * ms)); s = mf[s]; } out[e.name] = cat(...p).subarray(0, e.size); }
    else out[e.name] = read(e.start).subarray(0, e.size);
  }
  return out;
}

/* ---------- Descifrado Office "Agile" (AES-CBC) ---------- */
async function cbc(key, iv, ct) { // AES-CBC sin relleno: se agrega un bloque de relleno válido para WebCrypto
  const k = await subtle.importKey('raw', key, 'AES-CBC', false, ['encrypt', 'decrypt']);
  const pad = new Uint8Array(await subtle.encrypt({ name: 'AES-CBC', iv: ct.subarray(ct.length - 16) }, k, new Uint8Array(0)));
  return new Uint8Array(await subtle.decrypt({ name: 'AES-CBC', iv }, k, cat(ct, pad)));
}
async function decrypt(data, pw) {
  const s = cfb(data), info = s.EncryptionInfo, pk = s.EncryptedPackage;
  if (!info || !pk) throw new Error('FORMAT');
  const xml = td.decode(info.subarray(8));
  const at = (t, a) => { const m = xml.match(new RegExp('<(?:\\w+:)?' + t + ' [^>]*?' + a + '="([^"]*)"')); if (!m) throw new Error('FORMAT'); return m[1]; };
  const kd = a => at('keyData', a), ek = a => at('encryptedKey', a);
  const alg = ek('hashAlgorithm').replace('SHA', 'SHA-'), spin = +ek('spinCount'), n = +ek('keyBits') / 8, salt = b64(ek('saltValue'));
  const pwb = new Uint8Array(pw.length * 2);
  for (let i = 0; i < pw.length; i++) { pwb[2 * i] = pw.charCodeAt(i) & 255; pwb[2 * i + 1] = pw.charCodeAt(i) >> 8; }
  let h = await sha(alg, cat(salt, pwb));
  for (let i = 0; i < spin; i++) h = await sha(alg, cat(le32(i), h));
  const dk = async blk => { const d = await sha(alg, cat(h, blk)), o = new Uint8Array(n).fill(0x36); o.set(d.subarray(0, Math.min(n, d.length))); return o; };
  const iv = salt.subarray(0, 16);
  const vi = (await cbc(await dk(hex('fea7d2763b4b9e79')), iv, b64(ek('encryptedVerifierHashInput')))).subarray(0, 16);
  const vv = await cbc(await dk(hex('d7aa0f6d3061344e')), iv, b64(ek('encryptedVerifierHashValue')));
  const hv = await sha(alg, vi);
  if (!hv.every((x, i) => x === vv[i])) throw new Error('PASS');
  const key = (await cbc(await dk(hex('146e0be7abacd0d6')), iv, b64(ek('encryptedKeyValue')))).subarray(0, +kd('keyBits') / 8);
  const total = dv(pk).getUint32(0, true), body = pk.subarray(8), ka = kd('hashAlgorithm').replace('SHA', 'SHA-'), ks = b64(kd('saltValue')), bs = +kd('blockSize'), parts = [];
  for (let i = 0, b = 0; i < body.length; i += 4096, b++) {
    let seg = body.subarray(i, i + 4096); if (seg.length % 16) seg = cat(seg, new Uint8Array(16 - seg.length % 16));
    parts.push(await cbc(key, (await sha(ka, cat(ks, le32(b)))).subarray(0, bs), seg));
  }
  return cat(...parts).subarray(0, total);
}

/* ---------- Lectura del .xlsx ---------- */
async function unzip(z) {
  const d = dv(z); let e = z.length - 22; while (e >= 0 && d.getUint32(e, true) !== 0x06054b50) e--;
  if (e < 0) throw new Error('FORMAT');
  let p = d.getUint32(e + 16, true); const n = d.getUint16(e + 10, true), f = {};
  for (let i = 0; i < n; i++) {
    const m = d.getUint16(p + 10, true), cs = d.getUint32(p + 20, true), nl = d.getUint16(p + 28, true), xl = d.getUint16(p + 30, true), cl = d.getUint16(p + 32, true), lo = d.getUint32(p + 42, true);
    const name = td.decode(z.subarray(p + 46, p + 46 + nl)); p += 46 + nl + xl + cl;
    if (!/^xl\/(worksheets\/sheet\d+|sharedStrings)\.xml$/.test(name)) continue;
    const st = lo + 30 + d.getUint16(lo + 26, true) + d.getUint16(lo + 28, true), raw = z.subarray(st, st + cs);
    f[name] = td.decode(m === 0 ? raw : new Uint8Array(await new Response(new Blob([raw]).stream().pipeThrough(new DecompressionStream('deflate-raw'))).arrayBuffer()));
  }
  return f;
}
const unesc = s => s.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&#(\d+);/g, (_, c) => String.fromCharCode(c)).replace(/&amp;/g, '&');
const txt = s => unesc([...s.matchAll(/<t[^>]*>([\s\S]*?)<\/t>/g)].map(x => x[1]).join(''));
function sheet(f) {
  const ss = f['xl/sharedStrings.xml'] ? [...f['xl/sharedStrings.xml'].matchAll(/<si>([\s\S]*?)<\/si>/g)].map(m => txt(m[1])) : [];
  const nm = Object.keys(f).filter(k => /worksheets/.test(k)).sort((a, b) => parseInt(a.match(/\d+/)) - parseInt(b.match(/\d+/)))[0];
  if (!nm) throw new Error('FORMAT');
  const rows = [];
  for (const r of f[nm].matchAll(/<row\b[^>]*?[^\/]>([\s\S]*?)<\/row>/g)) {
    const row = [];
    for (const c of r[1].matchAll(/<c\s([^>]*?)(?:\/>|>([\s\S]*?)<\/c>)/g)) {
      const ref = /r="([A-Z]+)/.exec(c[1]); if (!ref) continue;
      let col = 0; for (const ch of ref[1]) col = col * 26 + ch.charCodeAt(0) - 64; col--;
      const t = (/\bt="(\w+)"/.exec(c[1]) || [])[1], body = c[2] || '', v = (/<v>([\s\S]*?)<\/v>/.exec(body) || [])[1];
      row[col] = t === 's' ? ss[+v] : t === 'inlineStr' ? txt(body) : v == null ? '' : unesc(v);
    }
    rows.push(row);
  }
  return rows;
}
const norm = s => String(s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().trim();
function build(rows) {
  const h = (rows[0] || []).map(norm), ix = (k, d) => { const i = h.indexOf(k); return i < 0 ? d : i; };
  const c = [ix('contribuyente', 0), ix('cuit contribuyente', 1), ix('cuit ddjj', 2), ix('clave', 3)];
  return rows.slice(1).filter(r => r.some(Boolean)).map(r => ({ n: r[c[0]] || '', a: r[c[1]] || '', b: r[c[2]] || '', k: r[c[3]] || '' }));
}

/* ---------- Pantalla ---------- */
let data = null, picked = null, idle = 0, hiddenAt = 0, f1 = '', arca = null, active = null, grace = false;
const fmt = s => /^\d{11}$/.test(s) ? `${s.slice(0, 2)}-${s.slice(2, 10)}-${s.slice(10)}` : s;
const el = (t, c, x) => { const e = document.createElement(t); if (c) e.className = c; if (x != null) e.textContent = x; return e; };
const msg = x => { $('msg').textContent = x || ''; };
function toast(x) { const t = $('toast'); t.textContent = x; t.classList.add('on'); setTimeout(() => t.classList.remove('on'), 1200); }
async function copy(x) {
  try { await navigator.clipboard.writeText(x); } catch { const a = el('textarea'); a.value = x; document.body.appendChild(a); a.select(); document.execCommand('copy'); a.remove(); }
  toast('Copiado');
}
const safeUrl = x => { try { let s = String(x || '').trim().replace(/^["'<]+|["'>]+$/g, ''); if (!s) return null; s = s.replace(/^http:\/\//i, 'https://'); if (!/^https:\/\//i.test(s)) s = 'https://' + s; const u = new URL(s); return u.hostname.includes('.') ? u.href : null; } catch { return null; } };
function copySync(x) { // síncrono: tiene que correr dentro del toque, antes de abrir ARCA
  const a = el('textarea'); a.value = x; a.readOnly = true; a.style.cssText = 'position:fixed;top:0;opacity:0;font-size:16px';
  document.body.appendChild(a); a.focus({ preventScroll: true }); a.select(); a.setSelectionRange(0, x.length);
  let ok = false; try { ok = document.execCommand('copy'); } catch {} a.remove(); return ok;
}
function ingresar(r) {
  if (!r.b) return toast('Falta el CUIT DDJJ');
  const ir = () => window.open(arca, '_blank', 'noopener,noreferrer');
  if (copySync(r.b)) { toast('CUIT DDJJ copiado'); ir(); }
  else if (navigator.clipboard) navigator.clipboard.writeText(r.b).then(() => { toast('CUIT DDJJ copiado'); ir(); }, () => { toast('No se pudo copiar el CUIT'); ir(); });
  else { toast('No se pudo copiar el CUIT'); ir(); }
  active = r; grace = true; bump();
  const b = $('bar'), k = el('button', 'p', 'Copiar clave'), c = el('button', '', 'Copiar CUIT DDJJ'), x = el('button', 'x', '✕');
  k.onclick = () => { copy(r.k); setTimeout(() => navigator.clipboard.writeText(' ').catch(() => {}), 60000); };
  c.onclick = () => copy(r.b);
  x.onclick = () => { active = null; grace = false; b.style.display = 'none'; document.body.classList.remove('bar'); };
  b.replaceChildren(el('div', 'who', 'ARCA · ' + r.n), c, k, x); b.style.display = 'flex'; document.body.classList.add('bar');
}
function line(label, val, secret) {
  const r = el('div', 'r'), v = el('b', '', secret ? '••••••••' : fmt(val)), cp = el('button', '', 'Copiar');
  r.append(el('span', '', label), v);
  if (secret) {
    const ver = el('button', '', 'Ver'); let tm = 0;
    ver.onclick = () => { clearTimeout(tm); if (v.textContent === val) { v.textContent = '••••••••'; ver.textContent = 'Ver'; return; } v.textContent = val; ver.textContent = 'Ocultar'; tm = setTimeout(() => { v.textContent = '••••••••'; ver.textContent = 'Ver'; }, 10000); };
    r.append(ver);
  }
  cp.onclick = () => copy(val); r.append(cp); return r;
}
function render() {
  const q = norm($('q').value), qd = q.replace(/\D/g, ''), L = $('list'); L.replaceChildren();
  const rows = data.filter(r => !q || norm(r.n).includes(q) || (qd && (r.a.includes(qd) || r.b.includes(qd)))), shown = rows.slice(0, 100);
  for (const r of shown) { const c = el('div', 'card'); c.append(el('h2', '', r.n), line('CUIT Contrib.', r.a), line('CUIT DDJJ', r.b), line('Clave', r.k, true));
    if (arca) { const g = el('button', 'p arca', 'Ingresar a ARCA'); g.onclick = () => ingresar(r); c.append(g); }
    L.append(c); }
  $('info').textContent = `${rows.length} de ${data.length}` + (rows.length > 100 ? ' · mostrando 100, afiná la búsqueda' : '') + ($('info').dataset.mod || '') + (arca ? '' : f1 ? ' · F1 no tiene una URL válida: «' + f1.slice(0, 40) + '»' : ' · falta la URL de ARCA en la celda F1');
}
function lock(m) {
  data = null; picked = null; arca = null; active = null; grace = false; $('bar').style.display = 'none'; document.body.classList.remove('bar'); clearTimeout(idle); $('list').replaceChildren(); $('q').value = ''; $('pw').value = ''; $('file').value = '';
  $('view').style.display = 'none'; $('login').style.display = ''; msg(m || '');
}
function bump() { clearTimeout(idle); if (data) idle = setTimeout(() => lock('Sesión cerrada por inactividad.'), grace ? 240000 : 120000); }
['pointerdown', 'keydown', 'input', 'scroll'].forEach(e => addEventListener(e, bump, { passive: true }));
document.addEventListener('visibilitychange', () => { if (document.hidden) hiddenAt = Date.now(); else if (data && Date.now() - hiddenAt > (grace ? 240000 : 60000)) lock('Sesión cerrada.'); });

function dropboxUrl() {
  try {
    const u = new URL(decodeURIComponent(location.hash.slice(1)));
    if (u.protocol !== 'https:' || !/(^|\.)dropbox(usercontent)?\.com$/.test(u.hostname)) return null;
    u.hostname = 'dl.dropboxusercontent.com'; u.searchParams.set('dl', '1'); u.searchParams.delete('raw'); return u.href;
  } catch { return null; }
}
async function abrir(fromFile) {
  const pw = $('pw').value; if (!pw) return msg('Escribí la contraseña.');
  const go = $('go'); go.disabled = true; msg('Abriendo… puede tardar unos segundos.');
  try {
    let buf, mod = '';
    if (picked) buf = await picked.arrayBuffer();
    else {
      const url = dropboxUrl(); if (!url) { msg('No hay un archivo elegido ni un link de Dropbox. Elegí un archivo en «Abrir un archivo descargado» o usá la dirección completa.'); return; }
      let res; try { res = await fetch(url, { cache: 'no-store', credentials: 'omit', referrerPolicy: 'no-referrer' }); } catch { throw new Error('NET'); }
      if (!res.ok) throw new Error('NET');
      buf = await res.arrayBuffer(); const lm = res.headers.get('last-modified'); if (lm) mod = ' · archivo del ' + new Date(lm).toLocaleString('es-AR', { dateStyle: 'short', timeStyle: 'short' });
    }
    const raw = new Uint8Array(buf);
    if (raw[0] !== 0xD0) throw new Error('PLAIN');
    const rows = sheet(await unzip(await decrypt(raw, pw))); data = build(rows); f1 = String((rows[0] && rows[0][5]) || ''); arca = safeUrl(f1);
    $('info').dataset.mod = mod; $('pw').value = '';
    $('login').style.display = 'none'; $('view').style.display = 'block'; msg(''); render(); bump();
  } catch (e) {
    data = null;
    msg({ PASS: 'Contraseña incorrecta.', NET: 'No se pudo descargar el archivo. Revisá la conexión o avisá al administrador.', PLAIN: 'El archivo no está cifrado. Avisá al administrador.' }[e.message] || 'No se pudo leer el archivo.');
  } finally { go.disabled = false; }
}
const eye = $('eye'), ver = x => { $('pw').type = x ? 'text' : 'password'; };
eye.addEventListener('pointerdown', e => { e.preventDefault(); eye.setPointerCapture(e.pointerId); ver(true); });
['pointerup', 'pointercancel', 'lostpointercapture'].forEach(t => eye.addEventListener(t, () => ver(false)));
eye.addEventListener('keydown', e => { if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); ver(true); } });
eye.addEventListener('keyup', () => ver(false));
eye.addEventListener('contextmenu', e => e.preventDefault());
eye.addEventListener('blur', () => ver(false));
addEventListener('pagehide', () => ver(false));
$('f').addEventListener('submit', e => { e.preventDefault(); ver(false); abrir(); });
$('file').addEventListener('change', e => {
  picked = e.target.files[0] || null; if (!picked) return;
  if ($('pw').value) abrir(); else { msg('Archivo elegido: ' + picked.name + '. Escribí la contraseña y tocá Abrir.'); $('pw').focus(); }
});
if (!dropboxUrl()) document.querySelector('details').open = true;
$('q').addEventListener('input', () => data && render());
$('close').onclick = () => lock();
})();
