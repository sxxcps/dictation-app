const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const edgeTts = require('./edge-tts.cjs');

const ROOT = __dirname;
const DATA = path.join(ROOT, 'data.json');
const CACHE_DIR = path.join(ROOT, 'tts-cache');
const PORT = process.env.PORT || 8000;

try { fs.mkdirSync(CACHE_DIR, { recursive: true }); } catch (e) {}

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.mp3': 'audio/mpeg',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.ico': 'image/x-icon'
};

function mimeOf(fp) { return MIME[path.extname(fp).toLowerCase()] || 'application/octet-stream'; }

function sendText(res, code, text) {
  if (res.headersSent) { try { res.end(); } catch (e) {} return; }
  res.writeHead(code, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end(text);
}

// ---------- 真人发音：有道词典音源 / Edge 神经网络语音，落盘缓存 ----------
async function handleTTS(query, res) {
  const text = String(query.get('text') || '').trim().slice(0, 120);
  if (!text) return sendText(res, 400, 'missing text');
  const engine = query.get('engine') === 'edge' ? 'edge' : 'youdao'; // edge=微软神经网络  youdao=有道真人
  const accent = query.get('accent') === '1' ? '1' : '2';             // 仅 youdao 用：1=英式 2=美式
  const voice = (query.get('voice') || 'en-US-AriaNeural').slice(0, 64);

  const key = crypto.createHash('md5').update(engine + '|' + (engine === 'edge' ? voice : accent) + '|' + text).digest('hex');
  const file = path.join(CACHE_DIR, key + '.mp3');

  const serve = () => {
    if (res.headersSent) { try { res.end(); } catch (e) {} return; }
    let size = 0;
    try { size = fs.statSync(file).size; } catch (e) { return sendText(res, 502, 'cache gone'); }
    res.writeHead(200, {
      'Content-Type': 'audio/mpeg',
      'Content-Length': String(size),
      'Cache-Control': 'public, max-age=604800'
    });
    fs.createReadStream(file).on('error', () => { try { res.end(); } catch (e) {} }).pipe(res);
  };

  // 命中缓存直接返回（绝大多数情况）
  try {
    if (fs.statSync(file).size > 800) return serve();
  } catch (e) {}

  try {
    let buf;
    if (engine === 'edge') {
      buf = await edgeTts.synth(text, voice);
    } else {
      const url = 'https://dict.youdao.com/dictvoice?audio=' + encodeURIComponent(text) + '&type=' + accent;
      const r = await fetch(url, {
        headers: {
          'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120 Safari/537.36',
          'Referer': 'https://dict.youdao.com/'
        }
      });
      if (!r.ok) throw new Error('upstream HTTP ' + r.status);
      buf = Buffer.from(await r.arrayBuffer());
    }
    if (buf.length < 800) throw new Error('empty audio (' + buf.length + ' bytes)');
    await fs.promises.writeFile(file, buf);
    console.log('[tts] cached:', engine, text, buf.length + 'B');
    return serve();
  } catch (e) {
    console.log('[tts] FAIL:', text, '->', e.message);
    return sendText(res, 502, 'tts failed: ' + e.message);
  }
}

// ---------- 主服务 ----------
const server = http.createServer(async (req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET,POST,OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

  if (req.method === 'OPTIONS') { res.writeHead(204); return res.end(); }

  let pathname = '';
  let query;
  try {
    const u = new URL(req.url, 'http://localhost');
    pathname = decodeURIComponent(u.pathname);
    query = u.searchParams;
  } catch (e) {
    return sendText(res, 400, 'bad url');
  }

  // 共享数据接口：电脑与手机读写同一份 data.json
  if (pathname === '/data') {
    if (req.method === 'GET') {
      fs.readFile(DATA, (e, buf) => {
        if (e) { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end('[]'); }
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(buf);
      });
      return;
    }
    if (req.method === 'POST') {
      let body = '';
      req.on('data', c => body += c);
      req.on('end', () => {
        try { JSON.parse(body); } catch (err) { res.writeHead(400); return res.end('bad json'); }
        fs.writeFile(DATA, body, err => {
          if (err) { res.writeHead(500); return res.end('write error'); }
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end('{"ok":true}');
        });
      });
      return;
    }
  }

  // 真人发音
  if (pathname === '/tts') return handleTTS(query, res);

  // 健康检查（前端用来判断真人发音是否可用）
  if (pathname === '/ping') {
    res.writeHead(200, { 'Content-Type': 'application/json' });
    return res.end('{"ok":true,"tts":true}');
  }

  // 静态文件
  let urlPath = pathname || '/';
  if (urlPath === '/') urlPath = '/dictation.html';
  const safe = path.normalize(urlPath).replace(/^(\.\.[\/\\])+/, '');
  const fp = path.join(ROOT, safe);
  fs.readFile(fp, (e, buf) => {
    if (e) { res.writeHead(404); return res.end('not found'); }
    res.writeHead(200, { 'Content-Type': mimeOf(fp) });
    res.end(buf);
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log('dictation server on http://0.0.0.0:' + PORT);
  console.log('  GET  /data                         共享单词本数据');
  console.log('  POST /data                         保存单词本数据');
  console.log('  GET  /tts?text=&accent=            真人发音·有道(美式2/英式1)');
  console.log('  GET  /tts?text=&engine=edge&voice= 真人发音·Edge神经网络语音');
});
