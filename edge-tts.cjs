'use strict';
/*
 * 纯 Node 实现的 Microsoft Edge-TTS（神经网络语音）。
 * 不依赖任何第三方包：GEC 令牌 + 极简 WebSocket 客户端全部用内置模块完成。
 * 对外导出 synth(text, voice) -> Promise<Buffer(mp3)> 与 EDGE_VOICES 列表。
 */
const crypto = require('crypto');
const https = require('https');

const TRUSTED_CLIENT_TOKEN = "6A5AA1D4EAFF4E9FB37E23D68491D6F4";
const WIN_EPOCH = 11644473600;
const S_TO_NS = 1e9;
const _U32 = 0xFFFFFFFF;

const _SHA256_INITIAL = [0x6A09E667,0xBB67AE85,0x3C6EF372,0xA54FF53A,0x510E527F,0x9B05688C,0x1F83D9AB,0x5BE0CD19];
const _SHA256_STATE = [0xFD9FBEA2,0x91243CE7,0xBE499094,0xCD2E1E0A,0x6C006F49,0x04BD35AB,0xFEB0A7E4,0x03EFFBD2];
const _SHA256_SCHEDULE = [0xEB24BF9E,0x1558691F,0xA0C09EE2,0x0CFA32BA,0xA622EE8C,0xD1DD9491,0xC0DD25A0,0xF9E70AB6,0xF0C31573,0x7058CE4E,0x7188E606,0x00E5AB33,0xD258B060,0x72766564];
const _SHA256_ROUND_CONSTANTS = [0x428A2F98,0x71374491,0xB5C0FBCF,0xE9B5DBA5,0x3956C25B,0x59F111F1,0x923F82A4,0xAB1C5ED5,0xD807AA98,0x12835B01,0x243185BE,0x550C7DC3,0x72BE5D74,0x80DEB1FE,0x9BDC06A7,0xC19BF174,0xE49B69C1,0xEFBE4786,0x0FC19DC6,0x240CA1CC,0x2DE92C6F,0x4A7484AA,0x5CB0A9DC,0x76F988DA,0x983E5152,0xA831C66D,0xB00327C8,0xBF597FC7,0xC6E00BF3,0xD5A79147,0x06CA6351,0x14292967,0x27B70A85,0x2E1B2138,0x4D2C6DFC,0x53380D13,0x650A7354,0x766A0ABB,0x81C2C92E,0x92722C85,0xA2BFE8A1,0xA81A664B,0xC24B8B70,0xC76C51A3,0xD192E819,0xD6990624,0xF40E3585,0x106AA070,0x19A4C116,0x1E376C08,0x2748774C,0x34B0BCB5,0x391C0CB3,0x4ED8AA4A,0x5B9CCA4F,0x682E6FF3,0x748F82EE,0x78A5636F,0x84C87814,0x8CC70208,0x90BEFFFA,0xA4506CEB,0xBEF9A3F7,0xC67178F2];
const _SHA256_ADJUSTMENT = 0xC9DC06A7;
const _SHA256_BLOCK_CONSTANTS = _SHA256_ROUND_CONSTANTS.slice(0,14).concat([_SHA256_ADJUSTMENT]).concat(_SHA256_ROUND_CONSTANTS.slice(15));
const _SHA256_SIGMA0_ADJUSTMENT = 0x059C0B80;
const _SHA256_SIGMA1_ADJUSTMENT = 0x000B92C0;
const _CS64_COEFFICIENTS = [[0xE82E91B1,0xB32700D0],[0x44DE24C6,0x88DFF51D],[0x3BEB65BC,0x29514038],[0xC89C5933,0xB328CBDF],[0x8D1EC211,0xD405B4D5],[0x314EF5D5,0x26E55F3C],[0xE92491B1,0x607801C6],[0xF0A5B9D5,0x82B2C1FB],[0x06064CF3,0xFA51A3DA],[0xDA79FA60,0x207CC464],[0xBED20560,0x3C3C74F3],[0x89F9C9F8,0xD2D14B61],[0x35FA38C6,0xBB04A2C1],[0xCB49E3C6,0xC5626167]];
const _CS64_FACTOR = 0x82893933;
const _CS64_ADJUSTMENT0 = 0xF2F90B1A;
const _CS64_ADJUSTMENT1 = 0x0B1A0000;

function _rol16(v){ v &= _U32; return ((v<<16)|(v>>>16)) & _U32; }
function _sigma0(v){ return ((v>>>7)^(v<<25)^(v>>>18)^(v<<14)^(v>>>3)) & _U32; }
function _sigma1(v){ return ((v>>>17)^(v<<15)^(v>>>19)^(v<<13)^(v>>>10)) & _U32; }

function _expand(words, firstWord){
  firstWord = firstWord || 16;
  for(let index=firstWord; index<64; index++){
    const x = words[index-2], y = words[index-15];
    const s1 = ((x>>>17)^(x<<15)^(x>>>19)^(x<<13)^(x>>>10)) & _U32;
    const s0 = ((y>>>7)^(y<<25)^(y>>>18)^(y<<14)^(y>>>3)) & _U32;
    words.push((((s1 + words[index-7]) & _U32) + s0 + words[index-16]) & _U32);
  }
}

function _sha256Rounds(state, words, firstRound){
  let [a,b,c,d,e,f,g,h] = state.map(x=>x>>>0);
  const K = (firstRound===14) ? _SHA256_BLOCK_CONSTANTS : _SHA256_ROUND_CONSTANTS;
  for(let i=firstRound;i<64;i++){
    const S1 = ((e>>>6)|(e<<26)) ^ ((e>>>11)|(e<<21)) ^ ((e>>>25)|(e<<7));
    const ch = g ^ (e & (f ^ g));
    const t1 = (h + S1 + ch + (K[i]>>>0) + (words[i]>>>0)) >>> 0;
    const S0 = ((a>>>2)|(a<<30)) ^ ((a>>>13)|(a<<19)) ^ ((a>>>22)|(a<<10));
    const maj = (a&b) ^ (a&c) ^ (b&c);
    const t2 = (S0 + maj) >>> 0;
    h=g; g=f; f=e; e=(d+t1)>>>0; d=c; c=b; b=a; a=(t1+t2)>>>0;
  }
  return [a,b,c,d,e,f,g,h];
}

function _sha256Init(data){
  const words = new Array(14).fill(0);
  words.push(data.readUIntBE(0,3));
  words.push(data.readUInt32BE(3));
  for(let index=16; index<30; index++){
    let value = _SHA256_SCHEDULE[index-16];
    if(index-2>=14){
      value += (index===16) ? (_sigma1(words[index-2]) ^ _SHA256_SIGMA1_ADJUSTMENT) : _sigma1(words[index-2]);
    }
    if(index-7>=14){ value += words[index-7]; }
    if(index-15>=14){
      value += (index===29) ? (_sigma0(words[index-15]) ^ _SHA256_SIGMA0_ADJUSTMENT) : _sigma0(words[index-15]);
    }
    words.push(value & _U32);
  }
  words.push(((_sigma1(words[28]) + words[23] + _sigma0(words[15]) + words[14] + _SHA256_ADJUSTMENT - _SHA256_ROUND_CONSTANTS[14]) & _U32));
  _expand(words, 31);
  const working = _sha256Rounds(_SHA256_STATE, words, 14);
  return _SHA256_INITIAL.map((x,i)=> (x + working[i]) & _U32);
}

function _sha256Digest(data){
  if(data.length < 7) throw new Error("salt >= 7");
  const length = 57 + data.length;
  const zeroCount = ((55 - length) % 64 + 64) % 64;
  const lenBuf = Buffer.alloc(8);
  lenBuf.writeBigUInt64BE(BigInt(length) * 8n);
  const padded = Buffer.concat([data.subarray(7), Buffer.from([0x80]), Buffer.alloc(zeroCount), lenBuf]);
  let state = _sha256Init(data.subarray(0,7));
  for(let offset=0; offset<padded.length; offset+=64){
    const block = padded.subarray(offset, offset+64);
    const words = [];
    for(let i=0;i<16;i++) words.push(block.readUInt32BE(i*4));
    _expand(words, 16);
    const working = _sha256Rounds(state, words, 0);
    state = state.map((x,i)=> (x + working[i]) & _U32);
  }
  const out = Buffer.alloc(32);
  state.forEach((v,i)=> out.writeUInt32BE(v>>>0, i*4));
  return out;
}

function _rol16Big(v){ v &= 0xFFFFFFFFn; return ((v<<16n)|(v>>16n)) & 0xFFFFFFFFn; }
function _cs64Digest(data, digest){
  const mask = 0xFFFFFFFFn;
  let keyA = BigInt(digest.readUInt32LE(0)) | 1n;
  let keyB = BigInt(digest.readUInt32LE(4)) | 1n;
  const factors = [ (keyA * 0x82893933n) & mask, (keyB * 0x82893933n) & mask ];
  const terms = _CS64_COEFFICIENTS.map(([c], idx) => (BigInt(c) * factors[idx % 2]) & mask);
  const offsets = _CS64_COEFFICIENTS.map(([,o]) => BigInt(o));
  const w = Buffer.concat([Buffer.from([0x00]), data]);
  const leWords = [];
  { let p = 0; while(p < w.length){ let v=0n; for(let i=0;i<4;i++){ v |= BigInt(w[p+i]||0) << (8n*BigInt(i)); } leWords.push(v & mask); p+=4; } if(leWords.length%2) leWords.push(0n); }
  leWords.forEach((word, index)=>{
    let term = (word * ((index%2===0)?keyA:keyB)) & mask;
    let offset = (_rol16Big(word) * ((index%2===0)?0xEF0569FBn:0xC31713DBn)) & mask;
    if(index===0){ term += 0xF2F90B1An * factors[0]; offset += 0x0B1A0000n; }
    terms.push(term & mask);
    offsets.push(offset & mask);
  });
  let swapAcc = 0n, swapLast = 0n, state = 0n, acc = 0n;
  for(let index=0; index<terms.length; index+=2){
    const x = terms[index], y = terms[index+1];
    let t = _rol16Big((offsets[index] + terms[index]) & mask);
    let q = (t * 0x76F50F34n) & mask;
    swapAcc = (swapAcc + ((_rol16Big(q) * 0xC3EFEA97n + q) & mask)) & mask;
    t = _rol16Big((offsets[index+1] + terms[index+1]) & mask);
    q = (t * 0x1881CE3Cn) & mask;
    swapLast = ((_rol16Big(q) * 0x35BD1EC9n + q) & mask);
    swapAcc = (swapAcc + swapLast) & mask;
    state = (state * keyA + x) & mask;
    state = (_rol16Big(state) * 0xCF98B111n) & mask;
    state = (_rol16Big(state) * 0x87085B9Fn) & mask;
    state = (_rol16Big(state) * 0x12CEB96Dn) & mask;
    state = (_rol16Big(state) * 0x257E1D83n) & mask;
    acc = (acc + state) & mask;
    let t2 = (state * keyB + y) & mask;
    t2 = (_rol16Big(t2) * 0xA27416F5n) & mask;
    t2 = (_rol16Big(t2) * 0xD38396FFn) & mask;
    state = ((_rol16Big((_rol16Big(t2) * 0x7C932B89n) & mask) * 0xBFA49F69n) & mask);
    acc = (acc + state) & mask;
  }
  const a = (swapLast ^ state) & mask;
  const b = (swapAcc ^ acc) & mask;
  return [Number(a), Number(b)];
}

function generateSecMsGec(unixTimestamp){
  let ticks = (unixTimestamp==null) ? Date.now()/1000 : Number(unixTimestamp);
  ticks += WIN_EPOCH;
  ticks -= ticks % 300;
  ticks *= S_TO_NS / 100;
  const strToHash = `${ticks.toFixed(0)}${TRUSTED_CLIENT_TOKEN}`;
  const digest = _sha256Digest(Buffer.from(strToHash, 'ascii'));
  const [cs64a, cs64b] = _cs64Digest(Buffer.from(strToHash, 'ascii'), digest);
  const cs64 = Buffer.alloc(8);
  cs64.writeUInt32LE(cs64a>>>0, 0); cs64.writeUInt32LE(cs64b>>>0, 4);
  return `${cs64.toString('hex').toUpperCase()}-${digest.toString('hex').toUpperCase()}`;
}

function uuid(){ return crypto.randomUUID().replace(/-/g,''); }

// ---- 极简 WebSocket 客户端（仅实现 Edge-TTS 所需：发送文本帧 / 解析文本与二进制帧）----
function _wsSendFrame(socket, str){
  const payload = Buffer.from(str, 'utf8');
  const len = payload.length;
  let header;
  if(len < 126){
    header = Buffer.from([0x81, 0x80 | len]);           // FIN + text, masked
  } else if(len < 65536){
    header = Buffer.alloc(4);
    header[0]=0x81; header[1]=0x80|126; header.writeUInt16BE(len,2);
  } else {
    header = Buffer.alloc(10);
    header[0]=0x81; header[1]=0x80|127; header.writeBigUInt64BE(BigInt(len),2);
  }
  const mask = crypto.randomBytes(4);
  const masked = Buffer.alloc(len);
  for(let i=0;i<len;i++) masked[i] = payload[i] ^ mask[i%4];
  socket.write(Buffer.concat([header, mask, masked]));
}

function _wsSendPong(socket, payload){
  let header;
  if(payload.length < 126){ header = Buffer.from([0x8A, 0x80 | payload.length]); }
  else { header = Buffer.alloc(4); header[0]=0x8A; header[1]=0x80|126; header.writeUInt16BE(payload.length,2); }
  const mask = crypto.randomBytes(4);
  const masked = Buffer.alloc(payload.length);
  for(let i=0;i<payload.length;i++) masked[i] = payload[i] ^ mask[i%4];
  socket.write(Buffer.concat([header, mask, masked]));
}

function synth(text, voice){
  voice = voice || 'en-US-AriaNeural';
  return new Promise((resolve, reject)=>{
    const gec = generateSecMsGec();
    const path = `/consumer/speech/synthesize/readaloud/edge/v1?TrustedClientToken=${TRUSTED_CLIENT_TOKEN}&ConnectionId=${uuid()}&Sec-MS-GEC=${gec}&Sec-MS-GEC-Version=2-143.0.3650.75`;
    const key = crypto.randomBytes(16).toString('base64');
    const options = {
      host: 'speech.platform.bing.com',
      port: 443,
      path,
      method: 'GET',
      headers: {
        'Host': 'speech.platform.bing.com',
        'Connection': 'Upgrade',
        'Upgrade': 'websocket',
        'Sec-WebSocket-Key': key,
        'Sec-WebSocket-Version': '13',
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/143.0.0.0 Safari/537.36 Edg/143.0.0.0',
        'Origin': 'chrome-extension://jdiccldimpdaibmpdkjnbmckianbfold',
        'Accept-Encoding': 'gzip, deflate, br, zstd',
        'Accept-Language': 'en-US,en;q=0.9',
        'Pragma': 'no-cache',
        'Cache-Control': 'no-cache',
        'Cookie': `muid=${crypto.randomBytes(16).toString('hex').toUpperCase()};`
      }
    };
    let settled = false;
    const finish = (fn, arg)=>{ if(settled) return; settled = true; fn(arg); };
    const req = https.request(options, ()=>{});
    req.on('upgrade', (res, socket)=>{
      if(res.statusCode !== 101){ return finish(reject, new Error('WS handshake HTTP '+res.statusCode)); }
      const audio = [];
      let buf = Buffer.alloc(0);
      const AUDIO_SEP = 'Path:audio\r\n';
      const tryParse = ()=>{
        while(buf.length >= 2){
          const b0 = buf[0], b1 = buf[1];
          const opcode = b0 & 0x0f;
          const masked = (b1 & 0x80) !== 0;
          let len = b1 & 0x7f;
          let off = 2;
          if(len === 126){ if(buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
          else if(len === 127){ if(buf.length < 10) return; len = Number(buf.readBigUInt64BE(2)); off = 10; }
          if(masked) off += 4;
          if(buf.length < off + len) return;
          let payload = buf.subarray(off, off+len);
          if(masked){ const m = buf.subarray(off-4, off); const p = Buffer.alloc(len); for(let i=0;i<len;i++) p[i]=payload[i]^m[i%4]; payload = p; }
          buf = buf.subarray(off+len);
          if(opcode === 0x9){ _wsSendPong(socket, payload); continue; }
          if(opcode === 0x8){ try{ socket.destroy(); }catch(e){} finish(resolve, Buffer.concat(audio)); continue; }
          if(opcode === 0x1){
            const s = payload.toString('utf8');
            if(s.includes('turn.end')){ try{ socket.destroy(); }catch(e){} finish(resolve, Buffer.concat(audio)); }
            continue;
          }
          if(opcode === 0x2){
            const idx = payload.indexOf(AUDIO_SEP);
            if(idx >= 0) audio.push(payload.subarray(idx + AUDIO_SEP.length));
            continue;
          }
        }
      };
      socket.on('data', d=>{ buf = Buffer.concat([buf, d]); tryParse(); });
      socket.on('error', e=> finish(reject, e));
      socket.on('close', ()=> finish(resolve, Buffer.concat(audio)));
      // 发送 speech.config 与 ssml
      const speechConfig = JSON.stringify({ context: { synthesis: { audio: { metadataoptions: { sentenceBoundaryEnabled:false, wordBoundaryEnabled:false }, outputFormat: "audio-24khz-48kbitrate-mono-mp3" } } } });
      const configMsg = `X-Timestamp:${new Date().toString()}\r\nContent-Type:application/json; charset=utf-8\r\nPath:speech.config\r\n\r\n${speechConfig}`;
      _wsSendFrame(socket, configMsg);
      const ssml = `X-RequestId:${uuid()}\r\nContent-Type:application/ssml+xml\r\nX-Timestamp:${new Date().toISOString()}Z\r\nPath:ssml\r\n\r\n<speak version='1.0' xmlns='http://www.w3.org/2001/10/synthesis' xml:lang='en-US'><voice name='${voice}'><prosody pitch='+0Hz' rate='+0%' volume='+0%'>${text.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')}</prosody></voice></speak>`;
      _wsSendFrame(socket, ssml);
    });
    req.on('response', (res)=>{ finish(reject, new Error('HTTP '+res.statusCode)); try{ res.destroy(); }catch(e){} });
    req.on('error', e=> finish(reject, e));
    req.setTimeout(20000, ()=> finish(reject, new Error('timeout')));
    req.end();
  });
}

// 常用英文神经网络语音（供前端下拉与后端校验）
const EDGE_VOICES = [
  { name: 'en-US-AriaNeural',        label: 'Aria · 美式女声（推荐）' },
  { name: 'en-US-GuyNeural',         label: 'Guy · 美式男声' },
  { name: 'en-US-JennyNeural',       label: 'Jenny · 美式女声' },
  { name: 'en-US-DavisNeural',       label: 'Davis · 美式男声' },
  { name: 'en-US-ChristopherNeural', label: 'Christopher · 美式男声' },
  { name: 'en-GB-SoniaNeural',       label: 'Sonia · 英式女声' },
  { name: 'en-GB-RyanNeural',        label: 'Ryan · 英式男声' },
  { name: 'en-AU-NatashaNeural',     label: 'Natasha · 澳式女声' },
  { name: 'en-CA-ClaraNeural',       label: 'Clara · 加式女声' },
  { name: 'en-IN-NeerjaNeural',      label: 'Neerja · 印度式女声' }
];

module.exports = { synth, generateSecMsGec, EDGE_VOICES };
