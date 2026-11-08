'use strict';
/* 불침번 온라인 서버 — 외부 패키지 없이 Node 내장 모듈만 사용 (http + 직접 구현한 WebSocket) */
const http = require('http'), crypto = require('crypto'), fs = require('fs'), path = require('path');

const PORT = +process.env.PORT || 3000;
const SH = +process.env.SH || 120;            // 근무 시간(초)
const TS = +process.env.TIMESCALE || 1;       // 테스트용 시간 배속
const NROOMS = 4, MAXP = 8;
const MAXIP = +process.env.MAXIP || 4;        // 같은 IP 동시 접속 한도
const MAXMSG = 2048;

const R = (a, b) => a + Math.random() * (b - a);
const pick = a => a[Math.floor(Math.random() * a.length)];
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const r2 = v => Math.round(v * 100) / 100;
const BX = i => -7 + i * 2, SZ = -2;
const TVZ = { x: 6.7, z: .5, r: 1.0 }, RZ = { x: -6.7, z: 3.4, r: .9 };
const ADJ = ['졸린', '배고픈', '용감한', '조용한', '눈치빠른', '든든한', '말년', '깐깐한', '씩씩한', '느긋한'];
const RANK = ['이병', '일병', '상병', '병장'];

/* ───────── WebSocket (RFC 6455 최소 구현) ───────── */
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
function frame(op, buf) {
  const n = buf.length; let h;
  if (n < 126) h = Buffer.from([0x80 | op, n]);
  else if (n < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 126; h.writeUInt16BE(n, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2); }
  return Buffer.concat([h, buf]);
}
class Conn {
  constructor(sock) {
    this.sock = sock; this.buf = Buffer.alloc(0); this.frag = []; this.fragLen = 0; this.dead = false;
    this.onmsg = null; this.onclose = null;
    sock.setNoDelay(true);
    sock.on('data', d => this.data(d));
    sock.on('close', () => this.closed());
    sock.on('error', () => this.close(1006));
  }
  data(d) {
    if (this.dead) return;
    this.buf = Buffer.concat([this.buf, d]);
    if (this.buf.length > MAXMSG * 4) return this.close(1009);
    for (;;) {
      if (this.buf.length < 2) return;
      const b0 = this.buf[0], b1 = this.buf[1], fin = !!(b0 & 0x80), op = b0 & 15, masked = !!(b1 & 0x80);
      let len = b1 & 127, off = 2;
      if (len === 126) { if (this.buf.length < 4) return; len = this.buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (this.buf.length < 10) return; const L = this.buf.readBigUInt64BE(2); if (L > 65536n) return this.close(1009); len = Number(L); off = 10; }
      if (!masked) return this.close(1002);
      if (len > MAXMSG) return this.close(1009);
      if (this.buf.length < off + 4 + len) return;
      const mask = this.buf.subarray(off, off + 4), p = Buffer.from(this.buf.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) p[i] ^= mask[i & 3];
      this.buf = this.buf.subarray(off + 4 + len);
      if (op === 8) return this.close(1000);
      if (op === 9) { this.raw(frame(10, p)); continue; }
      if (op === 10) continue;
      if (op === 1 || op === 0) {
        this.frag.push(p); this.fragLen += p.length;
        if (this.fragLen > MAXMSG) return this.close(1009);
        if (fin) { const s = Buffer.concat(this.frag).toString('utf8'); this.frag = []; this.fragLen = 0; if (this.onmsg) this.onmsg(s); }
      }
    }
  }
  raw(b) { if (this.dead) return; if (this.sock.writableLength > 1 << 20) return this.close(1013); this.sock.write(b); }
  sendStr(s) { this.raw(frame(1, Buffer.from(s))); }
  send(o) { this.sendStr(JSON.stringify(o)); }
  ping() { this.raw(frame(9, Buffer.alloc(0))); }
  close(code = 1000) {
    if (this.dead) return;
    try { const b = Buffer.alloc(2); b.writeUInt16BE(code); this.sock.write(frame(8, b)); this.sock.end(); } catch (e) {}
    this.closed(); setTimeout(() => { try { this.sock.destroy(); } catch (e) {} }, 500);
  }
  closed() { if (this.dead) return; this.dead = true; if (this.onclose) this.onclose(); }
}

/* ───────── 방 ───────── */
class Room {
  constructor(id) { this.id = id; this.hum = new Set(); this.init(); }
  init() {
    this.T = 0; this.tv = { on: false, next: 25, at: 0 };
    this.ofc = { st: 'off', x: 0, z: 0, tx: 0, tz: 0 };
    this.beam = null; this.nBeam = 20; this.alarm = -1; this.npcRamen = false; this.nShow = 0;
    this.ev = { type: null, next: 0, who: null, t0: 0, st: 0, caught: false, sl: 0, on: false };
    this.slots = [...Array(8)].map((_, i) => ({
      i, h: null, name: '', st: 'sleep', x: BX(i), z: -3.6, tx: BX(i), tz: -3.6, fy: 0, end: 0, nt: 0, busy: false,
      sal: 0, fl: 0, tgt: -1, hoT: 0, jT: 0, lp: 0, lastPour: 0, lastWrong: 0, rm: this.newRm()
    }));
    const s0 = this.slots[0], s1 = this.slots[1];
    s0.st = 'guard'; s0.z = SZ; s0.tz = SZ; s0.end = SH;
    s1.st = 'guard'; s1.x = -1; s1.z = 1.5; s1.tx = -1; s1.tz = 1.5; s1.end = SH * .5;
    this.queue = [2, 3, 4, 5, 6, 7];
  }
  newRm() { return { st: 'none', p: 0, t: 0, next: 0, slp: 0, hint: false }; }
  get n() { return this.hum.size; }
  bcast(o) { const s = JSON.stringify(o); for (const h of this.hum) h.conn.sendStr(s); }
  toSlot(s, o) { if (s.h) s.h.conn.send(o); }
  toast(m, ms = 3800) { this.bcast({ t: 'toast', m, ms }); }
  toastG(m, ms = 3800) { for (const h of this.hum) { const st = h.slot.st; if (st === 'guard' || st === 'handover') h.conn.send({ t: 'toast', m, ms }); } }
  fx(k, i) { this.bcast({ t: 'fx', k, i }); }
  lightsOn(m, snd) { this.alarm = this.T + 9; this.bcast({ t: 'alarm', m, snd: snd || 'buzz' }); }

  nameFor() {
    const used = new Set([...this.hum].map(h => h.name));
    for (let k = 0; k < 30; k++) { const n = pick(ADJ) + ' ' + pick(RANK); if (!used.has(n)) return n; }
    return pick(ADJ) + ' ' + pick(RANK) + ' ' + (1 + Math.floor(Math.random() * 99));
  }
  join(conn, ip) {
    if (this.n >= MAXP) return null;
    if (this.n === 0) this.init();
    const free = this.slots.filter(s => !s.h);
    const s = free.find(s => s.st === 'guard' && !s.busy)
      || this.queue.map(i => this.slots[i]).find(s => !s.h && s.st === 'sleep') || free[0];
    if (this.ev.who === s) this.endEv();
    const h = { conn, ip, slot: s, name: this.nameFor(), last: Date.now(), tok: 60, tokT: Date.now() };
    s.h = h; s.name = h.name; s.sal = 0; s.fl = 0; s.tgt = -1; s.rm = this.newRm(); s.jT = this.T; s.lp = Date.now(); s.busy = false;
    this.hum.add(h);
    conn.send({ t: 'welcome', slot: s.i, name: h.name, room: this.id, SH });
    conn.send(this.snap());
    this.toast(h.name + ' 입장', 2500);
    return h;
  }
  leave(h) {
    if (!this.hum.delete(h)) return;
    const s = h.slot; s.h = null; s.name = ''; s.sal = 0; s.fl = 0; s.rm = this.newRm(); s.tgt = -1;
    if (s.st === 'handover') { s.st = 'guard'; s.end = Math.min(s.end, this.T); }
    else if (s.st === 'journal') { s.st = 'walkbed'; s.tx = BX(s.i); s.tz = -3.6; }
    if (this.n) this.toast(h.name + ' 퇴장', 2500);
  }

  /* 상태 흐름 */
  wake(n) { n.st = 'guard'; n.x = BX(n.i); n.z = SZ; n.tx = n.x; n.tz = SZ; n.end = this.T + SH; n.nt = this.T + 1; n.busy = false; n.rm = n.h ? this.newRm() : n.rm; if (n.h) n.jT = this.T; }
  relieve(g, t) {
    let idx = t ? this.queue.indexOf(t.i) : 0; if (idx < 0) idx = 0;
    const ni = this.queue.splice(idx, 1)[0]; this.wake(this.slots[ni]); this.queue.push(g.i);
    if (g.h) { g.st = 'journal'; g.tgt = -1; } else { g.st = 'walkbed'; g.tx = BX(g.i); g.tz = -3.6; }
  }
  pickTgt(s) { const c = this.queue.filter(i => this.slots[i].st === 'sleep'); s.tgt = pick(c.length ? c : this.queue); }
  moveToward(p, dt, sp) {
    const dx = p.tx - p.x, dz = p.tz - p.z, d = Math.hypot(dx, dz);
    if (d < .05) return true;
    const s = Math.min(d, sp * dt); p.x += dx / d * s; p.z += dz / d * s; p.fy = Math.atan2(dx, dz); return false;
  }
  tvOff() { this.tv.on = false; this.tv.next = this.T + R(25, 50); }

  tick(dt) {
    const T = this.T += dt;
    this.tickTV(dt); this.tickEv(); this.tickHumans(dt); this.tickNpcs(dt);
    if (T > this.nBeam) { this.beam = T; this.nBeam = T + R(45, 80); this.toastG('반대편에서 당직사관 손전등이 비춘다.', 3000); }
    if (this.beam !== null && T - this.beam > 6) this.beam = null;
  }
  tickTV(dt) {
    const T = this.T, tv = this.tv, o = this.ofc;
    const g = [...this.hum].some(h => h.slot.st === 'guard' || h.slot.st === 'handover');
    if (!tv.on && o.st === 'off' && g && T > tv.next) { tv.on = true; tv.at = T; this.toastG('생활관 TV가 켜졌다. 당직사관이 오기 전에 TV 앞 빛나는 자리에서 꺼야 한다. (F)', 4500); }
    if (tv.on && o.st === 'off' && T - tv.at > 3) { o.st = 'in'; o.x = -7.8; o.z = 4.6; o.tx = 6.6; o.tz = .5; this.toastG('복도 끝에서 발소리가 들린다…', 3000); }
    if (o.st !== 'off') {
      const dx = o.tx - o.x, dz = o.tz - o.z, d = Math.hypot(dx, dz);
      if (d < .1) {
        if (o.st === 'in') {
          this.bcast({ t: 'shout', m: '“야!! TV 누가 켰어!!”' });
          this.lightsOn('당직사관에게 걸렸다. 불이 모두 켜지고 전원 기상한다!', 'ya');
          this.tvOff(); o.st = 'out'; o.tx = -7.8; o.tz = 4.6;
        } else o.st = 'off';
      } else { const s = Math.min(d, 1.5 * dt); o.x += dx / d * s; o.z += dz / d * s; }
    }
  }
  endEv() { const e = this.ev; if (e.who) e.who.busy = false; e.type = null; e.who = null; this.npcRamen = false; e.next = this.T + R(40, 90); }
  tickEv() {
    const e = this.ev, T = this.T, tv = this.tv, o = this.ofc;
    if (!e.on) { e.on = true; e.next = T + R(15, 30); }
    if (!e.type) {
      if (T < e.next) return;
      const gs = this.slots.filter(s => !s.h && s.st === 'guard');
      if (!gs.length || tv.on || o.st !== 'off' || this.beam !== null) { e.next = T + 10; return; }
      e.who = pick(gs); e.type = Math.random() < .5 ? 'tv' : 'ramen'; e.st = 0; e.who.busy = true;
      const d = e.type === 'tv' ? TVZ : RZ; e.who.tx = d.x; e.who.tz = d.z; e.caught = Math.random() < .65; return;
    }
    const w = e.who;
    if (!w || w.st !== 'guard' || w.h) { this.endEv(); return; }
    if (e.st === 0) {
      if (Math.hypot(w.x - w.tx, w.z - w.tz) < .3) {
        e.st = 1; e.t0 = T;
        if (e.type === 'tv') { tv.on = true; tv.at = T; this.toast('TV 소리가 들린다…', 3000); }
        else { this.npcRamen = true; this.toast('어디선가 라면 냄새가 난다…', 3000); this.fx('water'); }
      }
      return;
    }
    if (e.st === 1) {
      const el = T - e.t0;
      if (e.type === 'tv') {
        if (!e.caught && el > 2.2) { this.tvOff(); if (o.st === 'in') { o.st = 'out'; o.tx = -7.8; o.tz = 4.6; } this.toast((w.i + 1) + '번이 재빨리 TV를 껐다.', 3000); this.endEv(); }
        else if (e.caught && !tv.on) this.endEv();
      } else {
        if (T > e.sl) { this.fx('slurp'); e.sl = T + 1; }
        if (el > 3) {
          if (e.caught) { this.beam = T; this.nBeam = T + R(45, 80); e.st = 2; e.t0 = T; }
          else { this.toast((w.i + 1) + '번이 컵라면을 몰래 다 먹었다.', 3000); this.endEv(); }
        }
      }
      return;
    }
    if (e.st === 2 && T - e.t0 > .8) {
      this.bcast({ t: 'shout', m: '“야!! 거기 뭐 먹어!!”' });
      this.lightsOn((w.i + 1) + '번이 컵라면을 먹다 들켰다! 불이 모두 켜지고 전원 기상한다!');
      this.endEv();
    }
  }
  tickRamen(s, dt) {
    const r = s.rm, T = this.T, inR = Math.hypot(s.x - RZ.x, s.z - RZ.z) < RZ.r, COOK = SH < 60 ? 6 : 20, EAT = 3;
    if (!r.hint && T - s.jT > 12) { r.hint = true; this.toSlot(s, { t: 'toast', m: '구석 선반에 컵라면이 있다… 몰래 끓여 먹어 볼까?', ms: 4500 }); }
    if (r.st === 'none') {
      r.p = inR ? r.p + dt / 1.2 : Math.max(0, r.p - dt);
      if (r.p >= 1) { r.st = 'cook'; r.t = T; r.p = 0; this.fx('water'); this.toSlot(s, { t: 'toast', m: '컵라면에 물을 부었다. 익을 때까지 기다리자.', ms: 3500 }); }
    } else if (r.st === 'cook') {
      if (T - r.t >= COOK) { r.st = 'ready'; this.toSlot(s, { t: 'toast', m: '라면이 다 익었다! 선반 앞에서 먹자. 창밖 손전등 조심.', ms: 4500 }); }
    } else if (r.st === 'ready') {
      const th = this.beam !== null ? -Math.PI / 2 + (T - this.beam) / 6 * Math.PI : null;
      const near = th !== null && Math.abs(th - Math.atan2(RZ.x, 6.3 - RZ.z)) < .3;
      if (inR) {
        if (near && r.p > .02) { r.st = 'cool'; r.p = 0; r.next = T + R(30, 50); this.lightsOn(s.name + '이(가) 컵라면을 먹다 손전등에 들켰다! 불이 모두 켜지고 전원 기상한다!'); }
        else if (!near) { r.p += dt / EAT; if (T > r.slp) { this.fx('slurp'); r.slp = T + 1; } }
      } else r.p = Math.max(0, r.p - dt * .5);
      if (r.p >= 1) { r.st = 'cool'; r.p = 0; r.next = T + R(40, 70); this.toSlot(s, { t: 'toast', m: '몰래 컵라면을 다 먹었다. 흔적 없음.', ms: 4000 }); }
    } else if (T > r.next) r.st = 'none';
  }
  tickHumans(dt) {
    const T = this.T;
    for (const h of this.hum) {
      const s = h.slot;
      if (s.st === 'guard') { this.tickRamen(s, dt); if (T >= s.end) { s.st = 'handover'; s.hoT = T; this.pickTgt(s); } }
      else if (s.st === 'handover') {
        if (s.tgt < 0 || !this.queue.includes(s.tgt) || this.slots[s.tgt].st !== 'sleep') this.pickTgt(s);
        if (T - s.hoT > 60) { this.toSlot(s, { t: 'toast', m: '시간이 지나 교대가 자동으로 이루어졌다.', ms: 3500 }); this.relieve(s, this.slots[s.tgt]); }
      }
    }
  }
  tickNpcs(dt) {
    const T = this.T;
    for (const p of this.slots) {
      if (p.h) continue;
      if (p.st === 'guard') {
        if (T > p.nt && !p.busy) {
          const r = Math.random(), sl = this.queue.filter(q => this.slots[q].st === 'sleep');
          if (r < .3) { p.tx = -4.5; p.tz = SZ; } else if (r < .6) { p.tx = 4.5; p.tz = SZ; }
          else if (r < .8 && sl.length) { p.tx = BX(pick(sl)); p.tz = SZ; } else { p.tx = R(-7, 7); p.tz = R(-1.8, 4); }
          p.nt = T + R(3, 6);
        }
        this.moveToward(p, dt, 1.8);
        if (T >= p.end) this.relieve(p);
      } else if (p.st === 'walkbed' && this.moveToward(p, dt, 2.4)) { p.st = 'sleep'; p.x = BX(p.i); p.z = -3.6; }
    }
  }

  /* 클라이언트 메시지 */
  msg(h, m) {
    const s = h.slot, T = this.T, now = Date.now();
    switch (m.t) {
      case 'pos': {
        if (s.st === 'sleep') break;
        const x = +m.x, z = +m.z, fy = +m.fy;
        if (!Number.isFinite(x) || !Number.isFinite(z) || !Number.isFinite(fy)) break;
        const cx = clamp(x, -7.5, 7.5), cz = clamp(z, -3.7, 4.2);
        const dtp = Math.min(1, (now - s.lp) / 1000), maxd = 6 * dtp + .4, dx = cx - s.x, dz = cz - s.z, d = Math.hypot(dx, dz);
        if (d > maxd) { s.x += dx / d * maxd; s.z += dz / d * maxd; } else { s.x = cx; s.z = cz; }
        s.lp = now; s.fy = fy; s.sal = m.sal ? 1 : 0; s.fl = m.fl ? 1 : 0; break;
      }
      case 'pour': if (now - s.lastPour > 1100 && (s.st === 'guard' || s.st === 'handover')) { s.lastPour = now; this.fx('pour', s.i); } break;
      case 'tvoff':
        if (!this.tv.on || (s.st !== 'guard' && s.st !== 'handover')) break;
        if (Math.hypot(s.x - TVZ.x, s.z - TVZ.z) > TVZ.r + .35) { this.toSlot(s, { t: 'toast', m: 'TV 바로 앞 빛나는 자리에서만 끌 수 있다.', ms: 2000 }); break; }
        this.tvOff(); if (this.ofc.st === 'in') { this.ofc.st = 'out'; this.ofc.tx = -7.8; this.ofc.tz = 4.6; }
        this.toast(s.name + '이(가) TV를 껐다.', 2500); break;
      case 'wake': {
        const i = m.i | 0;
        if (s.st !== 'handover' || i < 0 || i > 7 || !this.queue.includes(i)) break;
        const ts = this.slots[i];
        if (ts.st !== 'sleep' || Math.hypot(s.x - BX(i), s.z - SZ) > 1.3) break;
        if (i === s.tgt) this.relieve(s, ts);
        else if (now - s.lastWrong > 1500) {
          s.lastWrong = now;
          this.toSlot(s, { t: 'toast', m: '“야, 나 아닌데?” ' + (i + 1) + '번을 잘못 깨웠다. 명령은 ' + (s.tgt + 1) + '번이다.', ms: 4500 });
          this.bcast({ t: 'bubble', i, x: '…누구야…' });
        }
        break;
      }
      case 'tobed': if (s.st === 'journal') { s.st = 'walkbed'; s.tx = BX(s.i); s.tz = -3.6; } break;
      case 'inbed': if (s.st === 'walkbed' && Math.hypot(s.x - BX(s.i), s.z - -3.6) < 1.2) { s.st = 'sleep'; s.x = BX(s.i); s.z = -3.6; s.sal = 0; s.fl = 0; } break;
    }
  }

  snap() {
    const T = this.T, o = this.ofc;
    const rv = this.npcRamen || [...this.hum].some(h => h.slot.rm.st === 'cook' || h.slot.rm.st === 'ready');
    return {
      t: 's', T: r2(T), tv: this.tv.on ? 1 : 0, o: o.st === 'off' ? 0 : [r2(o.x), r2(o.z)], b: this.beam === null ? null : r2(this.beam),
      al: r2(Math.max(0, this.alarm - T)), rv: rv ? 1 : 0, q: this.queue, n: this.n,
      p: this.slots.map(s => ({ i: s.i, h: s.h ? 1 : 0, nm: s.name, st: s.st, x: r2(s.x), z: r2(s.z), fy: r2(s.fy), sa: s.sal, fl: s.fl, e: r2(s.end), tg: s.tgt, rs: s.rm.st, rp: r2(s.rm.p) }))
    };
  }
}
const rooms = [...Array(NROOMS)].map((_, i) => new Room(i + 1));

/* ───────── HTTP ───────── */
let INDEX = null;
function loadIndex() { INDEX = fs.readFileSync(path.join(__dirname, 'public', 'index.html')); }
loadIndex();
const ipCount = new Map();
const ipOf = req => String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();

const server = http.createServer((req, res) => {
  const u = new URL(req.url, 'http://x');
  const hdr = { 'X-Content-Type-Options': 'nosniff', 'Referrer-Policy': 'no-referrer' };
  if (u.pathname === '/api/rooms') {
    res.writeHead(200, { ...hdr, 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify(rooms.map(r => ({ id: r.id, n: r.n, max: MAXP }))));
  } else if (u.pathname === '/healthz') { res.writeHead(200, hdr); res.end('ok'); }
  else if (u.pathname === '/' || u.pathname === '/index.html') {
    res.writeHead(200, { ...hdr, 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }); res.end(INDEX);
  } else { res.writeHead(404, hdr); res.end('not found'); }
});
server.on('upgrade', (req, sock) => {
  const fail = (code, msg) => { try { sock.write('HTTP/1.1 ' + code + ' ' + msg + '\r\nConnection: close\r\n\r\n'); } catch (e) {} sock.destroy(); };
  const u = new URL(req.url, 'http://x');
  if (u.pathname !== '/ws') return fail(404, 'Not Found');
  const key = req.headers['sec-websocket-key'];
  if (!key || String(req.headers.upgrade).toLowerCase() !== 'websocket' || req.headers['sec-websocket-version'] !== '13') return fail(400, 'Bad Request');
  const origin = req.headers.origin;
  if (origin && !process.env.ALLOW_ANY_ORIGIN) { let ok = false; try { ok = new URL(origin).host === req.headers.host; } catch (e) {} if (!ok) return fail(403, 'Forbidden'); }
  const room = rooms[(+u.searchParams.get('room') || 0) - 1];
  if (!room) return fail(404, 'No Room');
  const ip = ipOf(req);
  if ((ipCount.get(ip) || 0) >= MAXIP) return fail(429, 'Too Many Connections');
  if (room.n >= MAXP) return fail(409, 'Room Full');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' +
    crypto.createHash('sha1').update(key + GUID).digest('base64') + '\r\n\r\n');
  const conn = new Conn(sock);
  ipCount.set(ip, (ipCount.get(ip) || 0) + 1);
  const h = room.join(conn, ip);
  if (!h) { conn.close(1013); ipCount.set(ip, Math.max(0, ipCount.get(ip) - 1)); return; }
  conn.onmsg = s => {
    const now = Date.now(); h.tok = Math.min(60, h.tok + (now - h.tokT) / 1000 * 30); h.tokT = now;
    if (--h.tok < 0) return conn.close(1008);
    h.last = now;
    let m; try { m = JSON.parse(s); } catch (e) { return; }
    if (m && typeof m === 'object' && typeof m.t === 'string') room.msg(h, m);
  };
  conn.onclose = () => { room.leave(h); const c = (ipCount.get(ip) || 1) - 1; if (c <= 0) ipCount.delete(ip); else ipCount.set(ip, c); };
});

/* ───────── 메인 루프 ───────── */
let last = Date.now(), tickN = 0;
setInterval(() => {
  const now = Date.now(), dt = Math.min(.25, (now - last) / 1000) * TS; last = now; tickN++;
  for (const r of rooms) {
    if (!r.n) continue;
    r.tick(dt);
    if (tickN % 2 === 0) { const s = JSON.stringify(r.snap()); for (const h of r.hum) h.conn.sendStr(s); }
    for (const h of [...r.hum]) if (now - h.last > 45000) h.conn.close(4002);
  }
  if (tickN % 400 === 0) for (const r of rooms) for (const h of r.hum) h.conn.ping();
}, 50);

server.listen(PORT, () => console.log('불침번 서버 실행: http://localhost:' + PORT + '  (방 ' + NROOMS + '개 × ' + MAXP + '명, 근무 ' + SH + '초)'));
process.on('uncaughtException', e => console.error('uncaught', e));
process.on('unhandledRejection', e => console.error('unhandled', e));
process.on('SIGTERM', () => { for (const r of rooms) for (const h of r.hum) h.conn.close(1001); setTimeout(() => process.exit(0), 300); });
module.exports = { server, rooms };
