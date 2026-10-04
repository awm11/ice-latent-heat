import React, { useState, useEffect, useRef } from 'react';
import BuyMeCoffeeButton from './BuyMeCoffee.jsx';
import './styles.css';

// ===== Simulation (plain JS) =====
const W = 900, H = 540;
const X0 = 250, X1 = 520, TOP = 220, BOT = 462, BENCH = 466;
const SB = { x0: 620, x1: 740, top: 382, bot: 462 };
const M = 0.45;           // fraction of the ice (by mass) that melts before the new balance
const FP_SALT = -21.1;    // freezing point with the maximum amount of salt stirred in
const TH = { x: 290, y: 372, a: -0.2, len: 262 };
const MAX_SCOOPS = 6;     // six scoops reach the lowest possible freezing point
const SLOW = 0.25;        // overall melting pace at 1x
// Energy units: water+ice starts with KE 75 + PE 25 = 100.
const KW = 50 / 21.1;     // water+ice kinetic energy per degree
const LW = 50 / M;        // water+ice potential energy gained per unit of ice melted
// Ice cream mix: about a fifth of the mass of the ice, starts at 5 degC, freezes at about -3 degC
const CC = 0.5;           // ice cream kinetic energy per degree
const LC = 12;            // ice cream potential energy lost on freezing completely
const FPC = -3;           // freezing point of the ice cream mix
const T_ICE0 = -2;        // starting temperature of the ice
const H_EX = 0.08;        // how quickly energy flows from the bag into the ice
const ROOM_T = 20;        // room temperature, only relevant once insulation is off
const LEAK = 0.03;        // how quickly energy leaks in from the room when uninsulated
const BAG = { hw: 42, hh: 25 };
const N_ICE = 500;
const rand = (a, b) => a + Math.random() * (b - a);
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const uOf = T => 40 + (clamp(T, -30, 10) + 30) * 5;
function thermoPt(u, off) {
  off = off || 0;
  const s = Math.sin(TH.a), c = Math.cos(TH.a);
  return [TH.x + u * s + off * c, TH.y - u * c + off * s];
}
function fmtT(v) {
  const r = Math.round(v * 10) / 10;
  return (r < 0 ? '\u2212' : '') + Math.abs(r).toFixed(1) + ' \u00B0C';
}
const SALT_COLS = ['#fffcee', '#fcf8e4', '#fefaea', '#f9f4dc'];

function makeShard(x, y, i) {
  const r = rand(4.5, 8.2);
  const n = 4 + Math.floor(Math.random() * 3);
  const a0 = Math.random() * Math.PI * 2, el = rand(1.0, 1.45);
  const verts = [];
  for (let j = 0; j < n; j++) {
    const a = a0 + (j * 2 * Math.PI) / n + rand(-0.35, 0.35);
    const rr = rand(0.75, 1.15);
    verts.push([Math.cos(a) * rr * el, Math.sin(a) * rr]);
  }
  const l = Math.floor(rand(234, 251));
  return {
    i, x, y, px: x, py: y, r, verts, back: Math.random() < 0.2, rot: rand(0, 6.28), scale: 1, s: 0, d: 1,
    fill: `rgba(${l - 13},${l - 4},255,0.93)`,
    edge: `rgba(${Math.floor(rand(105, 140))},${Math.floor(rand(160, 185))},${Math.floor(rand(215, 235))},0.9)`
  };
}
function makeHeap() {
  const g = [], cx = (SB.x0 + SB.x1) / 2, hw = (SB.x1 - SB.x0) / 2 - 7;
  for (let k = 0; k < 520; k++) {
    const x = rand(SB.x0 + 7, SB.x1 - 7);
    const t = (x - cx) / hw;
    const hmax = 46 * (1 - 0.55 * t * t);
    g.push({ x, y: SB.bot - 2 - rand(0, hmax), c: SALT_COLS[k % 4], sh: Math.random() < 0.3 });
  }
  g.sort((a, b) => b.y - a.y);
  return g;
}

class Sim {
  constructor() { this.heap = makeHeap(); this.reset(); }
  reset() {
    this.ice = []; this.salt = []; this.m = 0; this.fp = 0; this.Uw = 100 + KW * T_ICE0; this.bag = null;
    this.saltAdded = false; this.saltStirred = false; this.stirredNoSalt = false;
    this.simT = 0; this.nextSample = 0; this.hist = []; this.events = [];
    this.scoopsIn = 0; this.scoopsStirred = 0;
    this.stir = null; this.pinches = MAX_SCOOPS; this.drag = null; this.hover = false; this.time = 0;
    this.insulated = true;
    let i = 0, row = 0;
    while (i < N_ICE) {
      const off = (row % 2) * 7;
      for (let x = X0 + 8 + off; x < X1 - 8 && i < N_ICE; x += 14) {
        this.ice.push(makeShard(x + rand(-2, 2), BOT - 8 - row * 12.5 + rand(-2, 2), i)); i++;
      }
      row++;
    }
    for (const p of this.ice) { p.d = rand(0.06, 0.18); p.s = rand(0, 1 - p.d); }
    this.iceArea = this.ice.reduce((a, p) => a + Math.PI * p.r * p.r * 0.8, 0);
    this.pileTop = TOP; this.pileBot = BOT;
    for (let k = 0; k < 400; k++) this.physics();
    for (const p of this.ice) { p.px = p.x; p.py = p.y; }
    this.bounds();
  }
  fpTarget() { return FP_SALT * this.scoopsStirred / MAX_SCOOPS; }
  peW() { return 25 + LW * this.m; }
  keW() { return this.Uw - this.peW(); }
  T() { return (this.keW() - 75) / KW; }
  // ice cream: enthalpy-style bookkeeping (kinetic part + potential part)
  creamState() {
    const H = this.bag.H, h0 = CC * (FPC + 21.1);
    if (H >= h0 + LC) return { T: (H - LC) / CC - 21.1, liq: 1 };
    if (H >= h0) return { T: FPC, liq: (H - h0) / LC };
    return { T: H / CC - 21.1, liq: 0 };
  }
  addCream() {
    if (this.bag) return;
    this.events.push({ t: this.simT, label: 'Ice cream in' });
    // bury the bag in the top third of the ice, with a layer of shards over it
    const cx = (X0 + X1) / 2 + 12;
    const y = clamp(this.pileTop + 16 + BAG.hh, TOP + BAG.hh + 10, BOT - BAG.hh - 2);
    this.bag = { x: cx, y, py: y, placing: false, boost: 1, H: CC * (5 + 21.1) + LC };
    // shards where the bag now sits are moved onto the top of the pile
    const moved = this.ice.filter(p => p.scale > 0.03 && Math.abs(p.x - cx) < BAG.hw + p.r * 0.6 && Math.abs(p.y - y) < BAG.hh + p.r * 0.6);
    moved.forEach((p, k) => {
      p.x = rand(X0 + 8, X1 - 8); p.y = this.pileTop - 4 - (k % 3) * 9 - rand(0, 4);
      if (Math.abs(p.x - cx) < BAG.hw + 6) p.y = Math.min(p.y, y - BAG.hh - p.r);
      p.px = p.x; p.py = p.y;
    });
  }
  waterY() { return BOT - Math.min(this.m, 1) * this.iceArea * 0.92 / (X1 - X0); }
  bounds() {
    let t = BOT, b = TOP;
    for (const p of this.ice) { if (p.scale <= 0.03) continue; if (p.y < t) t = p.y; if (p.y > b) b = p.y; }
    this.pileTop = t; this.pileBot = Math.max(b, t + 10);
  }
  rodPos() {
    const idle = [498, 456, 521, 100];
    if (!this.stir) return idle;
    const st = this.stir, t = st.t;
    const tx = (X0 + X1) / 2 + 100 * Math.sin(t * 2 * Math.PI * 0.9);
    const ty = clamp((this.pileTop + this.pileBot) / 2 + 45 * Math.sin(t * 2 * Math.PI * 0.45 + 1), TOP + 40, BOT - 14);
    const act = [tx, ty, tx + 22, ty - 300];
    const k = Math.min(1, t / 0.35, (st.dur - t) / 0.35);
    const e = k * k * (3 - 2 * k);
    return idle.map((v, j) => v + (act[j] - v) * e);
  }
  physics() {
    const G = 0.22, wy = this.waterY(), st = this.stir;
    const rod = st ? this.rodPos() : null;
    const bag = this.bag;
    if (bag) {
      if (bag.placing) {
        bag.y = Math.min(bag.ty, bag.y + 2.2); bag.py = bag.y;
        if (bag.y >= bag.ty) bag.placing = false;
      } else {
        // keep the bag pushed down below the surface of the ice beside it
        bag.press = false;
        if (st) {
          // while stirring, the bag is held where it is: the churned ice can't lift it out
          if (bag.holdY === undefined) bag.holdY = bag.py;
          bag.y = bag.py = bag.holdY; bag.press = true;
        } else {
          bag.holdY = undefined;
          const side = this.ice.filter(p => p.scale > 0.03 && Math.abs(p.x - bag.x) > BAG.hw + 6).map(p => p.y).sort((a, b) => a - b);
          if (side.length > 12) {
            const target = Math.min(side[12] + 8 + BAG.hh, BOT - BAG.hh);
            // the bag is held at this depth: it moves gently towards it, and the shards make way
            bag.y += clamp(target - bag.y, -0.6, 1.2); bag.py = bag.y; bag.press = true;
          }
        }
      }
    }
    for (const p of this.ice) {
      if (p.scale <= 0.03) continue;
      let vx = (p.x - p.px) * 0.95, vy = (p.y - p.py) * 0.95;
      const sub = p.y > wy + p.r * 0.3;
      if (sub) { vx *= 0.9; vy *= 0.9; }
      if (st && vy < 0) vy *= 0.6;          // while stirring, shards flung upwards lose their lift quickly
      vx = clamp(vx, -4, 4); vy = clamp(vy, -4, 4);
      p.px = p.x; p.py = p.y;
      p.x += vx; p.y += vy + (sub ? -0.3 : G);
      p.rot += vx * 0.025;
      if (st) {
        // jostle without adding lasting velocity (shift the previous position too)
        const jx = 0.5 * Math.sin(st.t * 7.5 + p.y * 0.05); p.x += jx; p.px += jx;
        if (Math.random() < 0.02) { const jy = rand(0, 3); p.y -= jy; p.py -= jy; }
      }
    }
    for (let it = 0; it < 4; it++) {
      const grid = new Map();
      for (const p of this.ice) {
        if (p.scale <= 0.03) continue;
        const k = ((p.x / 18) | 0) + ((Math.max(0, p.y) / 18) | 0) * 64;
        let a = grid.get(k); if (!a) { a = []; grid.set(k, a); } a.push(p);
      }
      for (const p of this.ice) {
        if (p.scale <= 0.03) continue;
        const cx = (p.x / 18) | 0, cy = (Math.max(0, p.y) / 18) | 0, rp = p.r * p.scale * 0.92;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
          const a = grid.get(cx + dx + (cy + dy) * 64); if (!a) continue;
          for (const q of a) {
            if (q.i <= p.i) continue;
            const rq = q.r * q.scale * 0.92;
            const ex = q.x - p.x, ey = q.y - p.y, d2 = ex * ex + ey * ey, mn = rp + rq;
            if (d2 < mn * mn) {
              const d = Math.sqrt(d2) || 0.01, o = (mn - d) / d * 0.5;
              p.x -= ex * o; p.y -= ey * o; q.x += ex * o; q.y += ey * o;
            }
          }
        }
      }
      if (rod) {
        const [ax, ay, bx, by] = rod, sx = bx - ax, sy = by - ay, sl = sx * sx + sy * sy;
        for (const p of this.ice) {
          if (p.scale <= 0.03 || p.back) continue;
          const t = clamp(((p.x - ax) * sx + (p.y - ay) * sy) / sl, 0, 1);
          const cx = ax + sx * t, cy = ay + sy * t, ex = p.x - cx, ey = p.y - cy;
          const d = Math.sqrt(ex * ex + ey * ey) || 0.01, mn = p.r * p.scale * 0.92 + 5;
          if (d < mn) { p.x = cx + ex / d * mn; p.y = cy + ey / d * mn; }
        }
      }
      const bag = this.bag;
      if (bag) {
        for (const p of this.ice) {
          if (p.scale <= 0.03) continue;
          const rp = p.r * p.scale * 0.92, dx = p.x - bag.x, dy = p.y - bag.y;
          const ox = BAG.hw + rp - Math.abs(dx), oy = BAG.hh + rp - Math.abs(dy);
          if (ox <= 0 || oy <= 0) continue;
          if (ox * 0.7 < oy) { p.x += Math.sign(dx || 1) * ox; }
          else if (bag.placing || dy < 0) {
            // shard above the bag rests on it; the bag carries the load (or is being pushed in)
            const sy = Math.sign(dy || -1);
            if (bag.placing || bag.press) p.y += sy * oy; else { p.y += sy * oy * 0.95; bag.y -= sy * oy * 0.05; }
          } else if (bag.press) { p.y += oy; } else { p.y += oy * 0.95; bag.y -= oy * 0.05; }
        }
        if (bag.holdY !== undefined) bag.y = bag.holdY;
        if (bag.y > BOT - BAG.hh) bag.y = BOT - BAG.hh;
      }
      for (const p of this.ice) {
        if (p.scale <= 0.03) continue;
        const rp = p.r * p.scale * 0.92;
        if (p.x < X0 + rp) p.x = X0 + rp;
        if (p.x > X1 - rp) p.x = X1 - rp;
        if (p.y > BOT - rp) p.y = BOT - rp;
        if (p.y < TOP - 6 + rp) p.y = TOP - 6 + rp;
      }
    }
  }
  addScoop(x, y) {
    if (this.pinches <= 0) return;
    this.pinches--; this.saltAdded = true; this.scoopsIn++;
    const y0 = clamp(Math.min(y, this.pileTop - 12), TOP - 60, BOT - 10);
    for (let k = 0; k < 70; k++) {
      const gx = clamp(x + rand(-24, 24), X0 + 3, X1 - 3), gy = y0 + rand(-8, 8);
      this.salt.push({ x: gx, y: gy, px: gx + rand(-0.4, 0.4), py: gy - rand(0, 1), state: 'fall', sz: rand(2.2, 3.1), rot: rand(0, 1.5), dis: 0, dOff: rand(0, 0.3), age: 0, stirred: false, c: SALT_COLS[k % 4], tx: 0, ty: 0, host: -1, ox: 0, oy: 0 });
    }
  }
  startStir() {
    if (this.stir) return;
    // stirring moves cold slush against the bag: energy leaves it twice as fast from now on
    if (this.bag) this.bag.boost = 2;
    const withSalt = this.scoopsIn > this.scoopsStirred;
    this.stir = { t: 0, dur: 3.2, withSalt, counted: false };
    if (this.scoopsIn === 0) this.stirredNoSalt = true;
    for (const g of this.salt) if (g.state !== 'free') { g.state = 'stir'; this.retarget(g); }
  }
  retarget(g) { g.tx = rand(X0 + 6, X1 - 6); g.ty = clamp(rand(this.pileTop + 4, this.pileBot - 4), TOP + 14, BOT - 4); }
  endStir() {
    const alive = this.ice.filter(p => p.scale > 0.3);
    for (const g of this.salt) {
      if (g.state !== 'stir') continue;
      let best = null, bd = 1e9;
      for (const p of alive) { const d = (p.x - g.x) ** 2 + (p.y - g.y) ** 2; if (d < bd) { bd = d; best = p; } }
      if (!best) { g.state = 'free'; continue; }
      let ox = g.x - best.x, oy = g.y - best.y; const l = Math.hypot(ox, oy), lim = best.r * 0.9;
      if (l > lim) { ox *= lim / l; oy *= lim / l; }
      g.host = best.i; g.ox = ox; g.oy = oy; g.state = 'attached';
    }
  }
  updateSalt(dt, speed) {
    const wy = this.waterY();
    const settled = this.salt.filter(g => g.state === 'settled');
    for (const g of this.salt) {
      if (g.state === 'fall') {
        const vx = (g.x - g.px) * 0.9, vy = clamp(g.y - g.py, -5, 5) * 0.98;
        g.px = g.x; g.py = g.y; g.x = clamp(g.x + vx, X0 + 2, X1 - 2); g.y += vy + 0.25;
        if (g.y >= BOT - 2) { g.y = BOT - 2; g.state = 'settled'; continue; }
        if (g.y > wy) { g.state = 'free'; continue; }
        const bg = this.bag;
        if (bg && Math.abs(g.x - bg.x) < BAG.hw && g.y > bg.y - BAG.hh - 1 && g.y < bg.y) { g.y = bg.y - BAG.hh - 1; g.state = 'settled'; continue; }
        for (const p of this.ice) {
          if (p.scale <= 0.03) continue;
          const ex = g.x - p.x, ey = g.y - p.y, mn = p.r * p.scale * 0.92 + 1.4, d2 = ex * ex + ey * ey;
          if (d2 < mn * mn) { const d = Math.sqrt(d2) || 0.01; g.x = p.x + ex / d * mn; g.y = p.y + ey / d * mn; g.state = 'settled'; break; }
        }
        if (g.state === 'fall') for (const s of settled) {
          if (Math.abs(s.x - g.x) < 2.6 && s.y - g.y < 3 && s.y - g.y > -1) { g.y = s.y - 3; g.state = 'settled'; break; }
        }
      } else if (g.state === 'stir') {
        if (Math.random() < 0.03) this.retarget(g);
        g.x = clamp(g.x + (g.tx - g.x) * 0.06 + rand(-1.2, 1.2), X0 + 2, X1 - 2);
        g.y = clamp(g.y + (g.ty - g.y) * 0.06 + rand(-1.2, 1.2), TOP + 8, BOT - 2);
        g.rot += 0.05;
      } else if (g.state === 'attached') {
        const h = this.ice[g.host];
        if (h.scale < 0.2) { g.state = 'free'; }
        else { g.x = h.x + g.ox * h.scale; g.y = h.y + g.oy * h.scale; }
        if (g.stirred) { g.age += dt * speed * SLOW; g.dis = Math.max(g.dis, clamp(g.age * 0.08 - g.dOff, 0, 1)); }
      } else if (g.state === 'free') {
        g.y = Math.min(BOT - 2, g.y + 0.6); g.dis += 0.012;
      }
    }
    if (this.salt.some(g => g.dis >= 1)) this.salt = this.salt.filter(g => g.dis < 1);
  }
  update(dt, speed) {
    this.time += dt;
    if (this.stir) {
      this.stir.t += dt;
      if (this.stir.withSalt && !this.stir.counted && this.stir.t > 1.0) {
        this.stir.counted = true; this.saltStirred = true;
        this.events.push({ t: this.simT, label: this.scoopsStirred > 0 ? 'More salt' : 'Salt stirred in' });
        this.scoopsStirred = this.scoopsIn;
        for (const g of this.salt) g.stirred = true;
      }
      if (this.stir.t >= this.stir.dur) { this.stir = null; this.endStir(); }
    }
    const fpT = this.fpTarget();
    if (this.fp > fpT) {
      this.fp += (fpT - this.fp) * Math.min(1, dt * 3.5);
      if (this.fp - fpT < 0.02) this.fp = fpT;
    }
    // heat flows from the ice cream bag into the water and ice
    if (this.bag && !this.bag.placing) {
      const dT = this.creamState().T - this.T();
      const q = (Math.abs(dT) < 0.03 ? dT * 0.5 * CC : H_EX * this.bag.boost * dT * dt * speed * SLOW);
      this.bag.H -= q; this.Uw += q;
    }
    // with insulation off, energy leaks in from the room: an open system, not a closed one
    if (!this.insulated) {
      const q = LEAK * (ROOM_T - this.T()) * dt * speed * SLOW;
      this.Uw += q;
      // once the ice is at its freezing point, incoming heat melts it instead of warming it further.
      // Cap this frame's conversion to what the leaked heat itself could account for, so that a
      // freezing point which suddenly drops (salt going in while uninsulated) doesn't dump a whole
      // backlog of "excess" into the ice in one frame — any remaining gap is melted gradually by
      // the ordinary above-freezing-point pacing below instead.
      const keCap = 75 + KW * this.fp;
      if (q > 0 && this.m < 0.97 && this.keW() > keCap) {
        this.m += Math.min(0.97 - this.m, q / LW, (this.keW() - keCap) / LW);
      }
    }
    // ice melts whenever it is warmer than its freezing point: kinetic -> potential
    const above = this.T() - this.fp;
    if (above > 1e-6 && this.m < 0.97) {
      const need = above * KW / LW;
      this.m = Math.min(0.97, this.m + Math.min(need, dt * speed * SLOW * (0.05 * need / M + 0.003)));
    }
    for (const p of this.ice) p.scale = 1 - clamp((this.m - p.s) / p.d, 0, 1);
    // temperature-time record (time in simulated seconds)
    this.simT += dt * speed;
    if (this.simT >= this.nextSample) {
      this.nextSample = this.simT + 0.5;
      this.hist.push({ t: this.simT, T: this.T(), fp: this.fp, Tc: this.bag ? this.creamState().T : null });
      if (this.hist.length > 3000) this.hist = this.hist.filter((_, i) => i % 2 === 0);
    }
    this.physics();
    this.bounds();
    this.updateSalt(dt, speed);
  }
  snapshot() {
    const cs = this.bag ? this.creamState() : null;
    return {
      m: this.m, T: this.T(), fp: this.fp, ke: this.keW(), pe: this.peW(), hist: this.hist, events: this.events, simT: this.simT,
      cream: cs ? { boost: this.bag.boost > 1, T: cs.T, liq: cs.liq, ke: 7 + CC * (cs.T + 21.1), pe: 6 + LC * cs.liq } : null,
      saltAdded: this.saltAdded, saltStirred: this.saltStirred, stirredNoSalt: this.stirredNoSalt,
      stirring: !!this.stir, pinches: this.pinches, scoops: this.scoopsStirred, fpTarget: this.fpTarget(),
      unstirred: this.scoopsIn > this.scoopsStirred, insulated: this.insulated,
      done: this.saltStirred && Math.abs(this.fp - this.fpTarget()) < 0.05 && this.T() - this.fp < 0.05
    };
  }
}
// ===== Canvas drawing =====
const FONT = '"Atkinson Hyperlegible", "Segoe UI", system-ui, sans-serif';
function rr(ctx, x, y, w, h, r) {
  ctx.beginPath(); ctx.moveTo(x + r, y); ctx.lineTo(x + w - r, y); ctx.quadraticCurveTo(x + w, y, x + w, y + r);
  ctx.lineTo(x + w, y + h - r); ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h); ctx.lineTo(x + r, y + h);
  ctx.quadraticCurveTo(x, y + h, x, y + h - r); ctx.lineTo(x, y + r); ctx.quadraticCurveTo(x, y, x + r, y); ctx.closePath();
}
function beakerPath(ctx, x0, x1, top, bot, lip) {
  ctx.beginPath();
  ctx.moveTo(x0 - 4 - lip, top - 10 - lip * 0.5);
  ctx.lineTo(x0 - 4, top - 8);
  ctx.lineTo(x0 - 4, bot - 8); ctx.quadraticCurveTo(x0 - 4, bot + 4, x0 + 8, bot + 4);
  ctx.lineTo(x1 - 8, bot + 4); ctx.quadraticCurveTo(x1 + 4, bot + 4, x1 + 4, bot - 8);
  ctx.lineTo(x1 + 4, top - 8); ctx.lineTo(x1 + 8, top - 11);
}
function haloText(ctx, txt, x, y, col) {
  ctx.lineJoin = 'round'; ctx.strokeStyle = 'rgba(255,255,255,0.9)'; ctx.lineWidth = 3; ctx.strokeText(txt, x, y);
  ctx.fillStyle = col; ctx.fillText(txt, x, y);
}
let benchImg = null;
function makeBench(dpr) {
  const c = document.createElement('canvas'), bh = H - BENCH;
  c.width = W * dpr; c.height = bh * dpr;
  const b = c.getContext('2d'); b.scale(dpr, dpr);
  let seed = 7; const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647;
  // top surface (seen slightly from above)
  let g = b.createLinearGradient(0, 0, 0, 22);
  g.addColorStop(0, '#b98a57'); g.addColorStop(1, '#a8794a');
  b.fillStyle = g; b.fillRect(0, 0, W, 22);
  // front face
  g = b.createLinearGradient(0, 22, 0, bh);
  g.addColorStop(0, '#8a5a32'); g.addColorStop(1, '#6b4426');
  b.fillStyle = g; b.fillRect(0, 22, W, bh - 22);
  // grain on the top: long, gently wavy streaks
  for (let k = 0; k < 46; k++) {
    const y0 = rnd() * 22, amp = 0.4 + rnd() * 1.2, f = 0.004 + rnd() * 0.01, ph = rnd() * 6;
    b.strokeStyle = rnd() < 0.5 ? `rgba(110,70,35,${0.12 + rnd() * 0.18})` : `rgba(225,185,135,${0.1 + rnd() * 0.15})`;
    b.lineWidth = 0.5 + rnd() * 0.9; b.beginPath();
    const xs = rnd() * W * 0.6, xe = xs + 200 + rnd() * 500;
    for (let x = xs; x <= xe; x += 6) { const y = y0 + Math.sin(x * f + ph) * amp; x === xs ? b.moveTo(x, y) : b.lineTo(x, y); }
    b.stroke();
  }
  // grain on the front face
  for (let k = 0; k < 60; k++) {
    const y0 = 24 + rnd() * (bh - 26), amp = 0.6 + rnd() * 1.8, f = 0.003 + rnd() * 0.012, ph = rnd() * 6;
    b.strokeStyle = rnd() < 0.6 ? `rgba(60,35,15,${0.15 + rnd() * 0.2})` : `rgba(190,140,90,${0.08 + rnd() * 0.12})`;
    b.lineWidth = 0.6 + rnd(); b.beginPath();
    for (let x = 0; x <= W; x += 6) { const y = y0 + Math.sin(x * f + ph) * amp; x === 0 ? b.moveTo(x, y) : b.lineTo(x, y); }
    b.stroke();
  }
  // a couple of knots on the front
  for (const [kx, ky] of [[150, 46], [800, 58]]) {
    for (let r = 7; r > 1; r -= 2) { b.strokeStyle = 'rgba(55,30,12,0.35)'; b.lineWidth = 1; b.beginPath(); b.ellipse(kx, ky, r * 1.8, r * 0.7, 0, 0, Math.PI * 2); b.stroke(); }
  }
  // plank joints on the front face
  b.fillStyle = 'rgba(40,22,8,0.45)';
  for (const x of [312, 668]) b.fillRect(x, 22, 1.5, bh - 22);
  // front edge highlight + top highlight
  b.fillStyle = 'rgba(255,230,190,0.35)'; b.fillRect(0, 21, W, 1.5);
  b.fillStyle = 'rgba(255,240,215,0.30)'; b.fillRect(0, 0, W, 1.5);
  return c;
}
function drawIce(ctx, sim, dpr, back) {
  for (const p of sim.ice) {
    if (p.scale <= 0.03 || p.back !== back) continue;
    const k = p.r * p.scale, c = Math.cos(p.rot) * dpr, s = Math.sin(p.rot) * dpr, v = p.verts;
    ctx.setTransform(c, s, -s, c, p.x * dpr, p.y * dpr);
    ctx.beginPath(); ctx.moveTo(v[0][0] * k, v[0][1] * k);
    for (let j = 1; j < v.length; j++) ctx.lineTo(v[j][0] * k, v[j][1] * k);
    ctx.closePath(); ctx.fillStyle = p.fill; ctx.fill();
    ctx.lineWidth = 0.8; ctx.strokeStyle = p.edge; ctx.stroke();
    ctx.beginPath(); ctx.moveTo(v[0][0] * k * 0.72, v[0][1] * k * 0.72); ctx.lineTo(v[1][0] * k * 0.72, v[1][1] * k * 0.72);
    ctx.strokeStyle = 'rgba(255,255,255,0.95)'; ctx.lineWidth = 1.1; ctx.stroke();
  }
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}
function drawRod(ctx, sim) {
  const [ax, ay, bx, by] = sim.rodPos();
  ctx.lineCap = 'round';
  ctx.strokeStyle = 'rgba(110,140,155,0.6)'; ctx.lineWidth = 8;
  ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(bx, by); ctx.stroke();
  ctx.strokeStyle = 'rgba(236,246,250,0.92)'; ctx.lineWidth = 5.4; ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,1)'; ctx.lineWidth = 1.2;
  ctx.beginPath(); ctx.moveTo(ax - 1.4, ay - 4); ctx.lineTo(bx - 1.4, by + 4); ctx.stroke();
  ctx.lineCap = 'butt';
}
const uC = T => 14 + (clamp(T, -30, 10) + 30) * 3;
const CTH = { a: 0.14, len: 150 };
function bagThermo(bag) { return { x: bag.x + 16, y: bag.y + 9 }; }
let vanillaDots = null;
function drawBag(ctx, sim) {
  const bag = sim.bag; if (!bag) return;
  const cs = sim.creamState(), frozen = 1 - cs.liq;
  const x0 = bag.x - BAG.hw, x1 = bag.x + BAG.hw, y0 = bag.y - BAG.hh, y1 = bag.y + BAG.hh;
  // plastic bag body (slightly bulging sides)
  ctx.beginPath();
  ctx.moveTo(x0 + 3, y0);
  ctx.lineTo(x1 - 3, y0);
  ctx.quadraticCurveTo(x1 + 3, bag.y, x1 - 1, y1 - 3);
  ctx.quadraticCurveTo(bag.x, y1 + 3, x0 + 1, y1 - 3);
  ctx.quadraticCurveTo(x0 - 3, bag.y, x0 + 3, y0);
  ctx.closePath();
  ctx.fillStyle = 'rgba(240,248,252,0.55)'; ctx.fill();
  // the mix inside
  ctx.save(); ctx.clip();
  const top = y0 + 13;
  const g = ctx.createLinearGradient(0, top, 0, y1);
  g.addColorStop(0, frozen > 0.5 ? '#fbf3d6' : '#f6e6b4'); g.addColorStop(1, '#ecd38f');
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.moveTo(x0 - 4, top + 2);
  ctx.quadraticCurveTo(bag.x - 20, top - 3 * cs.liq, bag.x, top + 1); ctx.quadraticCurveTo(bag.x + 22, top + 4 * cs.liq, x1 + 4, top);
  ctx.lineTo(x1 + 4, y1 + 4); ctx.lineTo(x0 - 4, y1 + 4); ctx.closePath(); ctx.fill();
  // frozen look: paler, frosty texture builds up
  if (frozen > 0) {
    ctx.globalAlpha = 0.65 * frozen;
    ctx.fillStyle = '#fffaf0'; ctx.fillRect(x0 - 4, top - 4, x1 - x0 + 8, y1 - top + 8);
    ctx.globalAlpha = Math.min(1, frozen * 1.2);
    ctx.strokeStyle = 'rgba(255,255,255,0.95)'; ctx.lineWidth = 0.8; ctx.beginPath();
    for (let k = 0; k < 22; k++) {
      const fx = x0 + 6 + ((k * 37) % (2 * BAG.hw - 12)), fy = top + 5 + ((k * 23) % (y1 - top - 9));
      ctx.moveTo(fx - 2.5, fy); ctx.lineTo(fx + 2.5, fy); ctx.moveTo(fx, fy - 2.5); ctx.lineTo(fx, fy + 2.5);
    }
    ctx.stroke(); ctx.globalAlpha = 1;
  }
  // vanilla seeds
  if (!vanillaDots) { vanillaDots = []; for (let k = 0; k < 34; k++) vanillaDots.push([rand(-BAG.hw + 4, BAG.hw - 4), rand(-BAG.hh + 16, BAG.hh - 4)]); }
  ctx.fillStyle = 'rgba(70,45,25,0.55)';
  for (const [dx, dy] of vanillaDots) ctx.fillRect(bag.x + dx, bag.y + dy, 1.3, 1.3);
  ctx.restore();
  // outline + highlight
  ctx.lineWidth = 1.4; ctx.strokeStyle = 'rgba(120,150,165,0.9)'; ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,0.8)'; ctx.lineWidth = 2;
  ctx.beginPath(); ctx.moveTo(x0 + 6, y0 + 16); ctx.quadraticCurveTo(x0 + 3, bag.y + 4, x0 + 7, y1 - 8); ctx.stroke();
  // zip seal
  ctx.fillStyle = 'rgba(214,232,242,0.95)'; ctx.fillRect(x0 + 2, y0, x1 - x0 - 4, 8);
  ctx.strokeStyle = '#3d7fc0'; ctx.lineWidth = 1.6;
  ctx.beginPath(); ctx.moveTo(x0 + 3, y0 + 3); ctx.lineTo(x1 - 3, y0 + 3); ctx.stroke();
  ctx.strokeStyle = '#d44a3a'; ctx.lineWidth = 1.2;
  ctx.beginPath(); ctx.moveTo(x0 + 3, y0 + 6); ctx.lineTo(x1 - 3, y0 + 6); ctx.stroke();
}
function drawBagThermo(ctx, sim, dpr) {
  const bag = sim.bag; if (!bag) return;
  const T = sim.creamState().T, p = bagThermo(bag), c = Math.cos(CTH.a), s = Math.sin(CTH.a);
  ctx.setTransform(c * dpr, s * dpr, -s * dpr, c * dpr, p.x * dpr, p.y * dpr);
  rr(ctx, -4.5, -CTH.len, 9, CTH.len + 2, 4.5);
  ctx.fillStyle = 'rgba(248,251,252,0.92)'; ctx.fill();
  ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(90,110,120,0.9)'; ctx.stroke();
  const u = uC(T);
  ctx.fillStyle = '#d02c2c'; ctx.fillRect(-1.3, -u, 2.6, u);
  ctx.beginPath(); ctx.arc(0, 0, 6.5, 0, Math.PI * 2); ctx.fill();
  ctx.strokeStyle = 'rgba(90,110,120,0.9)'; ctx.stroke();
  ctx.strokeStyle = '#25313a'; ctx.lineWidth = 0.8; ctx.beginPath();
  for (let t = -30; t <= 10; t += 5) { const y = -uC(t); ctx.moveTo(1.2, y); ctx.lineTo(t % 10 === 0 ? 4.5 : 3.2, y); }
  ctx.stroke();
  ctx.font = `700 8.5px ${FONT}`; ctx.textAlign = 'left';
  for (let t = -30; t <= 10; t += 10) haloText(ctx, (t < 0 ? '−' : '') + Math.abs(t), 7, -uC(t) + 3, '#1b262e');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}
function draw(ctx, sim, dpr, now, reduced) {
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  // wall
  let g = ctx.createLinearGradient(0, 0, 0, BENCH);
  g.addColorStop(0, '#d9e4e8'); g.addColorStop(1, '#c2d0d6');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, BENCH);
  ctx.strokeStyle = 'rgba(255,255,255,0.32)'; ctx.lineWidth = 1;
  ctx.beginPath();
  for (let x = 30; x < W; x += 60) { ctx.moveTo(x + 0.5, 0); ctx.lineTo(x + 0.5, BENCH); }
  for (let y = 46; y < BENCH; y += 60) { ctx.moveTo(0, y + 0.5); ctx.lineTo(W, y + 0.5); }
  ctx.stroke();
  // bench
  if (!benchImg || benchImg.dpr !== dpr) { benchImg = makeBench(dpr); benchImg.dpr = dpr; }
  ctx.drawImage(benchImg, 0, BENCH, W, H - BENCH);
  // shadows
  ctx.fillStyle = 'rgba(40,20,5,0.35)';
  ctx.beginPath(); ctx.ellipse((X0 + X1) / 2, BENCH + 4, (X1 - X0) / 2 + 10, 5, 0, 0, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.ellipse((SB.x0 + SB.x1) / 2, BENCH + 4, (SB.x1 - SB.x0) / 2 + 8, 4, 0, 0, Math.PI * 2); ctx.fill();
  // glass back tint
  ctx.fillStyle = 'rgba(255,255,255,0.20)'; ctx.fillRect(X0, TOP - 8, X1 - X0, BOT - TOP + 10);

  // ice shards: some behind the stirring rod, the rest in front
  drawIce(ctx, sim, dpr, true);
  drawBag(ctx, sim);
  drawRod(ctx, sim);
  drawIce(ctx, sim, dpr, false);
  // salt grains
  for (const gr of sim.salt) {
    if (gr.dis >= 1) continue;
    const sz = gr.sz * (1 - 0.5 * gr.dis), c = Math.cos(gr.rot) * dpr, s = Math.sin(gr.rot) * dpr;
    ctx.setTransform(c, s, -s, c, gr.x * dpr, gr.y * dpr);
    ctx.globalAlpha = 1 - gr.dis;
    ctx.fillStyle = gr.c; ctx.fillRect(-sz / 2, -sz / 2, sz, sz);
    ctx.lineWidth = 0.6; ctx.strokeStyle = 'rgba(128,112,60,0.8)'; ctx.strokeRect(-sz / 2, -sz / 2, sz, sz);
  }
  ctx.globalAlpha = 1; ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

  // meltwater
  const wy = sim.waterY();
  if (wy < BOT - 0.3) {
    ctx.fillStyle = 'rgba(62,138,204,0.36)'; ctx.fillRect(X0, wy, X1 - X0, BOT - wy);
    ctx.fillStyle = 'rgba(225,242,255,0.75)'; ctx.fillRect(X0, wy - 0.8, X1 - X0, 1.6);
  }

  // thermometer
  const T = sim.T(), fp = sim.fp;
  {
    const c = Math.cos(TH.a), s = Math.sin(TH.a);
    ctx.setTransform(c * dpr, s * dpr, -s * dpr, c * dpr, TH.x * dpr, TH.y * dpr);
    rr(ctx, -6, -TH.len, 12, TH.len + 2, 6);
    ctx.fillStyle = 'rgba(248,251,252,0.9)'; ctx.fill();
    ctx.lineWidth = 1.2; ctx.strokeStyle = 'rgba(90,110,120,0.9)'; ctx.stroke();
    const uT = uOf(T);
    ctx.fillStyle = '#d02c2c'; ctx.fillRect(-1.7, -uT, 3.4, uT);
    ctx.beginPath(); ctx.arc(0, 0, 9, 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = 'rgba(90,110,120,0.9)'; ctx.stroke();
    ctx.beginPath(); ctx.arc(-3, -3, 2.4, 0, Math.PI * 2); ctx.fillStyle = 'rgba(255,255,255,0.7)'; ctx.fill();
    ctx.strokeStyle = '#25313a'; ctx.lineWidth = 0.9; ctx.beginPath();
    for (let t = -30; t <= 10; t += 2) { const y = -uOf(t); ctx.moveTo(1.5, y); ctx.lineTo(t % 10 === 0 ? 6 : 4.2, y); }
    ctx.stroke();
    ctx.font = `700 9.5px ${FONT}`; ctx.textAlign = 'left';
    for (let t = -30; t <= 10; t += 10) haloText(ctx, (t < 0 ? '\u2212' : '') + Math.abs(t), 9, -uOf(t) + 3.5, '#1b262e');
    const yf = -uOf(fp);
    ctx.beginPath(); ctx.moveTo(-6.5, yf); ctx.lineTo(-13.5, yf - 4.5); ctx.lineTo(-13.5, yf + 4.5); ctx.closePath();
    ctx.fillStyle = '#1b62c4'; ctx.fill();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }

  drawBagThermo(ctx, sim, dpr);

  // beaker glass (front)
  beakerPath(ctx, X0, X1, TOP, BOT, 10);
  ctx.lineJoin = 'round'; ctx.lineWidth = 3.4; ctx.strokeStyle = 'rgba(140,178,195,0.95)'; ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,0.55)'; ctx.lineWidth = 3;
  ctx.beginPath(); ctx.moveTo(X0 + 8, TOP + 6); ctx.lineTo(X0 + 8, BOT - 24); ctx.stroke();
  ctx.lineWidth = 1.5; ctx.beginPath(); ctx.moveTo(X1 - 26, TOP + 14); ctx.lineTo(X1 - 26, TOP + 90); ctx.stroke();
  ctx.font = `700 9px ${FONT}`; ctx.textAlign = 'right'; ctx.strokeStyle = 'rgba(60,85,100,0.75)'; ctx.lineWidth = 1.2;
  for (let k = 1; k <= 4; k++) {
    const y = BOT - k * 52;
    ctx.beginPath(); ctx.moveTo(X1 + 2, y); ctx.lineTo(X1 - 14, y); ctx.strokeStyle = 'rgba(60,85,100,0.75)'; ctx.stroke();
    for (let j = 1; j <= 1; j++) { ctx.beginPath(); ctx.moveTo(X1 + 2, y + 26); ctx.lineTo(X1 - 7, y + 26); ctx.stroke(); }
    haloText(ctx, k * 100 + ' ml', X1 - 18, y + 3, '#2b3d48');
  }

  // salt beaker
  const vis = Math.floor(sim.heap.length * sim.pinches / MAX_SCOOPS);
  for (let k = 0; k < vis; k++) { const q = sim.heap[k]; ctx.fillStyle = q.sh ? '#e8e0c2' : q.c; ctx.fillRect(q.x - 1.2, q.y - 1.2, 2.4, 2.4); }
  ctx.fillStyle = 'rgba(255,255,255,0.18)'; ctx.fillRect(SB.x0, SB.top - 6, SB.x1 - SB.x0, SB.bot - SB.top + 8);
  beakerPath(ctx, SB.x0, SB.x1, SB.top, SB.bot, 6);
  ctx.lineWidth = 3; ctx.strokeStyle = sim.hover && sim.pinches > 0 && !sim.drag ? 'rgba(27,98,196,0.95)' : 'rgba(140,178,195,0.95)'; ctx.stroke();
  rr(ctx, SB.x0 + 30, SB.top + 8, 60, 22, 4); ctx.fillStyle = 'rgba(255,255,255,0.95)'; ctx.fill();
  ctx.lineWidth = 1; ctx.strokeStyle = '#7d8f99'; ctx.stroke();
  ctx.font = `700 12px ${FONT}`; ctx.textAlign = 'center'; ctx.fillStyle = '#1b262e';
  ctx.fillText(sim.pinches > 0 ? 'NaCl' : 'Empty', (SB.x0 + SB.x1) / 2, SB.top + 23);

  // readout + freezing-point label
  ctx.textAlign = 'left';
  rr(ctx, 40, 32, 176, 50, 9); ctx.fillStyle = 'rgba(255,255,255,0.94)'; ctx.fill();
  ctx.lineWidth = 1.5; ctx.strokeStyle = '#d02c2c'; ctx.stroke();
  ctx.font = `400 12px ${FONT}`; ctx.fillStyle = '#3a4852'; ctx.fillText('Thermometer reads', 54, 51);
  ctx.font = `700 19px ${FONT}`; ctx.fillStyle = '#b52222'; ctx.fillText(fmtT(T), 54, 73);
  const [mx, my] = thermoPt(uOf(fp), -14);
  const by = clamp(my, 112, H - 60);
  ctx.strokeStyle = '#1b62c4'; ctx.lineWidth = 1.3; ctx.setLineDash([3, 3]);
  ctx.beginPath(); ctx.moveTo(216, by); ctx.lineTo(mx, my); ctx.stroke(); ctx.setLineDash([]);
  rr(ctx, 40, by - 23, 176, 46, 9); ctx.fillStyle = 'rgba(255,255,255,0.94)'; ctx.fill();
  ctx.lineWidth = 1.5; ctx.strokeStyle = '#1b62c4'; ctx.stroke();
  ctx.font = `400 12px ${FONT}`; ctx.fillStyle = '#3a4852'; ctx.fillText('Freezing point', 54, by - 5);
  ctx.font = `700 17px ${FONT}`; ctx.fillStyle = '#1b62c4'; ctx.fillText(fmtT(fp), 54, by + 15);

  if (sim.bag) {
    const cs = sim.creamState(), tp = bagThermo(sim.bag);
    const topX = tp.x + Math.sin(CTH.a) * CTH.len, topY = tp.y - Math.cos(CTH.a) * CTH.len;
    const bx0 = 668, by0 = 32;
    ctx.strokeStyle = '#c99a0a'; ctx.lineWidth = 1.3; ctx.setLineDash([3, 3]);
    ctx.beginPath(); ctx.moveTo(bx0, by0 + 25); ctx.lineTo(topX + 6, topY + 6); ctx.stroke(); ctx.setLineDash([]);
    rr(ctx, bx0, by0, 196, 50, 9); ctx.fillStyle = 'rgba(255,255,255,0.94)'; ctx.fill();
    ctx.lineWidth = 1.5; ctx.strokeStyle = '#d4a514'; ctx.stroke();
    ctx.textAlign = 'left';
    ctx.font = `400 12px ${FONT}`; ctx.fillStyle = '#3a4852';
    ctx.fillText('Ice cream mix', bx0 + 14, by0 + 19);
    // state as a coloured tag: liquid (warm), freezing (purple, like potential energy), frozen (icy blue)
    const st = cs.liq >= 1 ? ['Liquid', '#c25a00'] : cs.liq > 0 ? ['Freezing', '#6a4fd6'] : ['Frozen', '#1b62c4'];
    ctx.font = `700 11.5px ${FONT}`;
    const tw = ctx.measureText(st[0]).width, tx = bx0 + 196 - tw - 26;
    rr(ctx, tx, by0 + 8, tw + 14, 18, 9); ctx.fillStyle = st[1]; ctx.fill();
    ctx.fillStyle = '#ffffff'; ctx.fillText(st[0], tx + 7, by0 + 21);
    ctx.font = `700 19px ${FONT}`; ctx.fillStyle = '#8f6b00'; ctx.fillText(fmtT(cs.T), bx0 + 14, by0 + 41);
  }

  // hints
  const bob = reduced ? 0 : Math.sin(now * 3) * 3;
  ctx.textAlign = 'center'; ctx.font = `700 14px ${FONT}`;
  if (!sim.saltAdded && !sim.drag) {
    const cx = (SB.x0 + SB.x1) / 2;
    haloText(ctx, 'Drag salt into the ice', cx, 318 + bob, '#1b262e');
    ctx.strokeStyle = '#1b262e'; ctx.lineWidth = 2; ctx.beginPath();
    ctx.moveTo(cx, 328 + bob); ctx.lineTo(cx, 356 + bob); ctx.moveTo(cx - 5, 350 + bob); ctx.lineTo(cx, 356 + bob); ctx.lineTo(cx + 5, 350 + bob); ctx.stroke();
  } else if (sim.scoopsIn > sim.scoopsStirred && !sim.stir && !sim.drag) {
    haloText(ctx, 'Now stir it in', (X0 + X1) / 2 + 20, TOP - 34 + bob, '#1b262e');
  }

  // dragging a scoop
  if (sim.drag) {
    const { x, y } = sim.drag;
    const over = x > X0 - 12 && x < X1 + 12 && y > TOP - 90 && y < BOT;
    if (over) {
      ctx.setLineDash([5, 4]); ctx.strokeStyle = 'rgba(27,98,196,0.9)'; ctx.lineWidth = 2;
      rr(ctx, X0 - 8, TOP - 16, X1 - X0 + 16, BOT - TOP + 24, 10); ctx.stroke(); ctx.setLineDash([]);
    }
    ctx.lineCap = 'round'; ctx.strokeStyle = '#7f8c95'; ctx.lineWidth = 4;
    ctx.beginPath(); ctx.moveTo(x + 12, y - 2); ctx.lineTo(x + 70, y - 46); ctx.stroke(); ctx.lineCap = 'butt';
    ctx.beginPath(); ctx.ellipse(x, y + 2, 17, 6, -0.2, 0, Math.PI * 2); ctx.fillStyle = '#b9c4ca'; ctx.fill();
    ctx.strokeStyle = '#7f8c95'; ctx.lineWidth = 1; ctx.stroke();
    for (const o of sim.drag.grains) { ctx.fillStyle = o.c; ctx.fillRect(x + o.x - 1.2, y + o.y - 1.2, 2.4, 2.4); }
  }
}
// ===== React UI =====
const h = React.createElement;

// arrow above a bar: 1 rising, -1 falling, 0 steady
function Trend({ x, top, dir }) {
  const y = top - 7;
  if (dir > 0) return h('path', { className: 'trend', d: `M${x},${y - 16} l8,9 h-4.5 v7 h-7 v-7 h-4.5 z` });
  if (dir < 0) return h('path', { className: 'trend', d: `M${x},${y} l8,-9 h-4.5 v-7 h-7 v7 h-4.5 z` });
  return h('line', { className: 'steady', x1: x - 8, x2: x + 8, y1: y - 8, y2: y - 8 });
}
const TREND_WORD = d => d > 0 ? 'rising' : d < 0 ? 'falling' : 'steady';
function EnergyBars({ ke, pe, cream, tr }) {
  tr = tr || { kw: 0, pw: 0, kc: 0, pc: 0, tot: 0 };
  const HH = 160, T0 = 24, base = T0 + HH;
  if (!cream) {
    const unit = HH / 100, maxV = Math.max(100, ke + pe);
    const y = v => base - v * unit, bw = 54;
    const viewTop = (base - maxV * unit) - 24, viewH = (base + 52) - viewTop;
    const bars = [
      { x: 70, label: 'Kinetic', sub: 'temperature', segs: [[0, ke, 'var(--ke)']], top: ke, dir: tr.kw },
      { x: 155, label: 'Potential', sub: 'state', segs: [[0, pe, 'var(--pe)']], top: pe, dir: tr.pw },
      { x: 240, label: 'Internal', sub: 'KE + PE', segs: [[0, ke, 'var(--ke)'], [ke, ke + pe, 'var(--pe)']], top: ke + pe, dir: tr.tot || 0 }
    ];
    return h('svg', { viewBox: `0 ${viewTop} 310 ${viewH}`, className: 'chart', role: 'img',
      'aria-label': `Kinetic energy ${TREND_WORD(tr.kw)}, potential energy ${TREND_WORD(tr.pw)}. Internal energy is their total, ${TREND_WORD(tr.tot)}.` },
      bars.map(b => h('g', { key: b.label },
        b.segs.map(([a, c, col], i) => h('rect', { key: i, x: b.x - bw / 2, y: y(c), width: bw, height: Math.max(0, y(a) - y(c)), fill: col })),
        b.segs.length > 1 && h('line', { x1: b.x - bw / 2, x2: b.x + bw / 2, y1: y(ke), y2: y(ke), className: 'divider' }),
        h(Trend, { x: b.x, top: y(b.top), dir: b.dir }),
        h('text', { x: b.x, y: base + 19, className: 'blab', textAnchor: 'middle' }, b.label),
        h('text', { x: b.x, y: base + 34, className: 'bsub', textAnchor: 'middle' }, b.sub))),
      h('line', { x1: 24, x2: 286, y1: base, y2: base, className: 'axis' }));
  }
  const tot = ke + pe + cream.ke + cream.pe, unit = HH / 145, maxV = Math.max(145, tot);
  const y = v => base - v * unit, bw = 34;
  const viewTop = (base - maxV * unit) - 24, viewH = (base + 52) - viewTop;
  const bar = (x, a, c, fill, w, key) => h('rect', { key, x: x - w / 2, y: y(c), width: w, height: Math.max(0, y(a) - y(c)), fill });
  const segs = [[ke, 'var(--ke)'], [pe, 'var(--pe)'], [cream.ke, 'url(#hatchKE)'], [cream.pe, 'url(#hatchPE)']];
  let acc = 0;
  const stack = segs.map(([v, f], i) => { const r = bar(266, acc, acc + v, f, 44, 's' + i); acc += v; return r; });
  const divs = []; acc = 0;
  for (let i = 0; i < 3; i++) { acc += segs[i][0]; divs.push(h('line', { key: 'd' + i, x1: 244, x2: 288, y1: y(acc), y2: y(acc), className: 'divider' })); }
  const lab = (x, t, cls, dy) => h('text', { x, y: base + dy, className: cls, textAnchor: 'middle' }, t);
  return h('svg', { viewBox: `0 ${viewTop} 310 ${viewH}`, className: 'chart', role: 'img',
    'aria-label': `Water and ice: kinetic energy ${TREND_WORD(tr.kw)}, potential energy ${TREND_WORD(tr.pw)}. Ice cream mix: kinetic energy ${TREND_WORD(tr.kc)}, potential energy ${TREND_WORD(tr.pc)}. The total of all four is ${TREND_WORD(tr.tot)}.` },
    h('defs', null,
      h('pattern', { id: 'hatchKE', width: 6, height: 6, patternUnits: 'userSpaceOnUse', patternTransform: 'rotate(45)' },
        h('rect', { width: 6, height: 6, fill: 'var(--ke)', opacity: 0.45 }), h('rect', { width: 3, height: 6, fill: 'var(--ke)' })),
      h('pattern', { id: 'hatchPE', width: 6, height: 6, patternUnits: 'userSpaceOnUse', patternTransform: 'rotate(45)' },
        h('rect', { width: 6, height: 6, fill: 'var(--pe)', opacity: 0.45 }), h('rect', { width: 3, height: 6, fill: 'var(--pe)' }))),
    bar(40, 0, ke, 'var(--ke)', bw, 'wk'), bar(80, 0, pe, 'var(--pe)', bw, 'wp'),
    bar(146, 0, cream.ke, 'url(#hatchKE)', bw, 'ck'), bar(186, 0, cream.pe, 'url(#hatchPE)', bw, 'cp'),
    stack, divs,
    h(Trend, { x: 40, top: y(ke), dir: tr.kw }), h(Trend, { x: 80, top: y(pe), dir: tr.pw }),
    h(Trend, { x: 146, top: y(cream.ke), dir: tr.kc }), h(Trend, { x: 186, top: y(cream.pe), dir: tr.pc }),
    h(Trend, { x: 266, top: y(tot), dir: tr.tot || 0 }),
    lab(40, 'KE', 'bsub', 15), lab(80, 'PE', 'bsub', 15), lab(146, 'KE', 'bsub', 15), lab(186, 'PE', 'bsub', 15), lab(266, 'all four', 'bsub', 15),
    lab(60, 'Water & ice', 'blab', 33), lab(166, 'Ice cream', 'blab', 33), lab(266, 'Total', 'blab', 33),
    h('line', { x1: 16, x2: 296, y1: base, y2: base, className: 'axis' }));
}

function TempGraph({ hist, events, now }) {
  const [hover, setHover] = useState(null);
  const svgRef = useRef(null);
  const L = 44, Rr = 628, Tp = 12, B = 186, YMIN = -25, YMAX = 10;
  const steps = [10, 15, 30, 60, 120, 180, 300, 600, 900, 1800];
  const span = Math.max(60, now);
  const step = steps.find(st => span / st <= 7) || 3600;
  const xmax = Math.ceil(span / step) * step;
  const xs = t => L + (t / xmax) * (Rr - L), ys = T => B - ((clamp(T, YMIN, YMAX) - YMIN) / (YMAX - YMIN)) * (B - Tp);
  const n = hist.length, k = Math.max(1, Math.ceil(n / 700));
  const pts = []; for (let i = 0; i < n; i += k) pts.push(hist[i]); if (n && pts[pts.length - 1] !== hist[n - 1]) pts.push(hist[n - 1]);
  const line = key => { let d = '', on = false;
    for (const p of pts) { const v = p[key]; if (v === null || v === undefined) { on = false; continue; } d += (on ? 'L' : 'M') + xs(p.t).toFixed(1) + ',' + ys(v).toFixed(1); on = true; }
    return d; };
  const hasCream = hist.some(p => p.Tc !== null);
  const xt = []; for (let t = 0; t <= xmax + 1e-6; t += step) xt.push(t);
  const yt = []; for (let T = YMIN; T <= YMAX; T += 5) yt.push(T);
  const onMove = e => {
    const r = svgRef.current.getBoundingClientRect(), x = (e.clientX - r.left) * 640 / r.width;
    if (x < L || x > Rr || !n) { setHover(null); return; }
    const t = (x - L) / (Rr - L) * xmax;
    let lo = 0, hi = n - 1; while (lo < hi) { const mid = (lo + hi) >> 1; if (hist[mid].t < t) lo = mid + 1; else hi = mid; }
    setHover(t > hist[n - 1].t + 1 ? null : hist[lo]);
  };
  const last = n ? hist[n - 1] : null;
  const fmtTime = t => t < 120 ? Math.round(t) + ' s' : Math.floor(t / 60) + ' min ' + String(Math.round(t % 60)).padStart(2, '0') + ' s';
  let tip = null;
  if (hover) {
    const rows = [['Ice & water', hover.T, 'var(--g-ice)'], ['Freezing point', hover.fp, 'var(--g-fp)']];
    if (hover.Tc !== null) rows.push(['Ice cream mix', hover.Tc, 'var(--g-cream)']);
    const hx = xs(hover.t), w = 184, hgt = 22 + rows.length * 17, bx = hx + 10 + w > Rr ? hx - 10 - w : hx + 10;
    tip = h('g', { className: 'tip', pointerEvents: 'none' },
      h('line', { className: 'cross', x1: hx, x2: hx, y1: Tp, y2: B }),
      rows.map(([lab, v, c]) => h('circle', { key: lab, cx: hx, cy: ys(v), r: 4, fill: c, stroke: 'var(--paper)', strokeWidth: 2 })),
      h('rect', { className: 'tipbg', x: bx, y: Tp + 4, width: w, height: hgt, rx: 7 }),
      h('text', { x: bx + 10, y: Tp + 20, className: 'tt' }, fmtTime(hover.t)),
      rows.map(([lab, v, c], i) => h('g', { key: lab },
        h('rect', { x: bx + 10, y: Tp + 29 + i * 17, width: 9, height: 3, fill: c, stroke: 'none' }),
        h('text', { x: bx + 25, y: Tp + 35 + i * 17 }, lab),
        h('text', { x: bx + w - 10, y: Tp + 35 + i * 17, textAnchor: 'end', fontWeight: 700 }, fmtT(v)))));
  }
  return h('svg', { ref: svgRef, viewBox: '0 0 640 222', className: 'tgraph', role: 'img',
      'aria-label': last ? `Temperature against time. Ice and water now ${fmtT(last.T)}, freezing point ${fmtT(last.fp)}${last.Tc !== null ? ', ice cream mix ' + fmtT(last.Tc) : ''}.` : 'Temperature against time',
      onPointerMove: onMove, onPointerLeave: () => setHover(null) },
    yt.map(T => h('g', { key: 'y' + T },
      h('line', { x1: L, x2: Rr, y1: ys(T), y2: ys(T), className: T === 0 ? 'zero' : 'grid' }),
      h('text', { x: L - 7, y: ys(T) + 4, className: 'tick', textAnchor: 'end' }, (T < 0 ? '−' : '') + Math.abs(T)))),
    xt.map(t => h('text', { key: 'x' + t, x: xs(t), y: B + 16, className: 'tick', textAnchor: 'middle' }, step >= 60 ? (t / 60) : t)),
    h('text', { x: (L + Rr) / 2, y: B + 33, className: 'atitle', textAnchor: 'middle' }, step >= 60 ? 'Time (minutes)' : 'Time (seconds)'),
    h('text', { x: 12, y: (Tp + B) / 2, className: 'atitle', textAnchor: 'middle', transform: `rotate(-90 12 ${(Tp + B) / 2})` }, 'Temperature (°C)'),
    events.map((ev, i) => h('g', { key: 'e' + i },
      h('line', { className: 'ev', x1: xs(ev.t), x2: xs(ev.t), y1: Tp, y2: B }),
      h('text', { className: 'evl', x: xs(ev.t) + 4, y: Tp + 10 + (i % 2) * 13 }, ev.label))),
    h('path', { d: line('fp'), fill: 'none', stroke: 'var(--g-fp)', strokeWidth: 2, strokeDasharray: '6 4' }),
    hasCream && h('path', { d: line('Tc'), fill: 'none', stroke: 'var(--g-cream)', strokeWidth: 2.6, strokeLinejoin: 'round' }),
    h('path', { d: line('T'), fill: 'none', stroke: 'var(--g-ice)', strokeWidth: 2, strokeLinejoin: 'round' }),
    h('line', { x1: L, x2: Rr, y1: B, y2: B, className: 'axis' }),
    h('line', { x1: L, x2: L, y1: Tp, y2: B, className: 'axis' }),
    tip);
}
function GraphKey({ cream }) {
  const item = (lab, c, dash) => h('li', { key: lab },
    h('svg', { viewBox: '0 0 24 10', 'aria-hidden': true }, h('line', { x1: 1, x2: 23, y1: 5, y2: 5, stroke: c, strokeWidth: 2.5, strokeDasharray: dash || null })), lab);
  return h('ul', { className: 'gkey' }, item('Ice & water', 'var(--g-ice)'), item('Freezing point', 'var(--g-fp)', '5 3'), cream && item('Ice cream mix', 'var(--g-cream)'));
}

// a chart panel that can be minimised to its title bar
function Panel({ title, className, startOpen, open: openProp, onToggle, children }) {
  const [openState, setOpenState] = useState(!!startOpen);
  const open = openProp === undefined ? openState : openProp;
  const toggle = onToggle || (() => setOpenState(o => !o));
  return h('figure', { className: 'fig' + (className ? ' ' + className : '') + (open ? '' : ' min') },
    h('div', { className: 'fighead' },
      h('h2', null, title),
      h('button', { className: 'minbtn', 'aria-expanded': open, 'aria-label': (open ? 'Minimise ' : 'Restore ') + title,
          title: open ? 'Minimise' : 'Restore', onClick: toggle },
        h('svg', { viewBox: '0 0 12 12', 'aria-hidden': true }, open
          ? h('path', { d: 'M2 6 H10', fill: 'none', stroke: 'currentColor', strokeWidth: 1.8, strokeLinecap: 'round' })
          : h('path', { d: 'M6 2 V10 M2 6 H10', fill: 'none', stroke: 'currentColor', strokeWidth: 1.8, strokeLinecap: 'round' })))),
    open && h('div', { className: 'figbody' }, children));
}

function Pie({ water }) {
  const cx = 70, cy = 70, r = 62, a = water * 2 * Math.PI;
  let w = null;
  if (water > 0.998) w = h('circle', { cx, cy, r, fill: 'var(--water)' });
  else if (water > 0.002) {
    const ex = cx + r * Math.sin(a), ey = cy - r * Math.cos(a);
    w = h('path', { d: `M${cx},${cy} L${cx},${cy - r} A${r},${r} 0 ${a > Math.PI ? 1 : 0} 1 ${ex},${ey} Z`, fill: 'var(--water)' });
  }
  const ip = Math.round((1 - water) * 100), wp = 100 - ip;
  return h('div', { className: 'pie' },
    h('svg', { viewBox: '0 0 140 140', role: 'img', 'aria-label': `Ice ${ip}%, water ${wp}% by mass` },
      h('circle', { cx, cy, r, fill: 'var(--ice)', stroke: 'var(--ice-edge)', strokeWidth: 1.5 }), w),
    h('ul', { className: 'legend' },
      h('li', null, h('span', { className: 'sw ice' }), 'Ice', h('b', null, ip + '%')),
      h('li', null, h('span', { className: 'sw water' }), 'Water', h('b', null, wp + '%'))));
}

const STEPS = ['Add salt', 'Stir it in', 'Ice melts and the mixture cools', 'A new balance at the freezing point'];
function creamNotes(s) {
  const c = s.cream; if (!c) return [];
  return creamState(s).concat(c.T - s.T > 0.4 ? [c.boost
    ? 'Stirring keeps cold water and ice moving against the bag, so energy leaves the ice cream mix twice as fast.'
    : 'Stir to move cold water and ice against the bag. That speeds up the energy transfer out of the ice cream mix.'] : []);
}
function creamState(s) {
  const c = s.cream;
  if (c.liq >= 1 && c.T > s.T + 0.4) return [
    'The ice cream mix is warmer than the ice around it, so energy flows out of the bag. Its particles slow down, so its kinetic energy and temperature fall. ' + (s.T < s.fp - 0.05 ? 'That energy warms the ice up towards its melting point.' : 'That energy melts more ice instead of warming it.')];
  if (c.liq >= 1) return [
    `The ice cream mix has cooled to ${fmtT(c.T)}, the same as the ice around it. It only freezes below about −3 °C, so it stays liquid.` +
    (s.fp > FPC ? ' Add salt to make the ice colder.' : '')];
  if (c.liq > 0) return [
    'The ice cream mix is freezing. Its temperature stays at about −3 °C while it freezes, because the energy leaving it now comes from its potential store, not its kinetic store.'];
  return [c.T > s.T + 0.4
    ? 'The ice cream mix has frozen. It keeps losing energy, and cooling, until it matches the ice around it.'
    : `The ice cream is frozen at ${fmtT(s.T)}, the same temperature as the ice around it.`];
}
function explain(stage, s) {
  if (stage === 0 && !s.insulated) {
    const msgs = [`${s.T > T_ICE0 + 0.05 ? 'The ice has warmed to' : 'The ice is at'} ${fmtT(s.T)}. The insulation is off, so the beaker is no longer a closed system: energy leaks in from the room, and the total internal energy rises.`];
    msgs.push(s.m > 0.001
      ? 'Once the ice reached 0 \u00B0C, that extra energy started melting it \u2014 raising potential energy \u2014 with no salt involved at all.'
      : 'For now that energy is raising the particles\u2019 kinetic energy, warming the ice towards its melting point of 0 \u00B0C.');
    return msgs;
  }
  if (stage === 0 && s.cream) return [
    `${s.T > T_ICE0 + 0.05 ? 'The ice has warmed to' : 'The ice is at'} ${fmtT(s.T)}. Its melting point is 0 \u00B0C. The beaker is insulated, so the only energy coming in is from the ice cream mix.`];
  if (stage === 0) return [
    'The ice is at \u22122 \u00B0C, below its melting point of 0 \u00B0C. The beaker is insulated, so no energy comes in from the room.',
    'The ice is colder than its freezing point, so it stays solid.' +
      (s.stirredNoSalt ? ' Stirring on its own changes nothing.' : '')];
  if (stage === 1) return [
    (s.scoops > 0 ? 'More salt is sitting on top of the ice. ' : 'The salt is sitting on top of the ice. ') +
    'Stir it in so it can dissolve in the thin film of water on the surface of each shard.'];
  if (stage === 2) return [
    `${s.scoops === 1 ? 'One scoop' : s.scoops + ' scoops'} of dissolved salt lower${s.scoops === 1 ? 's' : ''} the freezing point to ${fmtT(s.fpTarget)}. The more concentrated the salt solution, the lower the freezing point. The ice is now warmer than its freezing point, so it melts.`,
    'Melting means particles break free of the bonds holding them in the solid, which raises their potential energy.',
    s.cream ? 'Most of that energy has to come from the particles\u2019 own kinetic energy, with a little from the ice cream mix. Less kinetic energy means a lower temperature.'
      : (s.insulated ? 'No energy is coming in from outside, so that energy has to come from the particles\u2019 own kinetic energy. Less kinetic energy means a lower temperature.'
        : 'With the insulation off, some of that energy is topped up by leakage from the room, but most still has to come from the particles\u2019 own kinetic energy, so the temperature still falls.')];
  return [
    `The mixture has cooled to ${fmtT(s.fpTarget)}, the new freezing point. Ice and salty water are in balance again, so melting stops.`,
    s.cream ? 'The total internal energy never changed. Energy moved from kinetic stores (temperature) into potential stores (state), and from the ice cream mix into the water and ice.'
      : (s.insulated ? 'The internal energy never changed. Energy moved from the kinetic store (temperature) into the potential store (state).'
        : 'With the insulation off, energy keeps leaking in from the room, so the mixture won\u2019t stay balanced for long \u2014 it will keep melting.'),
    s.pinches > 0 ? 'Add another scoop and stir again to lower the freezing point further.'
      : 'That\u2019s as much salt as the water can take. \u221221.1 \u00B0C is the lowest freezing point salt water can have.'];
}

function App() {
  const cvRef = useRef(null), simRef = useRef(null), speedRef = useRef(1);
  const [ui, setUi] = useState(null);
  const [speed, setSpeed] = useState(1);
  const [paused, setPaused] = useState(false);
  const [tempOpen, setTempOpen] = useState(false);
  const pausedRef = useRef(false);
  useEffect(() => { speedRef.current = speed; }, [speed]);
  useEffect(() => { pausedRef.current = paused; }, [paused]);
  useEffect(() => {
    const sim = new Sim(); simRef.current = sim; setUi(sim.snapshot());
    const cv = cvRef.current, ctx = cv.getContext('2d');
    const dpr = Math.min(2, window.devicePixelRatio || 1);
    cv.width = W * dpr; cv.height = H * dpr;
    const mq = window.matchMedia('(prefers-reduced-motion: reduce)');
    let raf, last = performance.now(), acc = 0, lastUi = 0, prev = {}, lastTr = {}; const rate = {};
    const loop = now => {
      acc += Math.min(0.1, (now - last) / 1000); last = now;
      let n = 0;
      if (pausedRef.current) acc = 0;
      while (acc >= 1 / 60 && n < 4) { sim.update(1 / 60, speedRef.current); acc -= 1 / 60; n++; }
      if (n === 4) acc = 0;
      draw(ctx, sim, dpr, now / 1000, mq.matches);
      if (now - lastUi > 60) {
        const snap = sim.snapshot(), dtu = Math.max(0.001, (now - lastUi) / 1000); lastUi = now;
        const vals = { kw: snap.ke, pw: snap.pe, kc: snap.cream ? snap.cream.ke : 0, pc: snap.cream ? snap.cream.pe : 0 };
        vals.tot = vals.kw + vals.pw + vals.kc + vals.pc;
        let tr = {};
        if (pausedRef.current) { tr = lastTr; prev = {}; } else for (const k in vals) {
          const r = prev[k] === undefined ? 0 : (vals[k] - prev[k]) / dtu;
          rate[k] = (rate[k] || 0) * 0.7 + r * 0.3;
          tr[k] = rate[k] > 0.02 ? 1 : rate[k] < -0.02 ? -1 : 0;
        }
        if (!pausedRef.current) { prev = vals; lastTr = tr; }
        snap.tr = tr; setUi(snap);
      }
      raf = requestAnimationFrame(loop);
    };
    raf = requestAnimationFrame(loop);
    return () => cancelAnimationFrame(raf);
  }, []);

  const pos = e => { const r = cvRef.current.getBoundingClientRect(); return [(e.clientX - r.left) * W / r.width, (e.clientY - r.top) * H / r.height]; };
  const inSalt = (x, y) => x > SB.x0 - 14 && x < SB.x1 + 14 && y > SB.top - 30 && y < BENCH;
  const inDrop = (x, y) => x > X0 - 12 && x < X1 + 12 && y > TOP - 90 && y < BOT;
  const onDown = e => {
    const sim = simRef.current, [x, y] = pos(e);
    if (inSalt(x, y) && sim.pinches > 0) {
      sim.drag = { x, y, grains: Array.from({ length: 26 }, (_, k) => ({ x: rand(-11, 11), y: rand(-6, 1), c: SALT_COLS[k % 4] })) };
      cvRef.current.setPointerCapture(e.pointerId); e.preventDefault();
    }
  };
  const onMove = e => {
    const sim = simRef.current, [x, y] = pos(e);
    sim.hover = inSalt(x, y);
    if (sim.drag) { sim.drag.x = x; sim.drag.y = y; }
    cvRef.current.style.cursor = sim.drag ? 'grabbing' : sim.hover && sim.pinches > 0 ? 'grab' : 'default';
  };
  const onUp = e => {
    const sim = simRef.current, [x, y] = pos(e);
    if (sim.drag) { if (inDrop(x, y)) sim.addScoop(x, y); sim.drag = null; }
    cvRef.current.style.cursor = 'default';
  };

  const s = ui || { m: 0, T: 0, fp: 0, ke: 75, pe: 25, pinches: MAX_SCOOPS, scoops: 0, fpTarget: 0, insulated: true };
  const stage = !s.saltAdded ? 0 : s.unstirred ? 1 : !s.done ? 2 : 3;

  const tempPanel = h(Panel, { title: 'Temperature against time', className: 'graphfig', open: tempOpen, onToggle: () => setTempOpen(o => !o) },
    h(GraphKey, { cream: !!s.cream }),
    h(TempGraph, { hist: s.hist || [], events: s.events || [], now: s.simT || 0 }));

  return h('div', { className: 'app' },
    h('header', { className: 'top' },
      h('a', { className: 'favicon-link', href: 'https://awm11.github.io/', target: '_blank', rel: 'noopener noreferrer', 'aria-label': 'Visit awm11.github.io' },
        h('img', { src: `${import.meta.env.BASE_URL}favicon.svg`, alt: '', className: 'favicon-img' })),
      h('div', { className: 'title-block' },
        h('h1', null, 'Why does salt make ice colder?'),
        h('p', { className: 'lede' }, 'Add salt to ice in an insulated beaker, stir it in, and follow where the energy goes.'))),
    h('main', { className: 'grid' },
      h('section', { className: 'lab' },
        h('div', { className: 'stage' },
          h('canvas', { ref: cvRef, onPointerDown: onDown, onPointerMove: onMove, onPointerUp: onUp, onPointerCancel: onUp,
            role: 'img', 'aria-label': `Beaker of crushed ice on a lab bench. Temperature ${fmtT(s.T)}, freezing point ${fmtT(s.fp)}. Insulation ${s.insulated ? 'on' : 'off'}.` })),
        h('div', { className: 'controls' },
          h('button', { className: 'btn primary', onClick: () => simRef.current.startStir(), disabled: s.stirring }, s.stirring ? 'Stirring\u2026' : 'Stir'),
          h('button', { className: 'btn', onClick: () => simRef.current.addScoop((X0 + X1) / 2 + rand(-40, 40), TOP), disabled: s.pinches <= 0 }, 'Add salt'),
          h('button', { className: 'btn', onClick: () => simRef.current.addCream(), disabled: !!s.cream }, s.cream ? 'Ice cream added' : 'Add ice cream'),
          h('div', { className: 'speed', role: 'group', 'aria-label': 'Play, pause and speed' },
            
            h('button', { className: 'seg pause' + (paused ? ' on' : ''), 'aria-label': paused ? 'Play' : 'Pause', title: paused ? 'Play' : 'Pause', onClick: () => setPaused(p => !p) },
              h('svg', { viewBox: '0 0 12 12', 'aria-hidden': true }, paused
                ? h('path', { d: 'M3 1.5 L10.5 6 L3 10.5 Z', fill: 'currentColor' })
                : h('path', { d: 'M2.5 1.5 h2.6 v9 h-2.6 z M6.9 1.5 h2.6 v9 h-2.6 z', fill: 'currentColor' }))),
            h('span', { className: 'speedlbl' }, 'Speed'),
            [1, 2, 4].map(v => h('button', { key: v, className: 'seg' + (speed === v ? ' on' : ''), 'aria-pressed': speed === v, onClick: () => setSpeed(v) }, v + '\u00D7'))),
          h('label', { className: 'swgroup', title: s.insulated ? 'Insulation on: a closed system' : 'Insulation off: energy leaks in from the room' },
            h('span', { className: 'insw' },
              h('input', { type: 'checkbox', checked: s.insulated, 'aria-label': s.insulated ? 'Insulation on' : 'Insulation off',
                onChange: () => { simRef.current.insulated = !simRef.current.insulated; setUi(simRef.current.snapshot()); } }),
              h('span', { className: 'track', 'aria-hidden': true })),
            h('span', { className: 'swlabel' }, 'Insulated')),
          h('button', { className: 'btn ghost', onClick: () => { simRef.current.reset(); setSpeed(1); setPaused(false); } }, 'Reset')),
        tempOpen && tempPanel,
        h('div', { className: 'story' },
          h('ol', { className: 'steps' }, STEPS.map((t, i) =>
            h('li', { key: i, className: i < stage ? 'done' : i === stage ? 'now' : '' }, h('span', { className: 'num' }, i < stage ? '\u2713' : i + 1), t))),
          h('div', { className: 'explain', 'aria-live': 'polite' }, explain(stage, s).concat(creamNotes(s)).map((p, i) => h('p', { key: stage + '-' + i }, p)))),
        h('footer', { className: 'foot' },
          h('p', null, 'Model assumptions: the beaker is perfectly insulated and the whole beaker melts evenly rather than shard by shard. Each scoop of salt lowers the freezing point by the same amount; six scoops reach \u221221.1 \u00B0C, the lowest freezing point salt water can have (about 23% salt). The ice starts at \u22122 \u00B0C. The ice cream mix has about a fifth of the mass of the ice, starts at 5 \u00B0C and freezes at about \u22123 \u00B0C.'))),
      h('aside', { className: 'panel' },
        h(Panel, { title: 'Energy of the particles', startOpen: true },
          h('p', { className: 'eq' }, 'Internal energy = ', h('span', { className: 'k' }, 'kinetic'), ' + ', h('span', { className: 'p' }, 'potential')),
          s.cream && h('p', { className: 'note' }, 'Striped bars are the ice cream mix.'),
          h(EnergyBars, { ke: s.ke, pe: s.pe, cream: s.cream, tr: s.tr }),
          h('p', { className: 'note' }, s.cream
            ? 'Energy flows from the ice cream mix into the water and ice. Each store can change, but the total stays the same.'
            : (s.insulated ? 'As ice melts, energy moves from kinetic to potential at exactly the same rate. The total stays the same.'
              : 'With the insulation off, energy leaks in from the room, so the total keeps rising instead of staying fixed.'))),
        !tempOpen && tempPanel,
        h(Panel, { title: 'What\u2019s in the beaker', startOpen: true },
          h('p', { className: 'note' }, 'By mass'),
          h(Pie, { water: s.m })),
        h('div', { className: 'bottom-block' },
          h('a', { className: 'more-sims', href: 'https://awm11.github.io/', target: '_blank', rel: 'noopener noreferrer' },
            h('img', { src: `${import.meta.env.BASE_URL}favicon.svg`, alt: '', className: 'more-sims-icon' }),
            h('span', null, 'See other simulations')),
          h('p', { className: 'more-sims-note' }, 'Click the icon above to explore other interactive physics simulations like this one, or below to support the project.'),
          h('div', { className: 'coffee-row' }, h(BuyMeCoffeeButton))))));
}

export default App;