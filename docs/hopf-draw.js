// NRS³ · Hopf — estado compartido, cálculo de la caja y dibujo de los paneles.
"use strict";
const H = window.Hopf, DATA = window.HOPF_DATA;
const $ = id => document.getElementById(id);
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const C_CLOSED = Math.sqrt(6) / 2;
const st = { yaw: 0.65, pitch: 0.38, phase: 0, res: null };

// ---------- tema ----------
$("theme").onclick = () => {
  const r = document.documentElement, dark = r.dataset.theme ? r.dataset.theme === "dark"
    : matchMedia("(prefers-color-scheme: dark)").matches;
  r.dataset.theme = dark ? "light" : "dark"; draw();
};

// ---------- cálculo ----------
function fiberState(idx) {
  const row = DATA.fiber.rows[idx];
  return { v: row[0], psi: [[row[1], row[2]], [row[3], row[4]], [row[5], row[6]]] };
}

function compute() {
  const ds = [+$("dx").value, +$("dy").value, +$("dz").value];
  const on = $("fiberOn").getAttribute("aria-pressed") === "true";
  const k = +$("k").value;
  const vis = ds.map(d => {
    const psi = H.openMaxState(d);
    return { d, psi, b: H.block(H.openPair(d), psi) };
  });
  const fs = fiberState(+$("vw").value);
  const fb = H.block(H.closedPair, fs.psi);
  const ratio = b => b.detS / b.absDetO;
  let detS = vis.reduce((p, a) => p * a.b.detS, 1);
  let absO = vis.reduce((p, a) => p * a.b.absDetO, 1);
  const cube = { detS, absO, ratio: detS / absO };
  const F = ratio(fb);
  if (on) { detS *= Math.pow(fb.detS, k); absO *= Math.pow(fb.absDetO, k); }
  return { ds, on, k, vis, fs, fb, F, cube, detS, absO, ratio: detS / absO,
    speed: Math.abs(fb.tension) / C_CLOSED };
}

// ---------- insignias ----------
const fmt = (x, n = 4) => Math.abs(x) >= 1e-3 && Math.abs(x) < 1e4 ? x.toFixed(n) : x.toExponential(3);
function badges(r) {
  const out = [];
  const axes = ["x", "y", "z"];
  r.vis.forEach((a, i) => out.push(`<div class="badge"><span class="k">C(${a.d})² en ${axes[i]}</span>${fmt(a.b.detS / a.b.absDetO, 5)}</div>`));
  if (r.on) out.push(`<div class="badge"><span class="k">factor de w a ${fmt(r.speed, 3)} c</span>F = ${fmt(r.F, 5)}${r.k > 1 ? ` · F<sup>${r.k}</sup> = ${fmt(Math.pow(r.F, r.k), 5)}` : ""}</div>`);
  out.push(`<div class="badge"><span class="k">det Σ${r.on ? "₈" : "₆"}</span>${fmt(r.detS)}</div>`);
  out.push(`<div class="badge"><span class="k">|det Ω${r.on ? "₈" : "₆"}|</span>${fmt(r.absO)}</div>`);
  const strict = r.ratio > 1 + 1e-9;
  out.push(`<div class="badge ${strict ? "ok" : "no"}"><span class="k">det Σ / |det Ω|</span><span class="verdict">${fmt(r.ratio, 6)} · ${strict ? "estricto <" : "igualdad ="}</span></div>`);
  $("badges").innerHTML = out.join("");
}

// ---------- utilidades de canvas ----------
function setup(cv) {
  const dpr = window.devicePixelRatio || 1, w = cv.clientWidth, h = cv.clientHeight;
  cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
  const g = cv.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
  return { g, w, h };
}
function phaseColor(re, im) {
  const a = (Math.atan2(im, re) + Math.PI) / (2 * Math.PI);
  return `hsl(${Math.round(a * 360)}, 60%, 52%)`;
}

// ---------- la caja ----------
function drawBox(r) {
  const { g, w, h } = setup($("box"));
  const [dx, dy, dz] = r.ds, s = Math.min(w, h) * 0.6 / Math.max(dx, dy, dz, 3);
  const cy = Math.cos(st.yaw), sy = Math.sin(st.yaw), cp = Math.cos(st.pitch), sp = Math.sin(st.pitch);
  const proj = (x, y, z) => {
    const X = x * cy - z * sy, Z = x * sy + z * cy, Y = y * cp - Z * sp, D = y * sp + Z * cp;
    return [w * 0.40 + X * s, h * 0.56 - Y * s, D];
  };
  const pts = [];
  const [px, py, pz] = r.vis.map(a => a.psi);
  for (let i = 0; i < dx; i++) for (let j = 0; j < dy; j++) for (let l = 0; l < dz; l++) {
    const p = proj(i - (dx - 1) / 2, j - (dy - 1) / 2, l - (dz - 1) / 2);
    const a = px[i], b = py[j], c = pz[l];
    const ab = [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
    const amp = [ab[0] * c[0] - ab[1] * c[1], ab[0] * c[1] + ab[1] * c[0]];
    pts.push({ p, n: amp[0] * amp[0] + amp[1] * amp[1], amp });
  }
  pts.sort((u, v) => u.p[2] - v.p[2]);
  const nmax = Math.max(...pts.map(q => q.n));
  g.strokeStyle = css("--grid"); g.lineWidth = 1;
  for (const q of pts) {
    const rad = 2 + 9 * Math.sqrt(q.n / nmax);
    g.beginPath(); g.arc(q.p[0], q.p[1], rad, 0, 2 * Math.PI);
    g.fillStyle = phaseColor(q.amp[0], q.amp[1]); g.fill();
  }
  // ejes
  g.font = "12px system-ui"; g.fillStyle = css("--muted");
  const L = Math.max(dx, dy, dz) / 2 + 0.6;
  [["x", [L, 0, 0]], ["y", [0, L, 0]], ["z", [0, 0, L]]].forEach(([n, v]) => {
    const p = proj(...v); g.fillText(n, p[0], p[1]);
  });
  // la fibra w
  const R = Math.min(w, h) * 0.13, cx = w - R - 22, cyy = R + 30;
  g.strokeStyle = r.on ? css("--s-closed") : css("--grid"); g.lineWidth = 2;
  g.beginPath(); g.arc(cx, cyy, R, 0, 2 * Math.PI); g.stroke();
  g.fillStyle = css("--ink2"); g.fillText(r.on ? "w cerrada" : "w apagada", cx - R, cyy + R + 18);
  if (r.on) {
    const psi = r.fs.psi, nm = Math.max(...psi.map(z => z[0] * z[0] + z[1] * z[1]));
    psi.forEach((z, j) => {
      const ang = -Math.PI / 2 + j * 2 * Math.PI / 3, n = z[0] * z[0] + z[1] * z[1];
      g.beginPath(); g.arc(cx + R * Math.cos(ang), cyy + R * Math.sin(ang), 3 + 7 * Math.sqrt(n / nm), 0, 2 * Math.PI);
      g.fillStyle = phaseColor(z[0], z[1]); g.fill();
    });
    const a = st.phase;
    g.beginPath(); g.arc(cx + (R + 8) * Math.cos(a), cyy + (R + 8) * Math.sin(a), 3, 0, 2 * Math.PI);
    g.fillStyle = css("--s-closed"); g.fill();
  }
}

// ---------- las matrices ----------
function drawMats(r) {
  const { g, w, h } = setup($("mats"));
  const blocks = r.vis.map(a => a.b);
  if (r.on) blocks.push(r.fb);
  const n = blocks.length * 2;
  const names = ["Tx", "Px", "Ty", "Py", "Tz", "Pz", "Tw", "Pw"].slice(0, n);
  const cell = Math.min((w / 2 - 34) / n, (h - 40) / n);
  const draw1 = (x0, title, get) => {
    g.fillStyle = css("--ink2"); g.font = "600 13px system-ui"; g.fillText(title, x0, 16);
    let mx = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) mx = Math.max(mx, Math.abs(get(i, j)));
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const x = x0 + j * cell, y = 26 + i * cell, same = Math.floor(i / 2) === Math.floor(j / 2);
      const v = get(i, j);
      if (!same) {
        g.strokeStyle = css("--green"); g.lineWidth = 1.2;
        g.strokeRect(x + 2, y + 2, cell - 4, cell - 4);
        continue;
      }
      const t = mx ? Math.abs(v) / mx : 0;
      g.fillStyle = v >= 0 ? css("--blue") : css("--orange");
      g.globalAlpha = 0.15 + 0.85 * t; g.fillRect(x + 1, y + 1, cell - 2, cell - 2); g.globalAlpha = 1;
    }
    g.fillStyle = css("--muted"); g.font = "10px system-ui";
    names.forEach((s, i) => g.fillText(s, x0 - 22, 26 + i * cell + cell * 0.6));
  };
  const val = (which) => (i, j) => {
    const bi = Math.floor(i / 2), bj = Math.floor(j / 2);
    if (bi !== bj) return 0;
    return blocks[bi][which][i % 2][j % 2];
  };
  draw1(28, "Σ", val("sigma"));
  draw1(w / 2 + 28, "Ω", val("omega"));
  g.fillStyle = css("--muted"); g.font = "11px system-ui";
  g.fillText("azul +, naranja −, intensidad = |valor|" + (r.on && r.k > 1 ? `; la fibra se repite ${r.k} veces` : ""), 28, h - 6);
}

// ---------- la banda ----------
const bandGeom = {};
function drawBand(r) {
  const cv = $("band"), { g, w, h } = setup(cv);
  const m = { l: 46, r: 14, t: 14, b: 34 }, W = w - m.l - m.r, Hh = h - m.t - m.b;
  const ymin = 1, ymax = 1.25;
  const X = v => m.l + v * W, Y = F => m.t + (1 - (Math.min(F, ymax) - ymin) / (ymax - ymin)) * Hh;
  Object.assign(bandGeom, { m, W, Hh, X, Y, w, h });
  g.strokeStyle = css("--grid"); g.lineWidth = 1; g.fillStyle = css("--muted"); g.font = "11px system-ui";
  for (const F of [1, 1.05, 1.1, 1.15, 1.2, 1.25]) {
    g.beginPath(); g.moveTo(m.l, Y(F)); g.lineTo(m.l + W, Y(F)); g.stroke(); g.fillText(F.toFixed(2), 8, Y(F) + 4);
  }
  for (const v of [0, 0.25, 0.5, 0.75, 1]) g.fillText(v.toFixed(2), X(v) - 10, h - 16);
  g.fillText("velocidad / c", m.l + W - 78, h - 2);
  const series = [
    { key: "open3", col: css("--s-open3"), dash: [2, 3], label: "abierto d = 3" },
    { key: "open4", col: css("--s-open4"), dash: [6, 4], label: "abierto d = 4" },
    { key: "closed3", col: css("--s-closed"), dash: [], label: "cerrado d = 3" },
  ];
  for (const s of series) {
    const d = DATA.band[s.key];
    g.strokeStyle = s.col; g.lineWidth = 2; g.setLineDash(s.dash); g.beginPath();
    d.v.forEach((v, i) => { const x = X(v), y = Y(d.F[i]); i ? g.lineTo(x, y) : g.moveTo(x, y); });
    g.stroke(); g.setLineDash([]);
  }
  // leyenda arriba a la izquierda, con el estilo de cada línea
  series.slice().reverse().forEach((s, i) => {
    const y = m.t + 10 + i * 16;
    g.strokeStyle = s.col; g.lineWidth = 2; g.setLineDash(s.dash);
    g.beginPath(); g.moveTo(m.l + 8, y - 4); g.lineTo(m.l + 30, y - 4); g.stroke(); g.setLineDash([]);
    g.fillStyle = css("--ink2"); g.fillText(s.label, m.l + 36, y);
  });
  // umbrales, rotulados a la izquierda de su línea
  const thr = [[Math.sqrt(2 / 3), "v* cerrado = √(2/3)"], [3 * (Math.sqrt(5) - 1) / 4, "v* abierto d = 4"]];
  g.setLineDash([3, 3]); g.strokeStyle = css("--muted");
  thr.forEach(([v, lab], i) => {
    g.beginPath(); g.moveTo(X(v), m.t); g.lineTo(X(v), m.t + Hh); g.stroke();
    g.fillStyle = css("--muted");
    const tw = g.measureText(lab).width;
    g.fillText(lab, X(v) - tw - 4, m.t + Hh * (0.45 + 0.1 * i));
  });
  g.setLineDash([]);
  if (r.on) {
    g.beginPath(); g.arc(X(r.fs.v), Y(r.F), 5, 0, 2 * Math.PI);
    g.fillStyle = css("--s-closed"); g.fill(); g.strokeStyle = css("--panel"); g.lineWidth = 2; g.stroke();
  }
}
function bandHover(ev) {
  const tip = ensureTip($("band"));
  const rect = $("band").getBoundingClientRect(), x = ev.clientX - rect.left;
  const v = Math.max(0, Math.min(1, (x - bandGeom.m.l) / bandGeom.W));
  const pick = key => {
    const d = DATA.band[key]; let best = 0;
    d.v.forEach((u, i) => { if (Math.abs(u - v) < Math.abs(d.v[best] - v)) best = i; });
    return [d.v[best], d.F[best]];
  };
  const [vv, fc] = pick("closed3"), [, f4] = pick("open4"), [, f3] = pick("open3");
  tip.innerHTML = `v = ${vv.toFixed(2)} c<br>cerrado d=3: ${fc.toFixed(4)}<br>abierto d=4: ${f4.toFixed(4)}<br>abierto d=3: ${f3.toFixed(4)}`;
  tip.style.left = Math.min(x + 12, rect.width - 150) + "px"; tip.style.top = "30px"; tip.hidden = false;
}
function ensureTip(cv) {
  let t = cv.parentElement.querySelector(".tip");
  if (!t) { t = document.createElement("div"); t.className = "tip"; t.hidden = true; cv.parentElement.appendChild(t); }
  return t;
}

// ---------- la pila de fibras ----------
const stackGeom = {};
function drawStack(r) {
  const { g, w, h } = setup($("stack"));
  const m = { l: 52, r: 14, t: 16, b: 34 }, W = w - m.l - m.r, Hh = h - m.t - m.b, K = 12;
  const vals = []; for (let k = 0; k <= K; k++) vals.push(r.cube.ratio * Math.pow(r.F, k));
  const ymax = Math.max(...vals) * 1.05;
  const bw = W / (K + 1);
  Object.assign(stackGeom, { m, bw, vals });
  g.strokeStyle = css("--grid"); g.fillStyle = css("--muted"); g.font = "11px system-ui";
  for (let t = 0; t <= 4; t++) {
    const yv = ymax * t / 4, y = m.t + Hh - Hh * t / 4;
    g.beginPath(); g.moveTo(m.l, y); g.lineTo(m.l + W, y); g.stroke(); g.fillText(yv.toFixed(2), 6, y + 4);
  }
  vals.forEach((v, k) => {
    const x = m.l + k * bw + 2, bh = Hh * v / ymax, y = m.t + Hh - bh;
    g.fillStyle = k === (r.on ? r.k : 0) ? css("--s-closed") : css("--grid");
    const rr = Math.min(4, (bw - 4) / 2);
    g.beginPath(); g.moveTo(x, m.t + Hh); g.lineTo(x, y + rr); g.quadraticCurveTo(x, y, x + rr, y);
    g.lineTo(x + bw - 4 - rr, y); g.quadraticCurveTo(x + bw - 4, y, x + bw - 4, y + rr);
    g.lineTo(x + bw - 4, m.t + Hh); g.closePath(); g.fill();
    g.fillStyle = css("--muted"); g.fillText(String(k), x + bw / 2 - 5, h - 16);
  });
  g.fillText("fibras cerradas k", m.l + W - 96, h - 2);
  g.fillStyle = css("--ink2");
  g.fillText(`cubo ${fmt(r.cube.ratio, 4)} × F^k, F = ${fmt(r.F, 4)}`, m.l + 4, m.t + 12);
}
function stackHover(ev) {
  const cv = $("stack"), tip = ensureTip(cv), rect = cv.getBoundingClientRect(), x = ev.clientX - rect.left;
  const k = Math.max(0, Math.min(12, Math.floor((x - stackGeom.m.l) / stackGeom.bw)));
  tip.innerHTML = `k = ${k}<br>det Σ / |det Ω| = ${fmt(stackGeom.vals[k], 5)}`;
  tip.style.left = Math.min(x + 12, rect.width - 150) + "px"; tip.style.top = "30px"; tip.hidden = false;
}

