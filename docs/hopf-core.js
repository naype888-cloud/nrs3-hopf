// NRS³ · Hopf — núcleo numérico: x, y, z abiertos y la fibra w cerrada.
// Vectores complejos como arreglos de [re, im]. Todo se calcula en el navegador con las mismas
// matrices que Lean: T_d = A_d / ρ_d y P_d en [−1, 1] en los ejes abiertos; T° = (J − I)/2 y
// P₃ = diag(−1, 0, 1) en la fibra cerrada.
"use strict";
(function () {
  const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
  const conj = a => [a[0], -a[1]];
  const add = (a, b) => [a[0] + b[0], a[1] + b[1]];
  const scal = (s, a) => [s * a[0], s * a[1]];

  function matvec(M, v) {
    return M.map(row => row.reduce((acc, m, j) => add(acc, scal(m, v[j])), [0, 0]));
  }
  function inner(u, v) { // ⟪u, v⟫, conjugado en el primero
    return u.reduce((acc, x, j) => add(acc, cmul(conj(x), v[j])), [0, 0]);
  }
  function normalize(v) {
    const n = Math.sqrt(v.reduce((s, x) => s + x[0] * x[0] + x[1] * x[1], 0));
    return v.map(x => scal(1 / n, x));
  }

  function openPair(d) {
    const rho = 2 * Math.cos(Math.PI / (d + 1));
    const T = [], P = [];
    for (let i = 0; i < d; i++) {
      T.push([]); P.push([]);
      for (let j = 0; j < d; j++) {
        T[i].push(Math.abs(i - j) === 1 ? 1 / rho : 0);
        P[i].push(i === j ? (d === 1 ? 0 : -1 + 2 * i / (d - 1)) : 0);
      }
    }
    return { T, P };
  }
  const closedPair = {
    T: [[0, 0.5, 0.5], [0.5, 0, 0.5], [0.5, 0.5, 0]],
    P: [[-1, 0, 0], [0, 0, 0], [0, 0, 1]],
  };

  // Estado de corriente máxima del eje abierto: ψ_j = i^j sin((j + 1)π/(d + 1)).
  function openMaxState(d) {
    const ip = [[1, 0], [0, 1], [-1, 0], [0, -1]];
    const v = [];
    for (let j = 0; j < d; j++) v.push(scal(Math.sin((j + 1) * Math.PI / (d + 1)), ip[j % 4]));
    return normalize(v);
  }

  // Las estadísticas de un par en un estado unitario: Σ y Ω del bloque 2 × 2.
  function block(pair, psi) {
    const Tp = matvec(pair.T, psi), Pp = matvec(pair.P, psi);
    const mT = inner(psi, Tp)[0], mP = inner(psi, Pp)[0];
    const cT = Tp.map((x, j) => add(x, scal(-mT, psi[j])));
    const cP = Pp.map((x, j) => add(x, scal(-mP, psi[j])));
    const VT = inner(cT, cT)[0], VP = inner(cP, cP)[0];
    const g = inner(cT, cP);
    const om = g[1];               // Ω_TP = Im ⟪c_T, c_P⟫
    return {
      VT, VP, cov: g[0], om, tension: -2 * om, mT, mP,
      detS: VT * VP - g[0] * g[0], absDetO: om * om,
      sigma: [[VT, g[0]], [g[0], VP]], omega: [[0, om], [-om, 0]],
    };
  }

  window.Hopf = { openPair, closedPair, openMaxState, block, normalize };
})();
