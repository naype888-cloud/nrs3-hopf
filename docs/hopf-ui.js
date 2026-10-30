// RS^N³ · Hopf — tablas y control de la página.
"use strict";
// ---------- tablas ----------
const LEDGER = [
  ["Robertson 1934 en los 8 observables de la caja, todo estado", "robertson_det_four", "RobertsonFourAxes"],
  ["en c, det Σ = (Π C(dᵢ))² |det Ω|; igualdad ⟺ cada eje con 2 o 3; límite (C_N^∞)⁸", "det_covMatrix_maxCurrentState4, det_eq_iff, tendsto_ratio", "RobertsonFourAxes"],
  ["con cualquier par en w, Σ y Ω diagonales por bloques en estados producto", "covMatrix_box, imMatrix_box", "FourAxes"],
  ["x, y, z dentro de la caja son el cubo, lleve lo que lleve w", "covMatrix_xyz, imMatrix_xyz", "CubeInBox"],
  ["det Σ₈ = det Σ₆ · det Σ_w, |det Ω₈| = |det Ω₆| · |det Ω_w|", "det_covMatrix_box, abs_det_imMatrix_box", "CubeInBox"],
  ["w cerrado en su banda y det Σ₆ > 0 ⇒ la caja es estricta", "robertson_det_box_strict", "CubeInBox"],
  ["el cubo 3×3×3 satura en c y la caja con w cerrado no", "cube_three_saturates, cube_saturates_box_strict", "CubeInBox"],
  ["eje cerrado d = 3: incertidumbre mínima ⇒ |⟨K⟩| ≤ 1; c = √6/2; umbral √(2/3)", "abs_tension_le_of_saturated, tension_maxState, threshold_eq", "ClosedThree, ClosedThreeBand"],
  ["tiempo propio > 0 en la banda del eje cerrado; = 0 en el abierto de 3", "properTime_pos_of_speed, properTime_open_three", "ClosedThreeCone"],
  ["la c del eje cerrado tiende a 1, cargada por la costura", "tendsto_cMax", "ClosedAxis"],
  ["en la costura, razón √2 para todo d; su velocidad tiende a c", "ratio_seamState, tendsto_speed_seamState", "ClosedAxisQuantum"],
  ["defecto de la fibra cerrada en su banda, para todo estado enredado", "gramDefect_pos_of_band, gramDefect_box_pos", "ClosedAxisEntangled"],
  ["igualdad con n ejes y un eje con defecto ⇒ Σσᵢ[Tᵢ, Pᵢ]Φ = 0", "exists_sigma_of_det_eq", "RobertsonEquality"],
  ["los ejes de la caja conmutan; igualdad en la caja ⇒ relación entre tensiones", "boxPairs_comm, BoxEquality.exists_sigma_of_det_eq", "BoxCommute, BoxEquality"],
  ["[P, [T°, P]] invertible; T° invertible; núcleo (1, −2, 1)", "PC_eq, eq_zero_of_PC, eq_zero_of_Tc, TC_eq", "ClosedAxisAlgebra"],
  ["k fibras apiladas: det Σ = F^k |det Ω| con F > 1", "closed_stack, one_lt_closedFactor", "StackedFibers"],
  ["Yang–Mills: los pasos de los 4 ejes conmutan, plaquetas en los 6 planos; ley de Gauss y gap de acoplamiento fuerte a volumen finito", "step_comm, ham_gauge, gap_ham", "HopfYangMills, KogutSusskind, KogutSusskindGap"],
  ["acción de Wilson: invariante de gauge, ≥ 0, cero ⟺ holonomía trivial (también en los 32 triángulos de la celda de 16)", "action_gauge, action_nonneg, triangleAction_eq_zero_iff", "Cell16GaugeWilson"],
  ["estado base positivo, Harnack uniforme en el volumen, unicidad", "KogutSusskindHarnack, KogutSusskindUnique", "KogutSusskindGround, KogutSusskindHarnack, KogutSusskindUnique"],
  ["Dirac en ℤ³ × w: gap de masa 1/2 y velocidad ≤ 1/φ para todo estado", "abs_energy_ge, abs_velocity_le_inv_goldenRatio", "LatticeFiberDirac"],
  ["con espaciamiento a > 0: gap físico ħc/(2a); si un valor propio tiene E ≤ Emax, a ≥ ħc/(2 Emax) (Emax es hipótesis)", "abs_physical_energy_ge, spacing_floor, no_zero_spacing", "DiracFloor"],
  ["el defecto de Robertson δ = (Π C)² − 1 es un tiempo propio: δ > 0 desde 4 posiciones por eje, C₄⁸ − 1 ≤ δ < (C_N^∞)⁸ − 1, sin depender de la caja", "defect_pos, defect_ge, defect_lt, properTime_band", "ProperTimeBand"],
  ["el Hamiltoniano de red es una matriz hermitiana: su medida térmica es atómica, nunca una densidad (mitad de red del dilema de Poincaré)", "ham_thermal_ne_withDensity, thermal_ne_withDensity", "PlanckBridge"],
];
const NUMERIC = [
  ["mínimo de det Σ/|det Ω| con x, y, z = 2×2×2 y la fibra con |t| > 1.05, estados enredados", "1.008", "prueba para todo estado (análogo de D49t)"],
  ["lo mismo con 3×3×3", "1.014", "ídem"],
  ["lo mismo con 2×3×4", "1.014", "ídem"],
  ["la fibra sola con |t| > 1.05", "1.005", "—"],
  ["umbral v* del eje cerrado con d = 4, 6, 10", "0.567, 0.373, 0.210 (≈ 2/d)", "prueba para d ≥ 4"],
  ["razón en la corriente máxima exacta del eje cerrado, d = 160", "1.4186 → √2", "el estado exacto (la costura ya está en Lean)"],
  ["banda del defecto δ con 4 ejes abiertos de 4 o más posiciones: cota inferior C₄⁸ − 1 y tope (C_N^∞)⁸ − 1", "0.070 ≤ δ < 1.768", "Lean (ProperTimeBand); δ no se mide en metros: a es la unidad"],
];
const COMPARE = [
  ["cuanto desde", "d = 4", "d = 3", "Lean"],
  ["ancho de la banda en el primer d", "0.073", "0.184", "Lean"],
  ["la banda al crecer d", "se angosta hacia c", "se ensancha (v* ≈ 2/d)", "numérico"],
  ["cociente por eje en el límite", "(C_N^∞)² ≈ 1.29", "2 (exacto en la costura)", "Lean"],
  ["[P, [T, P]] y T", "se anulan si TΦ = 0", "invertibles", "Lean"],
];
function fillTables() {
  $("ledger").querySelector("tbody").innerHTML = LEDGER.map(([a, b, c]) =>
    `<tr><td>${a}</td><td><code>${b}</code></td><td><code>${c}</code></td></tr>`).join("");
  $("numeric").querySelector("tbody").innerHTML = NUMERIC.map(([a, b, c]) =>
    `<tr><td>${a}</td><td class="num">${b}</td><td>${c}</td></tr>`).join("");
  $("compare").querySelector("tbody").innerHTML = COMPARE.map(([a, b, c, d]) =>
    `<tr><td>${a}</td><td class="num">${b}</td><td class="num">${c}</td><td><span class="tag ${d === "Lean" ? "lean" : "num"}">${d}</span></td></tr>`).join("");
}

// ---------- control ----------
function labels() {
  for (const id of ["dx", "dy", "dz", "k"]) $("v" + id).textContent = $(id).value;
  $("vvw").textContent = fiberState(+$("vw").value).v.toFixed(2);
  const on = $("fiberOn").getAttribute("aria-pressed") === "true";
  $("lv").classList.toggle("off", !on); $("lk").classList.toggle("off", !on);
  $("fiberOn").textContent = on ? "fibra w cerrada: encendida" : "fibra w cerrada: apagada";
}
function draw() {
  const r = st.res || (st.res = compute());
  badges(r); drawBox(r); drawMats(r); drawBand(r); drawStack(r);
}
function update() { labels(); st.res = compute(); draw(); }

for (const id of ["dx", "dy", "dz", "vw", "k"]) $(id).addEventListener("input", update);
$("fiberOn").onclick = () => {
  const b = $("fiberOn"); b.setAttribute("aria-pressed", b.getAttribute("aria-pressed") !== "true"); update();
};
document.querySelectorAll("[data-preset]").forEach(b => b.onclick = () => {
  const [a, c, d] = b.dataset.preset.split(",");
  $("dx").value = a; $("dy").value = c; $("dz").value = d; update();
});
$("band").addEventListener("pointermove", bandHover);
$("band").addEventListener("pointerleave", () => { const t = $("band").parentElement.querySelector(".tip"); if (t) t.hidden = true; });
$("stack").addEventListener("pointermove", stackHover);
$("stack").addEventListener("pointerleave", () => { const t = $("stack").parentElement.querySelector(".tip"); if (t) t.hidden = true; });
(function () {
  const cv = $("box"); let drag = null;
  cv.addEventListener("pointerdown", e => { drag = [e.clientX, e.clientY, st.yaw, st.pitch]; cv.setPointerCapture(e.pointerId); });
  cv.addEventListener("pointermove", e => {
    if (!drag) return;
    st.yaw = drag[2] + (e.clientX - drag[0]) * 0.01;
    st.pitch = Math.max(-1.2, Math.min(1.2, drag[3] + (e.clientY - drag[1]) * 0.01));
    drawBox(st.res);
  });
  cv.addEventListener("pointerup", () => { drag = null; });
})();
window.addEventListener("resize", draw);
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", draw);

// la fibra gira a la velocidad elegida
const still = matchMedia("(prefers-reduced-motion: reduce)").matches;
function tick() {
  if (st.res && st.res.on) { st.phase += 0.06 * st.res.speed; drawBox(st.res); }
  if (!still) requestAnimationFrame(tick);
}
fillTables(); update(); if (!still) requestAnimationFrame(tick);
