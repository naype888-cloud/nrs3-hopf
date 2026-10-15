# NRS³ · Hopf — cuatro ejes espaciales

**El mismo cuanto en cuatro ejes.** La caja `dx × dy × dz × dw` lleva un par `(T_d, P_d)` por
eje: ocho observables. Robertson 1934, `|det Ω| ≤ det Σ`, vale para todo estado. En el estado de
corriente máxima (la `c` del sistema) el cociente es

  `det Σ / |det Ω| = (C_Nava(dx) C_Nava(dy) C_Nava(dz) C_Nava(dw))²`.

Vale `1` exactamente cuando cada eje tiene 2 o 3 posiciones. Es estrictamente mayor que `1` con
4 o más en cada eje (`C(4)⁸ ≈ 1.070` en `4 × 4 × 4 × 4`). Ninguna caja alcanza
`C_∞⁸ = (π²/3 − 2)⁴ ≈ 2.768`, y el cociente tiende a ese valor cuando los cuatro ejes crecen,
cada uno por su lado (Szegő, `D8`; monotonía, `D9`).

**[▶ Pruébalo: x, y, z abiertos con la fibra w cerrada, los determinantes y la banda](https://naype888-cloud.github.io/nrs3-hopf/)**
(local: `docs/index.html`)

Lean 4 sobre [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone)
y [`nava-robertson-schrodinger`](https://github.com/naype888-cloud/nava-robertson-schrodinger)
(D49c es el caso de tres ejes).

## Resultados

| Enunciado | Lean |
|---|---|
| los productos internos se factorizan en los cuatro ejes | `FourAxes.inner_prod4` |
| en estados producto `Σ` y `Ω` son diagonales por bloques, un bloque `2 × 2` por eje | `FourAxes.covMatrix_prod4`, `FourAxes.imMatrix_prod4` |
| el bloque de `Ω` de un eje tiene determinante `t²/4` | `FourAxes.det_imMatrix_pair` |
| Robertson 1934 para los ocho observables, en todo estado | `RobertsonFourAxes.robertson_det_four` |
| `det Σ = Π (s_i + t_i²/4)`, `\|det Ω\| = Π t_i²/4` en estados producto | `det_covMatrix_prod4`, `abs_det_imMatrix_prod4` |
| excedente positivo en los cuatro ejes ⇒ estricto | `robertson_det_prod4_strict` |
| en `c`: `det Σ = (Π C_Nava(d_i))² · \|det Ω\|` | `det_covMatrix_maxCurrentState4` |
| igualdad ⟺ cada eje con 2 o 3 posiciones | `det_eq_iff` |
| estricto con 4 o más posiciones en cada eje | `robertson_det_maxCurrentState4_strict` |
| `C_∞⁸ = (π²/3 − 2)⁴` | `CoherenceConstantInf_pow_eight` |
| ninguna caja alcanza `C_∞⁸` | `ratio_lt_inf` |
| el cociente tiende a `C_∞⁸` al crecer los cuatro ejes | `tendsto_ratio` |

## El eje cerrado con tres posiciones

Cerrar el eje es agregar el enlace `{0, 2}` (`D16e`): `T° = (J − I)/2`, normalizado por su
radio espectral `2`, con la misma `P₃ = diag(−1, 0, 1)`. En el eje abierto, `d = 3` satura en
el cono y no tiene banda (`D44`). En el eje cerrado sí la tiene:

| Enunciado | Lean |
|---|---|
| un estado de incertidumbre mínima que se mueve cumple `2ψ₀ψ₂ = ψ₁(ψ₀ + ψ₂)` | `ClosedThree.relation_of_saturated` |
| en esa cuádrica, `\|ζ\|²(‖ψ‖² ∓ ⟨K⟩) = (a² + a + b² + 1 ∓ 2b)² + 3a²`, así que `\|⟨K⟩\| ≤ ‖ψ‖²` | `abs_tension_le_of_relation` |
| todo estado de incertidumbre mínima tiene `\|⟨K⟩\| ≤ ‖ψ‖²` | `abs_tension_le_of_saturated` |
| la `c` del eje cerrado: `\|⟨K⟩\| ≤ √6/2`, alcanzada | `abs_tension_le_max`, `tension_maxState` |
| `(1 + i, 2, 1 − i)/(2√2)` es de incertidumbre mínima con `⟨K⟩ = 1` | `saturated_satState`, `tension_satState` |
| `1` es la mayor tensión de incertidumbre mínima | `isGreatest_satTension` |
| umbral `v* = 1/(√6/2) = √(2/3) < 1`: la banda `(√(2/3), 1]` no está vacía | `threshold_eq`, `threshold_lt_one` |
| arriba de `√(2/3)` todo estado unitario tiene excedente positivo | `surplus_pos_of_speed` |

| el intervalo del cuadrivector de incertidumbre es el excedente de Robertson–Schrödinger | `interval_eq_gramDefectAt` |
| en la banda, todo estado unitario tiene tiempo propio `τ > 0` | `properTime_pos_of_speed` |
| la corriente máxima del eje cerrado tiene `τ > 0`; en el eje abierto con 3 posiciones `τ = 0` | `properTime_maxState_pos`, `properTime_open_three` |

Cerrar el eje agrega cuanto: con 3 posiciones abierto no hay banda ni tiempo propio en `c`;
cerrado, sí. El tiempo propio nunca es negativo (`UncertaintyCone.mem_futureCone`).

## La `c` del eje cerrado tiende a `1`

Con `d` posiciones el transporte cerrado es `(A_d + S)/2`: el camino abierto más la costura `S`,
el enlace de la última posición a la primera. La posición sigue en `[−1, 1]`, así que la
costura salta todo el rango mientras cada enlace abierto avanza `2/(d − 1)`.

| Enunciado | Lean |
|---|---|
| `⟨K⟩ = (ρ_d/2) ⟨K_d⟩ − 2 Im(ψ̄₀ ψ_{d−1})`: parte abierta más costura | `ClosedAxis.tension_eq` |
| `\|⟨K⟩\| ≤ 1 + 2/(d − 1)` en todo estado unitario | `ClosedAxis.abs_tension_le` |
| el estado de la costura `(e₀ − i e_{d−1})/√2` alcanza `⟨K⟩ = 1` | `ClosedAxis.tension_seamState` |
| `1 ≤ c ≤ 1 + 2/(d − 1)` | `ClosedAxis.one_le_cMax`, `ClosedAxis.cMax_le` |
| `c → 1`: al crecer el eje la corriente se junta en la costura | `ClosedAxis.tendsto_cMax` |

| en el estado de la costura, para todo `d`: `Var T° = 1/2`, `Var P = 1`, `cov = 0`, `⟨K⟩ = 1` | `variance_transport_seamState`, `variance_PdOp_seamState`, `tension_seamState` |
| su excedente de Robertson–Schrödinger es `1/4` y su cociente `Var T° · Var P / (⟨K⟩/2)² = 2` | `gramDefectAt_seamState`, `ratio_seamState` |
| su velocidad `⟨K⟩/c` tiende a `1` | `tendsto_speed_seamState` |

Cada sistema fija su propia `c`; esta es la del eje cerrado. Al crecer el eje, el estado de la
costura llega a esa `c` con razón de incertidumbre `√2` para todo `d`: el cuanto `√2 − 1` no se
cierra en el límite.

## El cubo dentro de la caja: los cristales de 3 ejes caben en la caja de 4

Los 6 observables de `x`, `y`, `z` dentro de la caja de 4 ejes, con cualquier par en el cuarto
eje `w`. En estados producto:

| Enunciado | Lean |
|---|---|
| `Σ` y `Ω` de `x`, `y`, `z` son los del cubo, lleve lo que lleve el cuarto eje | `CubeInBox.covMatrix_xyz`, `CubeInBox.imMatrix_xyz` |
| los determinantes se factorizan: `det Σ₈ = det Σ₆ · det Σ_w`, `\|det Ω₈\| = \|det Ω₆\| · \|det Ω_w\|` | `det_covMatrix_box`, `abs_det_imMatrix_box` |
| con `w` cerrado de 3 posiciones en su banda, Robertson es estricto en toda la caja si `det Σ₆ > 0` | `robertson_det_box_strict` |
| el cubo `3 × 3 × 3` en corriente máxima satura (`det Σ₆ = \|det Ω₆\| = 1/64`) | `cube_three_saturates` |
| **el cubo satura y la caja no**: con `w` cerrado en su corriente máxima, la caja es estricta | `cube_saturates_box_strict` |

| **para todo estado, enredado o no**: la fibra cerrada oculta con tensión mayor que `1` conserva su defecto | `ClosedAxisEntangled.gramDefect_pos_of_band`, `gramDefect_box_pos` |

El cuarto eje no rompe nada de lo que se ve en `x`, `y`, `z`; solo puede agregar cuanto, y
enredarlo con `x`, `y`, `z` no le quita su defecto (análogo de `D49e`).

## Igualdad en Robertson 1934 con cualquier número de ejes

`n` ejes, cada uno con su par de observables, que conmutan entre ejes distintos: el cubo de
Tom (`n = 3`), la caja con la fibra cerrada (`n = 4`), una región de cristal en `n` direcciones.

| Enunciado | Lean |
|---|---|
| `n` rectas contra dimensión `n` dejan un vector en cualquier eje elegido | `RobertsonEquality.exists_single_axis` |
| `[L_a, L_b] = Σ_i σ_i(a, b) [A_{0,i}, A_{1,i}]` | `RobertsonEquality.commutator_sum` |
| en la igualdad, el núcleo de `Σ + iΩ` tiene dimensión `≥ n` | `RobertsonEquality.le_finrank_ker` |
| **un solo eje con defecto positivo** + `det Ω ≠ 0` + igualdad ⇒ `Σ_i σ_i [A_{0,i}, A_{1,i}] Φ = 0` con `σ ≠ 0` | `RobertsonEquality.exists_sigma_of_det_eq` |

En la caja, ese eje puede ser la fibra cerrada oculta, que tiene defecto para todo estado en su
banda (`ClosedAxisEntangled`):

| Enunciado | Lean |
|---|---|
| en la caja de 4 ejes, los observables de ejes distintos conmutan | `BoxCommute.boxPairs_comm` |
| **igualdad en la caja con la fibra oculta en su banda ⇒ `Σ_i σ_i [T_i, P_i] Φ = 0`, `σ ≠ 0`** (primer paso de `D49t` para la caja) | `BoxEquality.exists_sigma_of_det_eq` |
| en la igualdad los `2n` vectores de fluctuación generan dimensión `≤ n`, son independientes sobre `ℝ`, y el eje con defecto se acopla con los demás | `RobertsonCoupling.finrank_span_le`, `linearIndependent_real`, `exists_coupling` |
| **en la caja: igualdad ⇒ la fibra oculta se acopla con `x`, `y`, `z`** | `BoxEquality.exists_coupling` |

## El álgebra del eje cerrado (análogos de `D49i`, `D49r`)

| Enunciado | Lean |
|---|---|
| `[T°, P₃] = ½ [[0, 1, 2], [−1, 0, 1], [−2, −1, 0]]`: la costura pesa el doble | `ClosedAxisAlgebra.comm_eq` |
| `[P₃, [T°, P₃]] = −T° − (3/2) S`, invertible: no anula ningún estado | `PC_eq`, `eq_zero_of_PC` |
| `[T°, [T°, P₃]] = (3/2)(P₃ + P₃T° + T°P₃)`, con núcleo la recta de `(1, −2, 1)`, igual que `[T°, P₃]` | `TC_eq`, `TC_mulVec_eq_zero_iff`, `comm_mulVec_eq_zero_iff` |
| `T°` es invertible: el transporte no anula ningún estado | `eq_zero_of_Tc` |
| en un producto, enredado o no, `T°` y `[P₃, [T°, P₃]]` no anulan ningún estado | `eq_zero_of_lift_Tc`, `eq_zero_of_lift_PC` |

## El cuanto se multiplica: `k` fibras apiladas

`k` copias de un eje, cada una con su par, en `ℂ^(Fin k → Fin d)`. En un estado producto:

| Enunciado | Lean |
|---|---|
| los productos internos se factorizan por copia | `StackedFibers.inner_prodK` |
| `Σ` y `Ω` son diagonales por bloques, un bloque por copia | `covMatrix_prodK`, `imMatrix_prodK` |
| `det Σ = Π_i det Σ_i`, `\|det Ω\| = Π_i \|det Ω_i\|` | `det_covMatrix_prodK`, `abs_det_imMatrix_prodK` |
| una fibra cerrada en su corriente máxima tiene factor `F = det Σ_w / \|det Ω_w\| > 1` | `one_lt_closedFactor` |
| **`k` fibras cerradas: `det Σ = F^k · \|det Ω\|`**, exponencial en el número de fibras | `closed_stack`, `tendsto_closedFactor_pow` |

Lo que crece es el cuanto, no la velocidad: cada eje sigue acotado por su propia `c`
(`tension_lift_le`, `D37c`).

## Puente físico declarado (propuesta)

El cuarto eje `w` se lee como la fibra de Hopf del espacio físico. El espacio de cuatro ejes es
`ℂ² = ℝ⁴`, y cada esfera `S³` de radio `r` está fibrada por círculos (Hopf 1931). En la base
`S² = ℂ ∪ {∞}`, 0 e ∞ son dos puntos de la misma esfera. Este puente es premisa, no teorema.
Lo que está en Lean es lo de la tabla: el cuanto por eje, la exclusión de 2 y 3 posiciones y el
límite `C_∞⁸`, que son los mismos en cuatro ejes que en tres. Que un eje cerrado lleve un cuanto
por el cierre ya está en `D16c`/`D16e`.

## Construir

```
lake build
lake env lean Verification/Axioms.lean
```

Solo se esperan los axiomas `propext`, `Classical.choice` y `Quot.sound`.
