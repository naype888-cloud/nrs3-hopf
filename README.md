# NRS³ · Hopf — cuatro ejes espaciales

**El mismo cuanto en cuatro ejes.** La caja `dx × dy × dz × dw` lleva un par `(T_d, P_d)` por
eje: ocho observables. Robertson 1934, `|det Ω| ≤ det Σ`, vale para todo estado. En el estado de
corriente máxima (la `c` del sistema) el cociente es

  `det Σ / |det Ω| = (C_Nava(dx) C_Nava(dy) C_Nava(dz) C_Nava(dw))²`.

Vale `1` exactamente cuando cada eje tiene 2 o 3 posiciones. Es estrictamente mayor que `1` con
4 o más en cada eje (`C(4)⁸ ≈ 1.070` en `4 × 4 × 4 × 4`). Ninguna caja alcanza
`C_∞⁸ = (π²/3 − 2)⁴ ≈ 2.768`, y el cociente tiende a ese valor cuando los cuatro ejes crecen,
cada uno por su lado (Szegő, `D8`; monotonía, `D9`).

Lean 4 sobre [`nava-robertson-schrodinger`](https://github.com/naype888-cloud/nava-robertson-schrodinger)
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
