/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.KogutSusskindSecondDiff

/-!
# The mixed difference of the one-link ratio: the exact identity

First step of the recursion for the second difference of `log r`
(`KogutSusskindSecondDiff`). Write the right-hand side of `ratio_equation` as

  `Φ_{e,k}(U) = X_e(U) + |G|⁻¹ · Σ_{e'' ≠ e} Σ_h r (shift k e (shift h e'' U))`,

so that `a(U_k) · r(U_k) = λE · Φ_{e,k}(U)`. Changing a second link `e' ≠ e` of the argument
changes `Φ_{e,k}` only through the links `e'' ∉ {e, e'}` and through `X_e`: the term of `e'`
itself cancels exactly.

## Main results

- `KogutSusskindMixedDiff.Phi` : the function `Φ_{e,k}`.
- `KogutSusskindMixedDiff.a_mul_r_shift` : `a(U_k) r(U_k) = λE · Φ_{e,k}(U)`.
- `KogutSusskindMixedDiff.Phi_mixed` : for `e' ≠ e`, `Φ_{e,k}(U) − Φ_{e,k}(U')` with
  `U' = shift k' e' U` is the difference of `X_e` plus the sum over `e'' ∉ {e, e'}` only.

No inequality is proved here. The estimate of the mixed difference of `log r`, the choice of the
small root of the quadratic inequality and the Poincaré inequality for `r²` are not formalised.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindSpectrum KogutSusskindGround
  KogutSusskindHarnack KogutSusskindSecondDiff

namespace KogutSusskindMixedDiff

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))

/-- The right-hand side of the equation of the one-link ratio, divided by `λE`. -/
def Phi (r : Conf ι δ G → ℝ) (e : δ × ι) (k : G) (U : Conf ι δ G) : ℝ :=
  X r e U + (Fintype.card G : ℝ)⁻¹ * ∑ e' ∈ Finset.univ.erase e, ∑ h : G,
    r (shift k e.1 e.2 (shift h e'.1 e'.2 U))

/-- `a(U_k) · r(U_k) = λE · Φ_{e,k}(U)`: the equation of the one-link ratio. -/
theorem a_mul_r_shift {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ}
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (e : δ × ι) (k : G) (U : Conf ι δ G) :
    aF ρ τ R lE lB m0 (shift k e.1 e.2 U) * r (shift k e.1 e.2 U) = lE * Phi r e k U := by
  rw [ratio_equation ρ τ R heig e k U]
  unfold Phi
  ring

/-- **The mixed difference of `Φ`**: the term of the link `e'` cancels, so only `X_e` and the
links `e'' ∉ {e, e'}` remain. -/
theorem Phi_mixed (r : Conf ι δ G → ℝ) {e e' : δ × ι} (hne : e' ≠ e) (k k' : G)
    (U : Conf ι δ G) :
    Phi r e k U - Phi r e k (shift k' e'.1 e'.2 U)
      = (X r e U - X r e (shift k' e'.1 e'.2 U))
        + (Fintype.card G : ℝ)⁻¹ * ∑ e'' ∈ (Finset.univ.erase e).erase e', ∑ h : G,
            (r (shift k e.1 e.2 (shift h e''.1 e''.2 U))
              - r (shift k e.1 e.2 (shift h e''.1 e''.2 (shift k' e'.1 e'.2 U)))) := by
  have hmem : e' ∈ Finset.univ.erase e := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hcancel := term_invariant r e e' k k' U
  unfold Phi
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase (Finset.univ.erase e) _ hmem]
  simp only [Finset.sum_sub_distrib, hcancel]
  ring

end KogutSusskindMixedDiff
