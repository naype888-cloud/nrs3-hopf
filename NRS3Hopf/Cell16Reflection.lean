/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.NRSCell16

/-!
# The covariance at the top of the tension vanishes by symmetry

On the 16-cell (`NRSCell16`), at the state `ψ*` of maximal tension on axis `k`,
`Cov(T, P_k) = 0`. Here this zero is not computed: it comes from a symmetry of the state.

Let `g` be a permutation of the points and `Θ_g ψ = conj (ψ ∘ g)`, an antiunitary map. If `Θ_g`
fixes the state, commutes with an observable `L` and reverses an observable `M`, then
`⟪L̃ψ, M̃ψ⟫ = −conj ⟪L̃ψ, M̃ψ⟫`, so `⟨M⟩ = 0` and `Cov(L, M) = 0`: an even and an odd observable
of a symmetric state have covariance zero. Only the expectation of the bracket survives.

On the 16-cell take `g` the reflection of axis `k`, the signed permutation that reverses the sign
of `k` and keeps the other axes. It keeps the joins, so `Θ_g` commutes with `T`; it reverses the
coordinate along `k`, so `Θ_g` reverses `P_k`; and `ψ* = (−i/2, i/2, √3/6, …)` is fixed, because
the reflection swaps `±k` and the conjugation swaps `∓i/2`. Hence `⟨P_k⟩ = 0` and
`Cov(T, P_k) = 0` at `ψ*` on every axis.

## Main results

- `Cell16Reflection.mean_eq_zero_of_reverse` : a reversed observable of a fixed state has mean
  zero.
- `Cell16Reflection.covariance_eq_zero_of_reverse` : an even and an odd observable of a fixed
  state have covariance zero.
- `Cell16Reflection.reflect_psiK` : the reflection of axis `k` with conjugation fixes `ψ*`.
- `Cell16Reflection.covariance_psiK` : `Cov(T, P_k) = 0` at `ψ*`, by symmetry.
-/

@[expose] public noncomputable section

open Matrix Complex Cell16 PathGraph3DNRS

namespace Cell16Reflection

/-! ## Antiunitary symmetries -/

section Antiunitary

private lemma re_eq_zero_of_eq_neg_conj {z : ℂ} (h : z = -starRingEnd ℂ z) : z.re = 0 := by
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at this
  linarith

variable {ι : Type*} (g : Equiv.Perm ι)

/-- The antiunitary map `Θ_g ψ = conj (ψ ∘ g)`. -/
def conjPerm (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun p => starRingEnd ℂ (ψ (g p))

@[simp] lemma conjPerm_apply (ψ : EuclideanSpace ℂ ι) (p : ι) :
    conjPerm g ψ p = starRingEnd ℂ (ψ (g p)) := rfl

lemma conjPerm_sub (x y : EuclideanSpace ℂ ι) :
    conjPerm g (x - y) = conjPerm g x - conjPerm g y := by
  ext p; simp

lemma conjPerm_neg (x : EuclideanSpace ℂ ι) : conjPerm g (-x) = -conjPerm g x := by
  ext p; simp

lemma conjPerm_smul (c : ℂ) (x : EuclideanSpace ℂ ι) :
    conjPerm g (c • x) = starRingEnd ℂ c • conjPerm g x := by
  ext p; simp

lemma inner_conjPerm [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    inner ℂ (conjPerm g x) (conjPerm g y) = starRingEnd ℂ (inner ℂ x y) := by
  simp only [PiLp.inner_apply, conjPerm_apply, RCLike.inner_apply, map_sum,
    RingHomCompTriple.comp_apply, RingHom.id_apply, map_mul]
  exact Equiv.sum_comp g fun p => starRingEnd ℂ (y p) * x p

variable [Fintype ι] {g} {L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}
  {ψ : EuclideanSpace ℂ ι}
  (hψ : conjPerm g ψ = ψ) (hM : ∀ x, M (conjPerm g x) = -conjPerm g (M x))
include hψ hM

/-- **A reversed observable of a fixed state has mean zero.** -/
lemma mean_eq_zero_of_reverse : meanG M ψ = 0 := by
  refine re_eq_zero_of_eq_neg_conj ?_
  conv_lhs => rw [← hψ, hM, inner_neg_right, inner_conjPerm]

include hψ hM in
/-- **An even and an odd observable of a fixed state have covariance zero**: if `Θ_g` fixes
`ψ`, commutes with `L` and reverses `M`, then `Cov(L, M) = 0` at `ψ`. -/
lemma covariance_eq_zero_of_reverse (hL : ∀ x, L (conjPerm g x) = conjPerm g (L x)) :
    covarianceG L M ψ = 0 := by
  have hcM : centeredG M ψ = M ψ := by
    rw [centeredG, mean_eq_zero_of_reverse hψ hM]; simp
  have hcL : conjPerm g (centeredG L ψ) = centeredG L ψ := by
    rw [centeredG, conjPerm_sub, conjPerm_smul, ← hL, hψ, Complex.conj_ofReal]
  refine re_eq_zero_of_eq_neg_conj ?_
  conv_lhs => rw [hcM, ← hcL, ← hψ, hM, inner_neg_right, inner_conjPerm, hψ]
  rw [hcM]

end Antiunitary

/-! ## The reflection of an axis of the 16-cell -/

open NRSCell16

variable (k : Fin 4)

/-- The reflection of axis `k`: reverse the sign of `k`, keep the other axes. -/
def reflect : Equiv.Perm Pt := signedPerm 1 fun a => decide (a = k)

lemma T_conjPerm (x : H) : T (conjPerm (reflect k) x) = conjPerm (reflect k) (T x) := by
  ext ⟨i, s⟩
  simp only [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply, conjPerm_apply, mulVec, dotProduct,
    map_sum, map_mul]
  rw [← Equiv.sum_comp (reflect k)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Tm, Adj, reflect, apply_ite (starRingEnd ℂ), map_inv₀, map_ofNat]

lemma P_conjPerm (x : H) :
    Pos k (conjPerm (reflect k) x) = -conjPerm (reflect k) (Pos k x) := by
  ext ⟨i, s⟩
  simp only [Pos, Matrix.toEuclideanLin, Matrix.toLpLin_apply, conjPerm_apply, mulVec, dotProduct,
    Pm, diagonal_apply, PiLp.neg_apply]
  by_cases h : i = k
  · subst h; cases s <;> simp [reflect]
  · simp [reflect, h]

/-- **The reflection of axis `k` with conjugation fixes `ψ*`**: it swaps `±k` and `∓i/2`. -/
lemma reflect_psiK : conjPerm (reflect k) (psiK k) = psiK k := by
  ext ⟨i, s⟩
  by_cases h : i = k
  · subst h; cases s <;> simp [psiK, patk, reflect, map_ofNat]
  · simp [psiK, patk, reflect, h, Complex.conj_ofReal, map_ofNat, map_div₀]

/-- **`⟨P_k⟩ = 0` and `Cov(T, P_k) = 0` at `ψ*`, by symmetry**, on every axis. -/
theorem covariance_psiK : meanG (Pos k) (psiK k) = 0 ∧ covarianceG T (Pos k) (psiK k) = 0 :=
  ⟨mean_eq_zero_of_reverse (reflect_psiK k) (P_conjPerm k),
    covariance_eq_zero_of_reverse (reflect_psiK k) (P_conjPerm k) (T_conjPerm k)⟩

end Cell16Reflection
