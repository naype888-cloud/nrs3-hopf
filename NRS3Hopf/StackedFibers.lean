/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.CubeInBox

/-!
# The quantum multiplies: `k` stacked fibers

Stack `k` copies of one axis with `d` positions and a pair `M = (A, B)`: the space is
`ℂ^(Fin k → Fin d)`, and the pair of copy `i` acts on coordinate `i`. On a product state
`s₁ ⊗ ⋯ ⊗ s_k` the fluctuation vectors of different copies are orthogonal, so `Σ` and `Ω` are
block diagonal, one `2 × 2` block per copy, and

  `det Σ = Π_i det Σ_i`,  `|det Ω| = Π_i |det Ω_i|`.

With every copy in the same state the Robertson ratio is the ratio of one copy to the power
`k`. For the closed fiber with three positions at its maximal current state that ratio is a
constant `F > 1`, so `det Σ = F^k |det Ω|`: the quantum multiplies, exponentially in the number of
fibers.

## Main results

- `StackedFibers.inner_prodK` : inner products of product states factor over the copies.
- `StackedFibers.covMatrix_prodK`, `StackedFibers.imMatrix_prodK` : `Σ`, `Ω` block diagonal.
- `StackedFibers.det_covMatrix_prodK`, `StackedFibers.abs_det_imMatrix_prodK` : the products.
- `StackedFibers.det_replicate` : identical copies give the `k`-th power.
- `StackedFibers.one_lt_closedFactor` : one closed fiber at its maximal current state has
  `F = det Σ_w / |det Ω_w| > 1`.
- `StackedFibers.closed_stack` : `k` closed fibers at their maximal current state,
  `det Σ = F^k |det Ω|`.
- `StackedFibers.tendsto_closedFactor_pow` : `F^k` grows without bound.
-/

@[expose] public noncomputable section

open Matrix PathGraph3DNRS RobertsonDeterminant CubeInBox FourAxes TransportPosition

namespace StackedFibers

variable {d : ℕ}

/-- The product state `⊗_i s_i` on `ℂ^(κ → Fin d)`. -/
def prodK {κ : Type*} [Fintype κ] (s : κ → Hd d) : EuclideanSpace ℂ (κ → Fin d) :=
  WithLp.toLp 2 fun f => ∏ i, s i (f i)

theorem prodK_apply {κ : Type*} [Fintype κ] (s : κ → Hd d) (f : κ → Fin d) :
    prodK s f = ∏ i, s i (f i) := rfl

/-- Inner products of product states factor over the copies. -/
theorem inner_prodK {κ : Type*} [Fintype κ] [DecidableEq κ] (s s' : κ → Hd d) :
    inner ℂ (prodK s) (prodK s') = ∏ i, inner ℂ (s i) (s' i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, prodK_apply, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (x : Fin d) => s' i x * (starRingEnd ℂ) (s i x))).symm

variable {k : ℕ}

/-- Copy `i` and the other copies. -/
abbrev split (i : Fin k) : (Fin k → Fin d) ≃ Fin d × ({ j // j ≠ i } → Fin d) :=
  Equiv.funSplitAt i (Fin d)

theorem prodK_eq_split (s : Fin k → Hd d) (i : Fin k) :
    prodK s = prodAlong (split i) (s i) (prodK fun j : { j // j ≠ i } => s j) := by
  ext f
  simp only [prodK_apply, prodAlong_apply, split, Equiv.funSplitAt_apply]
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => s j (f j)) i

theorem prodAlong_split_eq_update (s : Fin k → Hd d) (i : Fin k) (x : Hd d) :
    prodAlong (split i) x (prodK fun j : { j // j ≠ i } => s j) =
      prodK (Function.update s i x) := by
  rw [prodK_eq_split _ i]
  congr 1
  · simp
  · congr 1
    funext j
    simp [Function.update_of_ne j.2]

/-- The pair of copy `i`, lifted to the stack. -/
def ops (M : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (p : Fin 2 × Fin k) :
    EuclideanSpace ℂ (Fin k → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin k → Fin d) :=
  Matrix.toEuclideanLin (liftAlong (split p.2) (M p.1))

variable {M : Fin 2 → Matrix (Fin d) (Fin d) ℂ} (hM : ∀ a, (M a).IsHermitian)
  {s : Fin k → Hd d} (hs : ∀ i, ‖s i‖ = 1)

include hs in
theorem norm_rest (i : Fin k) : ‖prodK fun j : { j // j ≠ i } => s j‖ = 1 := by
  have h := inner_prodK (fun j : { j // j ≠ i } => s j) (fun j : { j // j ≠ i } => s j)
  simp only [inner_self_of_norm_one (hs _), Finset.prod_const_one] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖prodK fun j : { j // j ≠ i } => s j‖ : ℂ)) ^ 2 = 1 := h
  have h3 : ((‖prodK fun j : { j // j ≠ i } => s j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    push_cast; exact h2
  have h3 : ‖prodK fun j : { j // j ≠ i } => s j‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3

include hs in
theorem centered_ops (a : Fin 2) (i : Fin k) :
    centeredG (ops M (a, i)) (prodK s) =
      prodK (Function.update s i (centeredG (Matrix.toEuclideanLin (M a)) (s i))) := by
  rw [ops, prodK_eq_split s i, centeredG_lift _ (norm_rest hs i), prodAlong_split_eq_update]

include hM hs

/-- The fluctuation vectors of different copies are orthogonal. -/
theorem inner_centered_ops (a b : Fin 2) (i j : Fin k) :
    inner ℂ (centeredG (ops M (a, i)) (prodK s)) (centeredG (ops M (b, j)) (prodK s)) =
      if i = j then inner ℂ (centeredG (wPair M a) (s i)) (centeredG (wPair M b) (s i))
      else 0 := by
  have hW a : (wPair M a).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hM a)
  rw [centered_ops hs, centered_ops hs, inner_prodK]
  split_ifs with h
  · subst h
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [Function.update_self]
    rw [Finset.prod_eq_one, mul_one]
    · rfl
    · intro x _
      simp [Function.update_of_ne x.2, hs x]
  · rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [Function.update_self, Function.update_of_ne h]
    rw [show inner ℂ (centeredG (Matrix.toEuclideanLin (M a)) (s i)) (s i) = 0 from
      CubePythagoras.inner_self_centeredG (hW a) (hs i), zero_mul]

/-- **On a product state `Σ` is block diagonal**, one `2 × 2` block per copy. -/
theorem covMatrix_prodK :
    covMatrix (ops M) (prodK s) = blockDiagonal fun i => covMatrix (wPair M) (s i) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [covMatrix, of_apply, blockDiagonal_apply, covarianceG, inner_centered_ops hM hs]
  split_ifs <;> rfl

/-- **On a product state `Ω` is block diagonal**, one `2 × 2` block per copy. -/
theorem imMatrix_prodK :
    imMatrix (ops M) (prodK s) = blockDiagonal fun i => imMatrix (wPair M) (s i) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [imMatrix, of_apply, blockDiagonal_apply, inner_centered_ops hM hs]
  split_ifs <;> rfl

/-- **`det Σ = Π_i det Σ_i`.** -/
theorem det_covMatrix_prodK :
    (covMatrix (ops M) (prodK s)).det = ∏ i, (covMatrix (wPair M) (s i)).det := by
  rw [covMatrix_prodK hM hs, det_blockDiagonal]

/-- **`|det Ω| = Π_i |det Ω_i|`.** -/
theorem abs_det_imMatrix_prodK :
    |(imMatrix (ops M) (prodK s)).det| = ∏ i, |(imMatrix (wPair M) (s i)).det| := by
  rw [imMatrix_prodK hM hs, det_blockDiagonal, Finset.abs_prod]

omit hs in
/-- **Identical copies**: the determinants are those of one copy to the power `k`. -/
theorem det_replicate {t : Hd d} (ht : ‖t‖ = 1) :
    (covMatrix (ops (k := k) M) (prodK fun _ => t)).det = (covMatrix (wPair M) t).det ^ k ∧
      |(imMatrix (ops (k := k) M) (prodK fun _ => t)).det| =
        |(imMatrix (wPair M) t).det| ^ k := by
  constructor
  · rw [det_covMatrix_prodK hM (fun _ => ht), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · rw [abs_det_imMatrix_prodK hM (fun _ => ht), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

end StackedFibers

namespace StackedFibers

open EigenvectorSaturation

/-- The factor of one closed fiber at its maximal current state,
`F = det Σ_w / |det Ω_w|`. -/
def closedFactor : ℝ :=
  (covMatrix (wPair closedPair) ClosedThree.maxState).det /
    |(imMatrix (wPair closedPair) ClosedThree.maxState).det|

theorem imPart_maxState_ne_zero : imPart ClosedThree.TcOp (PdOp 3) ClosedThree.maxState ≠ 0 := by
  intro h
  have ht := ClosedThree.tension_maxState
  rw [ClosedThree.tension, ← imPart_eq_im_inner ClosedThree.TcOp_isSymmetric
    (PdOp_isSymmetric 3), h, mul_zero] at ht
  have : (0 : ℝ) < √6 / 2 := by positivity
  linarith

/-- **One closed fiber at its maximal current state multiplies the ratio by `F > 1`.** -/
theorem one_lt_closedFactor : 1 < closedFactor := by
  have hi := imPart_maxState_ne_zero
  have hg := ClosedThree.surplus_pos_of_one_lt ClosedThree.norm_maxState (by
    rw [ClosedThree.tension_maxState, abs_of_pos (by positivity)]
    have : (2 : ℝ) < √6 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith)
  rw [closedFactor, det_covMatrix_closed, abs_det_imMatrix_closed,
    one_lt_div (by positivity)]
  linarith

/-- **The quantum multiplies**: `k` closed fibers, each at its maximal current state, have
`det Σ = F^k · |det Ω|` with `F > 1`, exponential in the number of fibers. -/
theorem closed_stack (k : ℕ) :
    (covMatrix (ops (k := k) closedPair) (prodK fun _ => ClosedThree.maxState)).det =
      closedFactor ^ k *
        |(imMatrix (ops (k := k) closedPair) (prodK fun _ => ClosedThree.maxState)).det| := by
  obtain ⟨h1, h2⟩ := det_replicate closedPair_isHermitian (k := k) ClosedThree.norm_maxState
  have hi : |(imMatrix (wPair closedPair) ClosedThree.maxState).det| ≠ 0 := by
    rw [abs_det_imMatrix_closed]
    exact pow_ne_zero 2 imPart_maxState_ne_zero
  rw [h1, h2, closedFactor, div_pow, div_mul_cancel₀ _ (pow_ne_zero k hi)]

/-- **Without bound**: the ratio of `k` closed fibers grows without bound in `k`. -/
theorem tendsto_closedFactor_pow :
    Filter.Tendsto (fun k : ℕ => closedFactor ^ k) Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt one_lt_closedFactor

end StackedFibers
