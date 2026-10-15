/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49h_DeterminantEqualityRelation
public import NRS3Hopf.RobertsonEqualityLines

/-!
# When Robertson 1934 is an equality, on any number of axes

The equality case of `D49h`, for `n` axes instead of three. Each axis `i` carries a pair of
symmetric operators `(A_{0,i}, A_{1,i})`, and operators of different axes commute: the cube of
three axes, the box of four with a closed fiber, or the region of a crystal along `n`
directions. For a state `Φ` with `det Ω ≠ 0`:

* if `det Σ = |det Ω|`, the kernel of the Gram matrix `Σ + iΩ` of the `2n` fluctuation vectors
  has dimension at least `n` (`D49g`);
* every kernel vector `a` is a relation, so `Φ` is an eigenvector of `L_a = Σ a_p A_p`, and
  `[L_a, L_b] = Σ_i σ_i(a, b) [A_{0,i}, A_{1,i}]`, with
  `σ_i(a, b) = a_{0,i} b_{1,i} − a_{1,i} b_{0,i}`;
* if every `σ_i` vanished on the kernel, its part on each axis would be a line, and `n` lines
  against dimension `n` leave a relation on any chosen axis `k` alone, a vanishing defect of
  that axis.

So if one axis `k` has a positive defect, equality forces `Σ_i σ_i [A_{0,i}, A_{1,i}] Φ = 0` with
`σ ≠ 0`. One axis with a forced defect is enough: on the box of four axes it can be the hidden
closed fiber (`ClosedAxisEntangled`).

## Main results

- `RobertsonEquality.exists_single_axis` : `n` lines against dimension `n` leave a vector on any
  chosen axis alone.
- `RobertsonEquality.commutator_sum` : `[L_a, L_b] = Σ_i σ_i(a, b) [A_{0,i}, A_{1,i}]`.
- `RobertsonEquality.sup_ker_eq_top` : at equality the relations and the kernel of the
  transpose span everything.
- `RobertsonEquality.le_finrank_ker` : at equality the kernel has dimension at least `n`.
- `RobertsonEquality.exists_sigma_of_det_eq` : one axis with a positive defect and equality give
  `Σ_i σ_i [A_{0,i}, A_{1,i}] Φ = 0` with `σ ≠ 0`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant CauchyGram
open DeterminantEqualityRelation SpectralExtremal
open scoped ComplexOrder

namespace RobertsonEquality

variable {n : ℕ}

/-! ## 2. Relations among the fluctuation vectors -/

variable {ι : Type*} [Fintype ι]
  (L : Fin 2 × Fin n → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ ι)

/-- The `2n` fluctuation vectors. -/
def fluct (p : Fin 2 × Fin n) : EuclideanSpace ℂ ι := centeredG (L p) Φ

/-- The combination `L_a = Σ a_p A_p`. -/
def comb (a : Fin 2 × Fin n → ℂ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  ∑ p, a p • L p

theorem sum_eq_zero_of_mulVec {a : Fin 2 × Fin n → ℂ} (h : gram ℂ (fluct L Φ) *ᵥ a = 0) :
    ∑ p, a p • fluct L Φ p = 0 := by
  have := star_dotProduct_gram_mulVec (𝕜 := ℂ) (fluct L Φ) a a
  rw [h, dotProduct_zero, eq_comm, inner_self_eq_zero] at this
  exact this

theorem comb_eigen {a : Fin 2 × Fin n → ℂ} (h : ∑ p, a p • fluct L Φ p = 0) :
    comb L a Φ = (∑ p, a p * meanG (L p) Φ) • Φ := by
  simp only [fluct, centeredG, smul_sub, Finset.sum_sub_distrib, smul_smul] at h
  simp only [comb, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
  exact sub_eq_zero.mp h

omit [Fintype ι] in
theorem comb_comb (c d : Fin 2 × Fin n → ℂ) :
    comb L c (comb L d Φ) = ∑ p, ∑ q, (c p * d q) • L p (L q Φ) := by
  simp only [comb, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_smul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable {L}
variable (hcomm : ∀ s t i j, i ≠ j → ∀ ψ, L (t, j) (L (s, i) ψ) = L (s, i) (L (t, j) ψ))
include hcomm

/-- One axis of the double sum: only the same axis survives. -/
theorem axis_sum (a b : Fin 2 × Fin n → ℂ) (i : Fin n) :
    ∑ s, ∑ q, ((a (s, i) * b q) • L (s, i) (L q Φ) - (b q * a (s, i)) • L q (L (s, i) Φ)) =
      (a (0, i) * b (1, i) - a (1, i) * b (0, i)) • opCommutator (L (0, i)) (L (1, i)) Φ := by
  have hq (s : Fin 2) : ∑ q, ((a (s, i) * b q) • L (s, i) (L q Φ) -
      (b q * a (s, i)) • L q (L (s, i) Φ)) =
      ∑ t, ((a (s, i) * b (t, i)) • L (s, i) (L (t, i) Φ) -
        (b (t, i) * a (s, i)) • L (t, i) (L (s, i) Φ)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single i]
    intro j _ hj
    rw [hcomm s t i j (Ne.symm hj), mul_comm, sub_self]
    intro h; exact absurd (Finset.mem_univ i) h
  simp only [hq, Fin.sum_univ_two, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply]
  module

/-- **`[L_a, L_b] = Σ_i σ_i(a, b) [A_{0,i}, A_{1,i}]`** when operators of different axes
commute. -/
theorem commutator_sum (a b : Fin 2 × Fin n → ℂ) :
    comb L a (comb L b Φ) - comb L b (comb L a Φ) =
      ∑ i, (a (0, i) * b (1, i) - a (1, i) * b (0, i)) • opCommutator (L (0, i)) (L (1, i)) Φ := by
  rw [comb_comb, comb_comb, Finset.sum_comm (f := fun p q => (b p * a q) • L p (L q Φ)),
    ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => axis_sum Φ hcomm a b i

omit hcomm in
theorem gramDefectC_eq_zero_of_rel {x y : EuclideanSpace ℂ ι} {α β : ℂ} (h : α • x + β • y = 0)
    (hαβ : α ≠ 0 ∨ β ≠ 0) : gramDefectC x y = 0 := by
  rw [gramDefectC_eq_zero_iff]
  rcases hαβ with hα | hβ
  · have hx : x = (-β / α) • y := by
      have h' : α • x = -(β • y) := eq_neg_of_add_eq_zero_left h
      calc x = α⁻¹ • (α • x) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = (-β / α) • y := by
          rw [h', smul_neg, smul_smul, ← neg_smul, neg_div, div_eq_inv_mul]
    rw [norm_inner_symm, mul_comm]
    exact ((norm_inner_eq_norm_tfae ℂ y x).out 3 1).mp (Or.inr (⟨_, hx⟩ : ∃ r : ℂ, x = r • y))
  · have hy : y = (-α / β) • x := by
      have h' : β • y = -(α • x) := eq_neg_of_add_eq_zero_right h
      calc y = β⁻¹ • (β • y) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = (-α / β) • x := by
          rw [h', smul_neg, smul_smul, ← neg_smul, neg_div, div_eq_inv_mul]
    exact ((norm_inner_eq_norm_tfae ℂ x y).out 3 1).mp (Or.inr (⟨_, hy⟩ : ∃ r : ℂ, y = r • x))

variable {Φ}

omit hcomm in
/-- **At equality the relations and the kernel of the transpose span everything**, when
`det Ω ≠ 0`. -/
theorem sup_ker_eq_top (hΩ : (imMatrix L Φ).det ≠ 0)
    (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin ⊔
      LinearMap.ker (gram ℂ (fluct L Φ))ᵀ.mulVecLin = ⊤ := by
  set S := covMatrix L Φ
  set W := imMatrix L Φ
  set A : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ := S.map ((↑) : ℝ → ℂ)
  set B : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ := Complex.I • W.map ((↑) : ℝ → ℂ)
  have hG : gram ℂ (fluct L Φ) = A + B := gram_centeredG L Φ
  have hGt : (gram ℂ (fluct L Φ))ᵀ = A - B := transpose_gram_centeredG L Φ
  have h₂ : (A + B).PosSemidef := hG ▸ posSemidef_gram ℂ (fluct L Φ)
  have h₁ : (A - B).PosSemidef := hGt ▸ (posSemidef_gram ℂ (fluct L Φ)).transpose
  have hS : A.PosSemidef := by
    have h := (h₁.add h₂).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
    convert h using 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    ring
  have hB : B.IsHermitian := by
    rw [show B = A - (A - B) by abel]
    exact hS.1.sub h₁.1
  have hdetA : A.det = (S.det : ℂ) := (RingHom.map_det Complex.ofRealHom S).symm
  have hA : A.PosDef := (Matrix.PosSemidef.posDef_iff_det_ne_zero hS).mpr (by
    rw [hdetA, heq]; exact_mod_cast abs_ne_zero.mpr hΩ)
  have hW : (W.map ((↑) : ℝ → ℂ)).det = (W.det : ℂ) := (RingHom.map_det Complex.ofRealHom W).symm
  have hnorm : ‖B.det‖ = A.det.re := by
    rw [det_smul, hW, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hdetA, Complex.ofReal_re, heq]
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_add_of_norm_det_eq hA hB h₁ h₂ hnorm x
  refine Submodule.add_mem_sup (LinearMap.mem_ker.mpr ?_) (LinearMap.mem_ker.mpr ?_)
  · rw [Matrix.mulVecLin_apply, hG]
    exact hy
  · rw [Matrix.mulVecLin_apply, hGt]
    exact hz

omit hcomm in
/-- **At equality the kernel of the Gram matrix has dimension at least `n`**, when
`det Ω ≠ 0`. -/
theorem le_finrank_ker (hΩ : (imMatrix L Φ).det ≠ 0)
    (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    n ≤ Module.finrank ℂ (LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin) := by
  set N := LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin
  set M := LinearMap.ker (gram ℂ (fluct L Φ))ᵀ.mulVecLin
  have hsup : N ⊔ M = ⊤ := sup_ker_eq_top hΩ heq
  have hNM : Module.finrank ℂ M = Module.finrank ℂ N := finrank_ker_transpose _
  show n ≤ Module.finrank ℂ N
  have h := Submodule.finrank_sup_add_finrank_inf_eq N M
  rw [hsup, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

/-- **Equality needs a relation among the tensions.** If one axis `k` has a positive defect,
`det Ω ≠ 0` and `det Σ = |det Ω|`, then `Σ_i σ_i [A_{0,i}, A_{1,i}] Φ = 0` with `σ ≠ 0`. -/
theorem exists_sigma_of_det_eq (k : Fin n)
    (hk : 0 < gramDefectC (fluct L Φ (0, k)) (fluct L Φ (1, k)))
    (hΩ : (imMatrix L Φ).det ≠ 0) (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    ∃ σ : Fin n → ℂ, σ ≠ 0 ∧
      ∑ i, σ i • opCommutator (L (0, i)) (L (1, i)) Φ = 0 := by
  set N := LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin
  have hdim : n ≤ Module.finrank ℂ N := le_finrank_ker hΩ heq
  by_contra hcon
  push Not at hcon
  have hrel (a : Fin 2 × Fin n → ℂ) (ha : a ∈ N) : ∑ p, a p • fluct L Φ p = 0 :=
    sum_eq_zero_of_mulVec L Φ (by rw [← Matrix.mulVecLin_apply]; exact ha)
  have hσ : ∀ a ∈ N, ∀ b ∈ N, ∀ i, a (0, i) * b (1, i) - a (1, i) * b (0, i) = 0 := by
    intro a ha b hb i
    by_contra hi
    apply hcon (fun i => a (0, i) * b (1, i) - a (1, i) * b (0, i)) (fun h => hi (congrFun h i))
    rw [← commutator_sum Φ hcomm, comb_eigen L Φ (hrel b hb), comb_eigen L Φ (hrel a ha),
      map_smul, map_smul, comb_eigen L Φ (hrel b hb), comb_eigen L Φ (hrel a ha), smul_smul,
      smul_smul, mul_comm, sub_self]
  obtain ⟨a, haN, ha0, hsupp⟩ := exists_single_axis N hdim hσ k
  have hk' : a (0, k) • fluct L Φ (0, k) + a (1, k) • fluct L Φ (1, k) = 0 := by
    have h := hrel a haN
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_eq_single k, Finset.sum_eq_single k]
      at h
    · exact h
    all_goals first
      | (intro j _ hj; rw [hsupp _ _ hj, zero_smul])
      | (intro h; exact absurd (Finset.mem_univ k) h)
  have hαβ : a (0, k) ≠ 0 ∨ a (1, k) ≠ 0 := by
    by_contra h
    push Not at h
    apply ha0
    ext ⟨s, i⟩
    by_cases hi : i = k
    · subst hi
      rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
      exacts [h.1, h.2]
    · exact hsupp s i hi
  exact (ne_of_gt hk) (gramDefectC_eq_zero_of_rel hk' hαβ)

end RobertsonEquality
