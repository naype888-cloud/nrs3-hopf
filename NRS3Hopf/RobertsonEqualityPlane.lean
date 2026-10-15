/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxFiberLine

/-!
# At equality an axis with a defect is crossed by the relations in both directions

The equality case of Robertson 1934 on `n` axes (`RobertsonEquality`), with symmetric
operators and operators of different axes commuting. Let `N` be the relations, `π_k` the part of
a coefficient vector on axis `k`, and `D_c = Σ_p c_p (A_p − ⟨A_p⟩)`, so that `c ∈ N` means
`D_c Φ = 0`. Suppose `π_k N` lies in a line spanned by `u`.

* At equality `N` and its conjugate span everything (`RobertsonEquality.sup_ker_eq_top`), so
  `u` and `ū` are independent, and every `c` with `π_k c = 0` is `y + z̄` with `y, z ∈ N` and
  `π_k y = π_k z = 0`.
* Let `S` be the states annihilated by `D_c` for every relation `c` off axis `k`. For `Ψ ∈ S` and
  `c` off axis `k`, `⟨Ψ, D_c Ψ⟩ = ⟨Ψ, D_y Ψ⟩ + ⟨D_z Ψ, Ψ⟩ = 0`, and by polarization
  `⟨Ψ, D_c Ψ'⟩ = 0` for `Ψ, Ψ' ∈ S`.
* A relation `a` through axis `k` splits as `D_a = D_b + M̃`, with `b` off axis `k` and `M̃` on
  axis `k`. `M̃` commutes with `D_c` for `c` off axis `k`, so `Φ, M̃Φ ∈ S`, and
  `‖M̃Φ‖² = −⟨M̃Φ, D_b Φ⟩ = 0`: a relation on axis `k` alone, against its positive defect.

So `π_k N` is all of `ℂ²`. No diagonalization of `M̃` is needed.

## Main results

- `RobertsonEqualityPlane.inner_dop_eq_zero` : `⟨Ψ, D_c Ψ'⟩ = 0` on `S`.
- `RobertsonEqualityPlane.not_line` : at equality the relations do not cross an axis with a
  positive defect along a line.
- `RobertsonEqualityPlane.map_fiberPart_eq_top` : they cross it in both directions.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant CauchyGram
open RobertsonEquality BoxFiberLine

namespace RobertsonEqualityPlane

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {L : Fin 2 × Fin n → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} {Φ : EuclideanSpace ℂ ι}

/-! ## 1. The centered combinations -/

variable (L Φ) in
/-- The centered operator `A_p − ⟨A_p⟩`. -/
def cop (p : Fin 2 × Fin n) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  L p - (meanG (L p) Φ : ℂ) • LinearMap.id

variable (L Φ) in
/-- The centered combination `D_c = Σ_p c_p (A_p − ⟨A_p⟩)`. -/
def dop (c : Fin 2 × Fin n → ℂ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  ∑ p, c p • cop L Φ p

theorem dop_apply (c : Fin 2 × Fin n → ℂ) (Ψ : EuclideanSpace ℂ ι) :
    dop L Φ c Ψ = ∑ p, c p • cop L Φ p Ψ := by
  simp [dop]

theorem dop_self (c : Fin 2 × Fin n → ℂ) : dop L Φ c Φ = ∑ p, c p • fluct L Φ p := by
  simp [dop_apply, cop, fluct, centeredG]

theorem dop_add (c d : Fin 2 × Fin n → ℂ) (Ψ : EuclideanSpace ℂ ι) :
    dop L Φ (c + d) Ψ = dop L Φ c Ψ + dop L Φ d Ψ := by
  simp [dop_apply, add_smul, Finset.sum_add_distrib]

/-- `D_c̄` is the adjoint of `D_c`. -/
theorem inner_dop_star (hsym : ∀ p, (L p).IsSymmetric) (c : Fin 2 × Fin n → ℂ)
    (Ψ Ψ' : EuclideanSpace ℂ ι) :
    inner ℂ Ψ (dop L Φ (star c) Ψ') = inner ℂ (dop L Φ c Ψ) Ψ' := by
  simp only [dop_apply, inner_sum, sum_inner, inner_smul_right, inner_smul_left, Pi.star_apply,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [cop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal, hsym p Ψ Ψ']

/-- Operators supported on different axes commute. -/
theorem dop_comm (hcomm : ∀ s t i j, i ≠ j → ∀ ψ, L (t, j) (L (s, i) ψ) = L (s, i) (L (t, j) ψ))
    {c e : Fin 2 × Fin n → ℂ} (hce : ∀ p q, c p ≠ 0 → e q ≠ 0 → p.2 ≠ q.2)
    (Ψ : EuclideanSpace ℂ ι) : dop L Φ c (dop L Φ e Ψ) = dop L Φ e (dop L Φ c Ψ) := by
  simp only [dop_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : c q = 0
  · simp [hc]
  by_cases he : e p = 0
  · simp [he]
  have h := hcomm p.1 q.1 p.2 q.2 (Ne.symm (hce q p hc he))
  rw [smul_comm]
  congr 2
  simp only [cop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
    map_smul, h]
  module

/-! ## 2. Relations off the axis -/

section Line

variable (k : Fin n) (hΩ : (imMatrix L Φ).det ≠ 0)
  (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) {u : Fin 2 → ℂ}
  (hline : ∀ a, gram ℂ (fluct L Φ) *ᵥ a = 0 → ∃ s : ℂ, fiberPart k a = s • u)
include hΩ heq hline

omit hline in
/-- Every coefficient vector is a relation plus a conjugate relation. -/
theorem exists_decomp (c : Fin 2 × Fin n → ℂ) : ∃ y z, gram ℂ (fluct L Φ) *ᵥ y = 0 ∧
    gram ℂ (fluct L Φ) *ᵥ z = 0 ∧ c = y + star z := by
  have hc : c ∈ LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin ⊔
      LinearMap.ker (gram ℂ (fluct L Φ))ᵀ.mulVecLin := by
    rw [sup_ker_eq_top hΩ heq]; trivial
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
  exact ⟨y, star w, LinearMap.mem_ker.mp hy, star_mulVec_eq_zero (LinearMap.mem_ker.mp hw),
    by rw [star_star]⟩

/-- **`u` and `ū` are independent.** -/
theorem det_ne_zero (hu : u ≠ 0) : star (u 0) * u 1 - star (u 1) * u 0 ≠ 0 := by
  intro hδ
  have hcomp (v : Fin 2 × Fin n → ℂ) :
      ∃ s t : ℂ, ∀ i, v (i, k) = s * u i + star t * star (u i) := by
    obtain ⟨y, z, hy, hz, rfl⟩ := exists_decomp hΩ heq v
    obtain ⟨s, hs⟩ := hline y hy
    obtain ⟨t, ht⟩ := hline z hz
    refine ⟨s, t, fun i => ?_⟩
    have h1 := congrFun hs i
    have h2 := congrFun ht i
    simp only [fiberPart_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    simp [h1, h2, star_mul']
  obtain ⟨s₀, t₀, h₀⟩ := hcomp (Pi.single (0, k) 1)
  obtain ⟨s₁, t₁, h₁⟩ := hcomp (Pi.single (1, k) 1)
  have a0 := h₀ 0; have a1 := h₀ 1; have b0 := h₁ 0; have b1 := h₁ 1
  simp only [Pi.single_apply, Prod.mk.injEq, and_true] at a0 a1 b0 b1
  norm_num at a0 a1 b0 b1
  apply hu
  funext i
  fin_cases i
  · show u 0 = 0
    simp only [RCLike.star_def] at hδ
    linear_combination u 0 * b1 - u 1 * b0 - starRingEnd ℂ t₁ * hδ
  · show u 1 = 0
    simp only [RCLike.star_def] at hδ
    linear_combination u 1 * a0 - u 0 * a1 + starRingEnd ℂ t₀ * hδ

/-- **Off the axis, a relation plus a conjugate relation, both off the axis.** -/
theorem exists_decomp_off (hu : u ≠ 0) {c : Fin 2 × Fin n → ℂ} (hc : fiberPart k c = 0) :
    ∃ y z, gram ℂ (fluct L Φ) *ᵥ y = 0 ∧ gram ℂ (fluct L Φ) *ᵥ z = 0 ∧
      fiberPart k y = 0 ∧ fiberPart k z = 0 ∧ c = y + star z := by
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_decomp hΩ heq c
  obtain ⟨s, hs⟩ := hline y hy
  obtain ⟨t, ht⟩ := hline z hz
  have hδ := det_ne_zero k hΩ heq hline hu
  have e (i : Fin 2) : s * u i + star t * star (u i) = 0 := by
    have := congrFun hc i
    simp only [fiberPart_apply, Pi.add_apply, Pi.star_apply, Pi.zero_apply] at this
    have h1 := congrFun hs i
    have h2 := congrFun ht i
    simp only [fiberPart_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [h1, h2, star_mul'] at this
    exact this
  have ht0 : star t = 0 := by
    have := e 0; have := e 1
    have h : star t * (star (u 0) * u 1 - star (u 1) * u 0) = 0 := by
      linear_combination u 1 * e 0 - u 0 * e 1
    exact (mul_eq_zero.mp h).resolve_right hδ
  have ht0' : t = 0 := by simpa using ht0
  refine ⟨y, z, hy, hz, ?_, by rw [ht, ht0', zero_smul], rfl⟩
  funext i
  have := e i
  rw [ht0, zero_mul, add_zero] at this
  rw [hs, Pi.smul_apply, smul_eq_mul, this, Pi.zero_apply]

/-! ## 3. The states annihilated by the relations off the axis -/

variable (L Φ) in
/-- The states annihilated by `D_c` for every relation `c` off axis `k`. -/
def InS (Ψ : EuclideanSpace ℂ ι) : Prop :=
  ∀ c, gram ℂ (fluct L Φ) *ᵥ c = 0 → fiberPart k c = 0 → dop L Φ c Ψ = 0

omit hΩ heq hline in
theorem inS_add {Ψ Ψ' : EuclideanSpace ℂ ι} (h : InS L Φ k Ψ) (h' : InS L Φ k Ψ') (r : ℂ) :
    InS L Φ k (Ψ + r • Ψ') := fun c hc hk => by
  rw [map_add, map_smul, h c hc hk, h' c hc hk, smul_zero, add_zero]

theorem inner_dop_self (hsym : ∀ p, (L p).IsSymmetric) (hu : u ≠ 0) {Ψ : EuclideanSpace ℂ ι}
    (hΨ : InS L Φ k Ψ) {c : Fin 2 × Fin n → ℂ} (hc : fiberPart k c = 0) :
    inner ℂ Ψ (dop L Φ c Ψ) = 0 := by
  obtain ⟨y, z, hy, hz, hyk, hzk, rfl⟩ := exists_decomp_off k hΩ heq hline hu hc
  rw [dop_add, inner_add_right, hΨ y hy hyk, inner_dop_star hsym, hΨ z hz hzk, inner_zero_right,
    inner_zero_left, add_zero]

/-- **On `S` the centered combinations off the axis vanish**: `⟨Ψ, D_c Ψ'⟩ = 0`, by
polarization. -/
theorem inner_dop_eq_zero (hsym : ∀ p, (L p).IsSymmetric) (hu : u ≠ 0)
    {Ψ Ψ' : EuclideanSpace ℂ ι} (hΨ : InS L Φ k Ψ) (hΨ' : InS L Φ k Ψ')
    {c : Fin 2 × Fin n → ℂ} (hc : fiberPart k c = 0) : inner ℂ Ψ (dop L Φ c Ψ') = 0 := by
  have h1 := inner_dop_self k hΩ heq hline hsym hu (inS_add k hΨ hΨ' 1) hc
  have h2 := inner_dop_self k hΩ heq hline hsym hu (inS_add k hΨ hΨ' Complex.I) hc
  have h3 := inner_dop_self k hΩ heq hline hsym hu hΨ hc
  have h4 := inner_dop_self k hΩ heq hline hsym hu hΨ' hc
  simp only [one_smul, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_I, h3, h4] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 +
    ((inner ℂ Ψ (dop L Φ c Ψ') - inner ℂ Ψ' (dop L Φ c Ψ)) / 2) * Complex.I_sq

/-! ## 4. A line leaves a relation on the axis alone -/

/-- **At equality the relations do not cross an axis with a positive defect along a line.** -/
theorem not_line (hcomm : ∀ s t i j, i ≠ j → ∀ ψ, L (t, j) (L (s, i) ψ) = L (s, i) (L (t, j) ψ))
    (hsym : ∀ p, (L p).IsSymmetric)
    (hk : 0 < gramDefectC (fluct L Φ (0, k)) (fluct L Φ (1, k))) : False := by
  obtain ⟨_, ⟨a, ha, rfl⟩, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (map_fiberPart_ne_bot k hΩ heq)
  have ha' : gram ℂ (fluct L Φ) *ᵥ a = 0 := LinearMap.mem_ker.mp ha
  have hu : u ≠ 0 := by
    rintro rfl
    obtain ⟨s, hs⟩ := hline a ha'
    exact ha0 (by rw [hs, smul_zero])
  set e : Fin 2 × Fin n → ℂ := fun p => if p.2 = k then a p else 0
  set b : Fin 2 × Fin n → ℂ := fun p => if p.2 = k then 0 else a p
  have hab : a = b + e := funext fun p => by simp only [b, e, Pi.add_apply]; split_ifs <;> simp
  have hb : fiberPart k b = 0 := funext fun s => by simp [fiberPart_apply, b]
  have hΦ : InS L Φ k Φ := fun c hc _ => by rw [dop_self]; exact sum_eq_zero_of_mulVec L Φ hc
  have hM : InS L Φ k (dop L Φ e Φ) := fun c hc hck => by
    have hce : ∀ p q, c p ≠ 0 → e q ≠ 0 → p.2 ≠ q.2 := by
      intro p q hp hq
      have hq' : q.2 = k := by by_contra h; exact hq (by simp [e, h])
      rw [hq']
      intro hpk
      apply hp
      have := congrFun hck p.1
      rwa [fiberPart_apply, ← hpk] at this
    rw [dop_comm hcomm hce, hΦ c hc hck, map_zero]
  have hrel : dop L Φ e Φ = -dop L Φ b Φ := by
    have h := dop_self (L := L) (Φ := Φ) a
    rw [sum_eq_zero_of_mulVec L Φ ha', hab, dop_add] at h
    exact eq_neg_of_add_eq_zero_right h
  have hzero : dop L Φ e Φ = 0 := by
    have h := inner_dop_eq_zero k hΩ heq hline hsym hu hM hΦ hb
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    nth_rewrite 2 [hrel]
    rw [inner_neg_right, h, neg_zero]
  have hsum : dop L Φ e Φ = a (0, k) • fluct L Φ (0, k) + a (1, k) • fluct L Φ (1, k) := by
    rw [dop_self, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_eq_single k,
      Finset.sum_eq_single k]
    · simp [e]
    all_goals first
      | (intro j _ hj; simp [e, hj])
      | (intro h; exact absurd (Finset.mem_univ k) h)
  have hαβ : a (0, k) ≠ 0 ∨ a (1, k) ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (funext fun s => by fin_cases s <;> simp [fiberPart_apply, h.1, h.2])
  exact (ne_of_gt hk) (gramDefectC_eq_zero_of_rel (hsum ▸ hzero) hαβ)

end Line

/-- **At equality an axis with a positive defect is crossed by the relations in both
directions**: their parts on that axis fill `ℂ²`. -/
theorem map_fiberPart_eq_top
    (hcomm : ∀ s t i j, i ≠ j → ∀ ψ, L (t, j) (L (s, i) ψ) = L (s, i) (L (t, j) ψ))
    (hsym : ∀ p, (L p).IsSymmetric) (k : Fin n)
    (hk : 0 < gramDefectC (fluct L Φ (0, k)) (fluct L Φ (1, k)))
    (hΩ : (imMatrix L Φ).det ≠ 0) (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    (LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin).map (fiberPart k) = ⊤ := by
  set W := (LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin).map (fiberPart k)
  by_contra htop
  have h0 : Module.finrank ℂ W ≠ 0 :=
    fun h => map_fiberPart_ne_bot k hΩ heq (Submodule.finrank_eq_zero.mp h)
  have h2 : Module.finrank ℂ W ≤ 2 := by simpa using Submodule.finrank_le W
  have h1 : Module.finrank ℂ W = 1 := by
    by_contra h
    exact htop (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega))
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp h1
  refine not_line (u := (v : Fin 2 → ℂ)) k hΩ heq (fun a ha => ?_) hcomm hsym hk
  obtain ⟨s, hs⟩ := hv ⟨fiberPart k a, Submodule.mem_map_of_mem (LinearMap.mem_ker.mpr ha)⟩
  exact ⟨s, (congrArg Subtype.val hs).symm⟩

end RobertsonEqualityPlane
