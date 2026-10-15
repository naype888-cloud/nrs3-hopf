/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.RobertsonEquality
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# At equality an axis with a defect couples to the others

The equality case of Robertson 1934 on `n` axes (`RobertsonEquality`), one step further. Let
`c_p` be the `2n` fluctuation vectors, `V` their complex span and `k` an axis with a positive
defect, so that `c_{0,k}`, `c_{1,k}` are independent.

* At equality the relations have dimension at least `n`, so `dim V ≤ n`.
* `det Ω ≠ 0` and equality make `Σ` invertible: the `2n` vectors are independent over `ℝ`, and
  the `2n − 2` vectors off axis `k` span a complex space of dimension at least `n − 1`.
* If the span `V_k` of the two vectors of axis `k` met the span `V_r` of the others only in `0`,
  `dim V = dim V_r + 2 ≥ n + 1`.

So `V_k ∩ V_r ≠ 0`: some combination `α c_{0,k} + β c_{1,k} ≠ 0` is a combination of the
fluctuation vectors of the other axes. On the box with the hidden closed fiber this is the
coupling `(α T° + β P₃ − λ) Φ = B Φ`, with `B` made of the observables of `x`, `y`, `z`.

## Main results

- `RobertsonCoupling.finrank_span_le` : at equality `dim V ≤ n`.
- `RobertsonCoupling.linearIndependent_real` : `Σ` invertible makes the vectors independent over
  `ℝ`.
- `RobertsonCoupling.exists_coupling` : the axis with a defect couples to the other axes.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant CauchyGram SpectralExtremal
open scoped ComplexOrder

namespace RobertsonCoupling

open RobertsonEquality

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {L : Fin 2 × Fin n → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} {Φ : EuclideanSpace ℂ ι}

/-- The combination `a ↦ Σ_p a_p c_p`. -/
def comb (L : Fin 2 × Fin n → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Φ : EuclideanSpace ℂ ι) : (Fin 2 × Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Fintype.linearCombination ℂ (fluct L Φ)

theorem comb_apply (a : Fin 2 × Fin n → ℂ) : comb L Φ a = ∑ p, a p • fluct L Φ p := by
  simp [comb, Fintype.linearCombination_apply]

/-- The relations are the kernel of `a ↦ Σ_p a_p c_p`. -/
theorem ker_comb : LinearMap.ker (comb L Φ) = LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin := by
  ext a
  simp only [LinearMap.mem_ker, comb_apply, Matrix.mulVecLin_apply]
  constructor
  · intro h
    funext i
    simp only [Matrix.mulVec, dotProduct, gram, of_apply, Pi.zero_apply]
    rw [show ∑ j, inner ℂ (fluct L Φ i) (fluct L Φ j) * a j =
      inner ℂ (fluct L Φ i) (∑ j, a j • fluct L Φ j) by
        rw [inner_sum]; exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right, mul_comm]]
    rw [h, inner_zero_right]
  · exact fun h => sum_eq_zero_of_mulVec L Φ h

/-- **At equality `dim V ≤ n`.** -/
theorem finrank_span_le (hΩ : (imMatrix L Φ).det ≠ 0)
    (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    Module.finrank ℂ (LinearMap.range (comb L Φ)) ≤ n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (comb L Φ)
  have h2 := le_finrank_ker (L := L) (Φ := Φ) hΩ heq
  rw [ker_comb] at h1
  rw [Module.finrank_fintype_fun_eq_card] at h1
  simp only [Fintype.card_prod, Fintype.card_fin] at h1
  omega

/-- A real combination that vanishes is in the kernel of `Σ`. -/
theorem covMatrix_mulVec_eq_zero {r : Fin 2 × Fin n → ℝ}
    (h : ∑ p, (r p : ℂ) • fluct L Φ p = 0) : (covMatrix L Φ).mulVec r = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, covMatrix, of_apply, covarianceG, Pi.zero_apply]
  have : ∑ j, (inner ℂ (centeredG (L i) Φ) (centeredG (L j) Φ)).re * r j =
      (inner ℂ (fluct L Φ i) (∑ j, (r j : ℂ) • fluct L Φ j)).re := by
    rw [inner_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [inner_smul_right, Complex.re_ofReal_mul, mul_comm]; rfl
  rw [this, h, inner_zero_right, Complex.zero_re]

/-- **`Σ` invertible makes the fluctuation vectors independent over `ℝ`.** -/
theorem linearIndependent_real (hΩ : (imMatrix L Φ).det ≠ 0)
    (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) {r : Fin 2 × Fin n → ℝ}
    (h : ∑ p, (r p : ℂ) • fluct L Φ p = 0) : r = 0 := by
  have hdet : (covMatrix L Φ).det ≠ 0 := by rw [heq]; exact abs_ne_zero.mpr hΩ
  by_contra hr
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨r, hr, covMatrix_mulVec_eq_zero h⟩)

variable (L Φ) in
/-- The combination of the fluctuation vectors off axis `k`. -/
def combOff (k : Fin n) : ({ p : Fin 2 × Fin n // p.2 ≠ k } → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Fintype.linearCombination ℂ fun q => fluct L Φ q.1

variable (L Φ) in
/-- The combination of the two fluctuation vectors of axis `k`. -/
def combAxis (k : Fin n) : (Fin 2 → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Fintype.linearCombination ℂ fun s => fluct L Φ (s, k)

theorem card_off (k : Fin n) : Fintype.card { p : Fin 2 × Fin n // p.2 ≠ k } = 2 * n - 2 := by
  rw [Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have : Fintype.card { p : Fin 2 × Fin n // p.2 = k } = 2 := by
    rw [Fintype.card_subtype]
    rw [show (Finset.univ.filter fun p : Fin 2 × Fin n => p.2 = k) =
      (Finset.univ : Finset (Fin 2)) ×ˢ {k} by ext ⟨a, b⟩; simp [eq_comm]]
    simp
  omega

/-- The two pieces add up to the full combination. -/
theorem comb_split (k : Fin n) (a : Fin 2 × Fin n → ℂ) :
    comb L Φ a = combOff L Φ k (fun q => a q.1) + combAxis L Φ k (fun s => a (s, k)) := by
  rw [comb_apply, ← Fintype.sum_subtype_add_sum_subtype (fun p : Fin 2 × Fin n => p.2 ≠ k)]
  simp only [combOff, combAxis, Fintype.linearCombination_apply]
  congr 1
  let e : { p : Fin 2 × Fin n // ¬ p.2 ≠ k } ≃ Fin 2 :=
    { toFun := fun p => p.1.1
      invFun := fun s => ⟨(s, k), by simp⟩
      left_inv := by
        rintro ⟨⟨s, j⟩, h⟩
        simp only [ne_eq, not_not] at h
        subst h; rfl
      right_inv := fun s => rfl }
  refine Fintype.sum_equiv e _ _ fun x => ?_
  obtain ⟨⟨s, j⟩, h⟩ := x
  simp only [ne_eq, not_not] at h
  subst h; rfl

/-- **The axis with a defect couples to the other axes.** At equality, with `det Ω ≠ 0` and a
positive defect on axis `k`, some nonzero combination of the two fluctuation vectors of axis
`k` is a combination of the fluctuation vectors of the other axes. -/
theorem exists_coupling (k : Fin n)
    (hk : 0 < gramDefectC (fluct L Φ (0, k)) (fluct L Φ (1, k)))
    (hΩ : (imMatrix L Φ).det ≠ 0) (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    ∃ b : Fin 2 → ℂ, combAxis L Φ k b ≠ 0 ∧ combAxis L Φ k b ∈ LinearMap.range (combOff L Φ k) := by
  by_contra hcon
  push Not at hcon
  -- the axis map is injective
  have hinj : Function.Injective (combAxis L Φ k) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    have hb' : b 0 ≠ 0 ∨ b 1 ≠ 0 := by
      by_contra h; push Not at h; exact hb0 (funext fun s => by fin_cases s <;> simp [h])
    have hrel : b 0 • fluct L Φ (0, k) + b 1 • fluct L Φ (1, k) = 0 := by
      simpa [combAxis, Fintype.linearCombination_apply, Fin.sum_univ_two] using hb
    exact (ne_of_gt hk) (gramDefectC_eq_zero_of_rel hrel hb')
  -- the two ranges meet only in 0
  have hdisj : LinearMap.range (combAxis L Φ k) ⊓ LinearMap.range (combOff L Φ k) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨b, rfl⟩, hx⟩
    by_contra h0
    exact (hcon b h0) hx
  -- both ranges sit in the full span
  have hle : LinearMap.range (combAxis L Φ k) ⊔ LinearMap.range (combOff L Φ k) ≤
      LinearMap.range (comb L Φ) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨b, rfl⟩
      refine ⟨fun p => if p.2 = k then b p.1 else 0, ?_⟩
      rw [comb_split k]
      have h0 : (fun q : { p : Fin 2 × Fin n // p.2 ≠ k } =>
          if q.1.2 = k then b q.1.1 else 0) = 0 := funext fun q => by simp [q.2]
      simp [h0]
    · rintro _ ⟨a, rfl⟩
      refine ⟨fun p => if h : p.2 = k then 0 else a ⟨p, h⟩, ?_⟩
      rw [comb_split k]
      have e1 : (fun q : { p : Fin 2 × Fin n // p.2 ≠ k } =>
          if h : q.1.2 = k then (0 : ℂ) else a ⟨q.1, h⟩) = a := funext fun q => by simp [q.2]
      have e2 : (fun s : Fin 2 => if h : ((s, k) : Fin 2 × Fin n).2 = k then (0 : ℂ)
          else a ⟨(s, k), h⟩) = 0 := funext fun s => by simp
      rw [e1, e2, map_zero, add_zero]
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (combAxis L Φ k))
    (LinearMap.range (combOff L Φ k))
  rw [hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fin_fun] at hrank
  have hsup := Submodule.finrank_mono hle
  have hV := finrank_span_le hΩ heq
  -- the real count
  set U := LinearMap.range (combOff L Φ k)
  let g : ({ p : Fin 2 × Fin n // p.2 ≠ k } → ℝ) →ₗ[ℝ] U :=
    { toFun := fun r => ⟨combOff L Φ k fun q => (r q : ℂ), ⟨_, rfl⟩⟩
      map_add' := fun r s => by
        ext1
        simp only [Pi.add_apply, Complex.ofReal_add, Submodule.coe_add]
        rw [← map_add]; rfl
      map_smul' := fun c r => by
        ext1
        simp only [RingHom.id_apply]
        rw [show (fun q => ((c • r) q : ℂ)) = (c : ℂ) • fun q => (r q : ℂ) by
          funext q; simp]
        rw [map_smul]; rfl }
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have hr' : combOff L Φ k (fun q => (r q : ℂ)) = 0 := congrArg Subtype.val hr
    have hz := linearIndependent_real (r := fun p => if h : p.2 = k then 0 else r ⟨p, h⟩) hΩ heq
      (by
        have := comb_split (L := L) (Φ := Φ) k
          (fun p => ((if h : p.2 = k then 0 else r ⟨p, h⟩ : ℝ) : ℂ))
        rw [comb_apply] at this
        rw [this]
        have e1 : (fun q : { p : Fin 2 × Fin n // p.2 ≠ k } =>
            (((if h : q.1.2 = k then 0 else r ⟨q.1, h⟩ : ℝ)) : ℂ)) = fun q => (r q : ℂ) :=
          funext fun q => by simp [q.2]
        have e2 : (fun s : Fin 2 => (((if h : ((s, k) : Fin 2 × Fin n).2 = k then 0
            else r ⟨(s, k), h⟩ : ℝ)) : ℂ)) = 0 := funext fun s => by simp
        rw [e1, e2, map_zero, add_zero]
        exact hr')
    funext q
    have := congrFun hz q.1
    simpa [q.2] using this
  have : Module.Finite ℝ U := Module.Finite.trans ℂ U
  have hreal := LinearMap.finrank_le_finrank_of_injective hginj
  rw [Module.finrank_fintype_fun_eq_card, card_off, finrank_real_of_complex] at hreal
  have hn : 1 ≤ n := Fin.pos k
  omega

end RobertsonCoupling
