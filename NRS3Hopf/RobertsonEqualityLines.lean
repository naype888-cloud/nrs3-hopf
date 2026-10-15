/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49h_DeterminantEqualityRelation

/-!
# Lines on `n` axes

Coefficient vectors on `n` axes, two coefficients per axis, live in `ℂ^(2 × n)`. If the `2 × 2`
determinants `σ_i(a, b) = a_{0,i} b_{1,i} − a_{1,i} b_{0,i}` vanish on a subspace `N`, the part of
`N` on each axis is a line; `n` lines against `dim N ≥ n` leave a nonzero vector of `N` on any
chosen axis alone. This is the linear algebra of the equality case of Robertson 1934
(`RobertsonEquality`).

## Main results

- `RobertsonEquality.exists_line` : vanishing `σ_i` make the part on axis `i` a line.
- `RobertsonEquality.exists_single_axis` : a nonzero vector on any chosen axis alone.
-/

@[expose] public noncomputable section

namespace RobertsonEquality

variable {n : ℕ}

/-! ## 1. Lines on `n` axes -/

/-- The part of a coefficient vector on axis `i`. -/
def restr (i : Fin n) : (Fin 2 × Fin n → ℂ) →ₗ[ℂ] (Fin 2 × Fin n → ℂ) :=
  LinearMap.pi fun p => if p.2 = i then LinearMap.proj p else 0

theorem restr_apply (i : Fin n) (a : Fin 2 × Fin n → ℂ) (p : Fin 2 × Fin n) :
    restr i a p = if p.2 = i then a p else 0 := by
  simp only [restr, LinearMap.pi_apply]
  split_ifs <;> simp

/-- If the `2 × 2` determinants `σ_i` vanish on `N`, the part of `N` on axis `i` is a line. -/
theorem exists_line (N : Submodule ℂ (Fin 2 × Fin n → ℂ)) (i : Fin n)
    (hσ : ∀ a ∈ N, ∀ b ∈ N, a (0, i) * b (1, i) - a (1, i) * b (0, i) = 0) :
    ∃ g, ∀ a ∈ N, ∃ t : ℂ, restr i a = t • g := by
  by_cases h : ∃ a₀ ∈ N, a₀ (0, i) ≠ 0 ∨ a₀ (1, i) ≠ 0
  · obtain ⟨a₀, ha₀, h0⟩ := h
    refine ⟨restr i a₀, fun a ha => ?_⟩
    have hs := hσ a₀ ha₀ a ha
    rcases h0 with h0 | h0
    · refine ⟨a (0, i) / a₀ (0, i), ?_⟩
      ext ⟨s, j⟩
      simp only [restr_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs with hj
      · subst hj
        rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
        · field_simp
        · field_simp
          linear_combination hs
      · simp
    · refine ⟨a (1, i) / a₀ (1, i), ?_⟩
      ext ⟨s, j⟩
      simp only [restr_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs with hj
      · subst hj
        rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
        · field_simp
          linear_combination -hs
        · field_simp
      · simp
  · push Not at h
    refine ⟨0, fun a ha => ⟨0, ?_⟩⟩
    ext ⟨s, j⟩
    simp only [restr_apply, smul_zero, Pi.zero_apply]
    split_ifs with hj
    · subst hj
      rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
      exacts [(h a ha).1, (h a ha).2]
    · rfl

/-- **`n` lines against dimension `n` leave a vector on any chosen axis `k` alone.** -/
theorem exists_single_axis (N : Submodule ℂ (Fin 2 × Fin n → ℂ)) (hdim : n ≤ Module.finrank ℂ N)
    (hσ : ∀ a ∈ N, ∀ b ∈ N, ∀ i, a (0, i) * b (1, i) - a (1, i) * b (0, i) = 0) (k : Fin n) :
    ∃ a ∈ N, a ≠ 0 ∧ ∀ s i, i ≠ k → a (s, i) = 0 := by
  choose g hg using fun i => exists_line N i fun a ha b hb => hσ a ha b hb i
  set P := (∑ i ∈ Finset.univ.erase k, restr i) ∘ₗ N.subtype
  have hrange : LinearMap.range P ≤
      Submodule.span ℂ (Set.range fun i : (Finset.univ.erase k : Finset (Fin n)) => g i) := by
    rintro _ ⟨x, rfl⟩
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨t, ht⟩ := hg i x x.2
    rw [ht]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  have hr : Module.finrank ℂ (LinearMap.range P) ≤ n - 1 :=
    (Submodule.finrank_mono hrange).trans ((finrank_range_le_card _).trans (by simp))
  have hrn := LinearMap.finrank_range_add_finrank_ker P
  have hn : 0 < n := Fin.pos k
  have hker : LinearMap.ker P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrn
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, x.2, fun h => hx0 (Subtype.ext h), fun s i hi => ?_⟩
  have hP := congrFun (show P x = 0 from hx) (s, i)
  simp only [P, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
    Finset.sum_apply, restr_apply, Pi.zero_apply] at hP
  rw [Finset.sum_ite_eq] at hP
  simpa [hi] using hP

end RobertsonEquality
