/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.HodgeCubeD
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The adjoint of the coboundary on the open axes

`HodgeCubeD.d_adjoint` needs a finite site set. Here the sites are arbitrary (the open axes `ℤ`
included) and the inner product is a `finsum` over the sites, for the cochains of finite support:
in every degree `T`, only finitely many sites `p` have `ω (p, T) ≠ 0`.

## Main results

- `HodgeCubeFin.ipf` : the inner product, `Σ_T Σᶠ_p ω(p, T) η(p, T)`.
- `HodgeCubeFin.key_shift_fin` : the shift by `1_i` moves from `ω` to `η`, as a `finsum`.
- `HodgeCubeFin.d_adjoint_fin` : `⟨d ω, η⟩ = ⟨ω, δ η⟩` for cochains of finite support, on any
  groups on the axes.
-/

@[expose] public noncomputable section

namespace HodgeCubeFin

open HodgeCube HodgeCubeD

variable {n : ℕ} {Z : Fin n → Type*} [∀ i, AddCommGroup (Z i)] [∀ i, One (Z i)]

/-- The cochains of finite support: in every degree, finitely many sites carry a value. -/
def FinSupp (ω : Cochain Z) : Prop :=
  ∀ T : Finset (Fin n), (Function.support fun p : Site Z => ω (p, T)).Finite

/-- The inner product of two cochains of finite support. -/
def ipf (ω η : Cochain Z) : ℝ :=
  ∑ T : Finset (Fin n), ∑ᶠ p : Site Z, ω (p, T) * η (p, T)

/-- The shift by `1_i` moves from `ω` to `η`, as a `finsum` over the sites. -/
theorem key_shift_fin (ω η : Cochain Z) (hω : FinSupp ω) (hη : FinSupp η)
    (S : Finset (Fin n)) (i : Fin n) :
    ∑ᶠ p : Site Z, (sigma i (insert i S) : ℝ) * (ω (p + unit {i}, S) - ω (p, S))
        * η (p, insert i S)
      = ∑ᶠ p : Site Z, ω (p, S) * ((sigma i (insert i S) : ℝ) *
          (η (p - unit {i}, insert i S) - η (p, insert i S))) := by
  set σ : ℝ := (sigma i (insert i S) : ℝ) with hσ
  have e1 : ∀ p : Site Z, σ * (ω (p + unit {i}, S) - ω (p, S)) * η (p, insert i S)
      = σ * (ω (p + unit {i}, S) * η (p, insert i S))
        - σ * (ω (p, S) * η (p, insert i S)) := fun p => by ring
  have e2 : ∀ p : Site Z, ω (p, S) * (σ * (η (p - unit {i}, insert i S) - η (p, insert i S)))
      = σ * (ω (p, S) * η (p - unit {i}, insert i S))
        - σ * (ω (p, S) * η (p, insert i S)) := fun p => by ring
  have hA : (Function.support fun p : Site Z =>
      σ * (ω (p + unit {i}, S) * η (p, insert i S))).Finite :=
    (hη (insert i S)).subset fun p hp h0 => hp (by simp [h0])
  have hB : (Function.support fun p : Site Z => σ * (ω (p, S) * η (p, insert i S))).Finite :=
    (hη (insert i S)).subset fun p hp h0 => hp (by simp [h0])
  have hC : (Function.support fun p : Site Z =>
      σ * (ω (p, S) * η (p - unit {i}, insert i S))).Finite :=
    (hω S).subset fun p hp h0 => hp (by simp [h0])
  simp only [e1, e2]
  rw [finsum_sub_distrib hA hB, finsum_sub_distrib hC hB]
  congr 1
  let g : Site Z → ℝ := fun q => σ * (ω (q, S) * η (q - unit {i}, insert i S))
  calc ∑ᶠ p : Site Z, σ * (ω (p + unit {i}, S) * η (p, insert i S))
      = ∑ᶠ p : Site Z, g (Equiv.addRight (unit {i}) p) := finsum_congr fun p => by simp [g]
    _ = ∑ᶠ q : Site Z, g q := finsum_comp_equiv _

/-- **`d` and `δ` are adjoint on cochains of finite support**: `⟨d ω, η⟩ = ⟨ω, δ η⟩`. -/
theorem d_adjoint_fin (ω η : Cochain Z) (hω : FinSupp ω) (hη : FinSupp η) :
    ipf (d ω) η = ipf ω (codiff η) := by
  classical
  unfold ipf
  have hL : ∀ T : Finset (Fin n), ∑ᶠ p : Site Z, d ω (p, T) * η (p, T)
      = ∑ i ∈ T, ∑ᶠ p : Site Z, (sigma i T : ℝ) *
          (ω (p + unit {i}, T.erase i) - ω (p, T.erase i)) * η (p, T) := by
    intro T
    simp only [d, Finset.sum_mul]
    exact finsum_sum_comm T _ fun i _ => (hη T).subset fun p hp h0 => hp (by simp [h0])
  have hR : ∀ S : Finset (Fin n), ∑ᶠ p : Site Z, ω (p, S) * codiff η (p, S)
      = ∑ i ∈ Sᶜ, ∑ᶠ p : Site Z, ω (p, S) * ((sigma i (insert i S) : ℝ) *
          (η (p - unit {i}, insert i S) - η (p, insert i S))) := by
    intro S
    simp only [codiff, Finset.mul_sum]
    exact finsum_sum_comm Sᶜ _ fun i _ => (hω S).subset fun p hp h0 => hp (by simp [h0])
  simp only [hL, hR]
  refine (sum_cells_swap _).trans ?_
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.erase_insert (Finset.mem_compl.mp hi)]
  exact key_shift_fin ω η hω hη S i

end HodgeCubeFin
