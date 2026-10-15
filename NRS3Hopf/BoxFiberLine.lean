/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxEquality
public import NRS3Hopf.BoxTwoRelations

/-!
# At equality the relations meet the closed fiber in a line

Let `N` be the relations among the `2n` fluctuation vectors, the kernel of their Gram matrix
`G = Σ + iΩ`, and `π_k a = (a_{0,k}, a_{1,k})` the part of a relation on axis `k`.

* `G` is Hermitian, so the kernel of `Gᵀ` is the conjugate of `N`.
* At equality with `det Ω ≠ 0`, `N` and its conjugate span everything (`RobertsonEquality`), so
  `π_k N ≠ 0`: some relation passes through axis `k`.

On the box with `2` or `3` positions on `x`, `y`, `z` and the closed fiber, `π_w N` cannot be all
of `ℂ²` either: two relations with fiber parts `T°` and `P₃` leave no state
(`BoxTwoRelations`). So at equality `π_w N` is a line: the relations pass through the fiber
along one combination `α T° + β P₃` only.

## Main results

- `BoxFiberLine.star_mulVec_eq_zero` : the kernel of `Gᵀ` is the conjugate of the kernel of `G`.
- `BoxFiberLine.map_fiberPart_ne_bot` : at equality some relation passes through any axis.
- `BoxFiberLine.finrank_map_fiberPart_eq_one` : on the box with `2` or `3` positions on `x`,
  `y`, `z`, at equality the relations meet the closed fiber in a line.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant CauchyGram FourAxes CubeInBox
open RobertsonEquality

namespace BoxFiberLine

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {L : Fin 2 × Fin n → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} {Φ : EuclideanSpace ℂ ι}

/-- The part of a coefficient vector on axis `k`, `a ↦ (a_{0,k}, a_{1,k})`. -/
def fiberPart (k : Fin n) : (Fin 2 × Fin n → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun s => LinearMap.proj (s, k)

theorem fiberPart_apply (k : Fin n) (a : Fin 2 × Fin n → ℂ) (s : Fin 2) :
    fiberPart k a s = a (s, k) := rfl

/-- **The kernel of `Gᵀ` is the conjugate of the kernel of `G`**, since `G` is Hermitian. -/
theorem star_mulVec_eq_zero {v : Fin 2 × Fin n → EuclideanSpace ℂ ι} {x : Fin 2 × Fin n → ℂ}
    (h : (gram ℂ v)ᵀ *ᵥ x = 0) : gram ℂ v *ᵥ star x = 0 := by
  funext i
  have hi := congrArg (starRingEnd ℂ) (congrFun h i)
  simp only [Matrix.mulVec, dotProduct, transpose_apply, gram, of_apply, Pi.zero_apply,
    map_sum, map_mul, inner_conj_symm, map_zero] at hi
  simpa [Matrix.mulVec, dotProduct, gram] using hi

/-- **At equality some relation passes through any axis `k`**, when `det Ω ≠ 0`. -/
theorem map_fiberPart_ne_bot (k : Fin n) (hΩ : (imMatrix L Φ).det ≠ 0)
    (heq : (covMatrix L Φ).det = |(imMatrix L Φ).det|) :
    (LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin).map (fiberPart k) ≠ ⊥ := by
  intro hbot
  have hN (a) (ha : gram ℂ (fluct L Φ) *ᵥ a = 0) (s : Fin 2) : a (s, k) = 0 := by
    have : fiberPart k a ∈ (⊥ : Submodule ℂ (Fin 2 → ℂ)) :=
      hbot ▸ Submodule.mem_map_of_mem (LinearMap.mem_ker.mpr ha)
    exact congrFun ((Submodule.mem_bot ℂ).mp this) s
  have hx : (Pi.single (0, k) 1 : Fin 2 × Fin n → ℂ) ∈
      LinearMap.ker (gram ℂ (fluct L Φ)).mulVecLin ⊔
        LinearMap.ker (gram ℂ (fluct L Φ))ᵀ.mulVecLin := by
    rw [sup_ker_eq_top hΩ heq]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
  have hy0 := hN y hy 0
  have hz0 : z (0, k) = 0 := by
    have := hN _ (star_mulVec_eq_zero (LinearMap.mem_ker.mp hz)) 0
    simpa using this
  have := congrFun hyz (0, k)
  simp [hy0, hz0] at this

/-! ## The box -/

variable {dx dy dz : ℕ}

/-- **At equality the relations meet the closed fiber in a line.** On the box with `2` or `3`
positions on `x`, `y`, `z` and the closed fiber, for a unit state with `det Ω ≠ 0` and
`det Σ = |det Ω|`, the parts of the relations on the fiber form a line of `ℂ²`. -/
theorem finrank_map_fiberPart_eq_one (hx : dx = 2 ∨ dx = 3) (hy : dy = 2 ∨ dy = 3)
    (hz : dz = 2 ∨ dz = 3) {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0)
    (heq : (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det =
      |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det|) :
    Module.finrank ℂ ((LinearMap.ker
      (gram ℂ (fluct (boxPairs dx dy dz 3 closedPair) Φ)).mulVecLin).map (fiberPart 3)) = 1 := by
  set N := LinearMap.ker (gram ℂ (fluct (boxPairs dx dy dz 3 closedPair) Φ)).mulVecLin
  have hpos : Module.finrank ℂ (N.map (fiberPart 3)) ≠ 0 :=
    fun h => map_fiberPart_ne_bot 3 hΩ heq (Submodule.finrank_eq_zero.mp h)
  have hle : Module.finrank ℂ (N.map (fiberPart 3)) ≤ 2 := by
    simpa using Submodule.finrank_le (N.map (fiberPart 3))
  by_contra hne
  have htop : N.map (fiberPart 3) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
  have hpre (s : Fin 2) : ∃ a, gram ℂ (fluct (boxPairs dx dy dz 3 closedPair) Φ) *ᵥ a = 0 ∧
      a (s, 3) = 1 ∧ a (1 - s, 3) = 0 := by
    have : (Pi.single s 1 : Fin 2 → ℂ) ∈ N.map (fiberPart 3) := htop ▸ trivial
    obtain ⟨a, ha, hfa⟩ := this
    refine ⟨a, LinearMap.mem_ker.mp ha, ?_, ?_⟩
    · simpa [fiberPart_apply] using congrFun hfa s
    · have := congrFun hfa (1 - s)
      fin_cases s <;> simpa [fiberPart_apply] using this
  obtain ⟨a, ha, ha0, ha1⟩ := hpre 0
  obtain ⟨b, hb, hb1, hb0⟩ := hpre 1
  have h0 := BoxTwoRelations.eq_zero_of_relations hx hy hz
    (sum_eq_zero_of_mulVec _ Φ ha) (sum_eq_zero_of_mulVec _ Φ hb) ha0 ha1 hb0 hb1
  rw [h0, norm_zero] at hΦ
  exact zero_ne_one hΦ

end BoxFiberLine
