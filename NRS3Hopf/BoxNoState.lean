/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxEverySize

/-!
# Equality on the box leaves no state

The three axes of `BoxEverySize` put together. For each open axis, the fiber parts of the
elements of the algebra of the relations that vanish on that axis form a nonzero subspace of
traceless matrices, stable under `T°` and `P₃`: it contains every `E_ij` (`ClosedThreeIdeal`).
Take `Z_x`, `Z_y`, `Z_z` vanishing on `x`, `y`, `z`, with fiber parts `E₀₁`, `E₁₂`, `E₂₀`. Then
`[[Z_x, Z_y], Z_z]` and `[[Z_y, Z_z], Z_x]` vanish on `x`, `y`, `z`, are `E₀₀ − E₂₂` and
`E₁₁ − E₀₀` on the fiber, and annihilate `Φ`; with no common kernel, `Φ = 0`.

## Main results

- `BoxNoState.exists_single` : for each open axis, an element of the algebra vanishing on it
  with fiber part `E_ij`.
- `BoxNoState.eq_zero_of_det_eq` : for every size of `x`, `y`, `z`, equality with `det Ω ≠ 0`
  and the closed fiber in its band leaves no unit state.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant FourAxes CubeInBox
open BoxTwoRelations ClosedThreeIdeal RobertsonEquality BoxFiberLine BoxEverySize

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace BoxNoState

variable {dx dy dz d : ℕ} {Φ : H4D dx dy dz 3}

/-- **For each open axis, an element vanishing on it with fiber part `E_ij`.** -/
theorem exists_single (π : Axes dx dy dz →ₗ⁅ℂ⁆ Matrix (Fin d) (Fin d) ℂ)
    {La Lb : Axes dx dy dz} (ha : La ∈ alg Φ) (hb : Lb ∈ alg Φ) {a₀ a₁ b₀ b₁ : ℂ}
    (hπa : π La = a₀ • Td d + a₁ • Pd d) (hπb : π Lb = b₀ • Td d + b₁ • Pd d)
    (hρa : πw La = ClosedThree.Tc) (hρb : πw Lb = Pd 3) {i j : Fin 3} (hij : i ≠ j) :
    ∃ Z ∈ alg Φ, π Z = 0 ∧ πw Z = E i j := by
  set J := ((alg Φ).toSubmodule ⊓ LinearMap.ker π.toLinearMap).map
    (πw (dx := dx) (dy := dy) (dz := dz)).toLinearMap
  have hmem {F} : F ∈ J ↔ ∃ Z ∈ alg Φ, π Z = 0 ∧ πw Z = F := by
    simp only [J, Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker,
      LieSubalgebra.mem_toSubmodule, LieHom.coe_toLinearMap]
    constructor
    · rintro ⟨Z, ⟨hZ, h0⟩, rfl⟩; exact ⟨Z, hZ, h0, rfl⟩
    · rintro ⟨Z, hZ, h0, rfl⟩; exact ⟨Z, ⟨hZ, h0⟩, rfl⟩
  have stable {L : Axes dx dy dz} (hL : L ∈ alg Φ) : ∀ F ∈ J, ⁅πw L, F⁆ ∈ J := by
    intro F hF
    obtain ⟨Z, hZ, h0, rfl⟩ := hmem.mp hF
    exact hmem.mpr ⟨⁅L, Z⁆, LieSubalgebra.lie_mem _ hL hZ,
      by rw [LieHom.map_lie, h0, lie_zero], LieHom.map_lie _ _ _⟩
  have hT : ∀ F ∈ J, ⁅ClosedThree.Tc, F⁆ ∈ J := hρa ▸ stable ha
  have hP : ∀ F ∈ J, ⁅Pd 3, F⁆ ∈ J := hρb ▸ stable hb
  have htr : ∀ F ∈ J, F.trace = 0 := by
    intro F hF
    obtain ⟨Z, hZ, -, rfl⟩ := hmem.mp hF
    exact trace_πw Φ hZ
  have hne : J ≠ ⊥ := by
    obtain ⟨Z, hZ, h0, hw⟩ := exists_off_axis π πw ha hb hπa hπb hρa hρb
    intro hbot
    have : πw Z ∈ J := hmem.mpr ⟨Z, hZ, h0, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hw this
  exact hmem.mp (single_mem hT hP htr hne hij)

theorem lam_of_zero {Z : Axes dx dy dz} (hx : Z.1 = 0) (hy : Z.2.1 = 0) (hz : Z.2.2.1 = 0) :
    lam Z = liftAlong (eW dx dy dz 3) Z.2.2.2 := by
  simp [lam, hx, hy, hz, liftAlong_zero]

theorem no_common_kernel (v : Fin 3 → ℂ) (h₁ : (E 0 0 - E 2 2) *ᵥ v = 0)
    (h₂ : (E 1 1 - E 0 0) *ᵥ v = 0) : v = 0 := by
  have a0 := congrFun h₁ 0
  have a2 := congrFun h₁ 2
  have b1 := congrFun h₂ 1
  simp [Matrix.mulVec, dotProduct, single_apply] at a0 a2 b1
  funext i
  fin_cases i
  exacts [a0, b1, a2]

/-- **Equality on the box leaves no state**, for every size of `x`, `y`, `z`: with the closed
fiber in its band and `det Ω ≠ 0`, Robertson 1934 is never an equality on a unit state. -/
theorem eq_zero_of_det_eq (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|)
    (hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0)
    (heq : (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det =
      |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det|) : False := by
  have htop := RobertsonEqualityPlane.map_fiberPart_eq_top
    (fun s t i j h ψ => BoxCommute.boxPairs_comm closedPair s t i j h ψ) boxPairs_isSymmetric 3
    (ClosedAxisEntangled.gramDefect_box_pos hΦ hb) hΩ heq
  have hpre (s : Fin 2) : ∃ a ∈ rel Φ, a (s, 3) = 1 ∧ a (1 - s, 3) = 0 := by
    have : (Pi.single s 1 : Fin 2 → ℂ) ∈
        (LinearMap.ker (gram ℂ (fluct (boxPairs dx dy dz 3 closedPair) Φ)).mulVecLin).map
          (fiberPart 3) := htop ▸ trivial
    obtain ⟨a, ha, hfa⟩ := this
    refine ⟨a, LinearMap.mem_ker.mp ha, ?_, ?_⟩
    · simpa [fiberPart_apply] using congrFun hfa s
    · have := congrFun hfa (1 - s)
      fin_cases s <;> simpa [fiberPart_apply] using this
  obtain ⟨a, ha, ha0, ha1⟩ := hpre 0
  obtain ⟨b, hb', hb1, hb0⟩ := hpre 1
  have hw := fiber_parts (dx := dx) (dy := dy) (dz := dz) ha0 ha1 hb0 hb1
  have mA : axesOf a ∈ alg Φ := LieSubalgebra.subset_lieSpan ⟨a, ha, rfl⟩
  have mB : axesOf b ∈ alg Φ := LieSubalgebra.subset_lieSpan ⟨b, hb', rfl⟩
  obtain ⟨Zx, hZx, hx0, hxw⟩ := exists_single πx mA mB rfl rfl hw.1 hw.2 (i := 0) (j := 1)
    (by decide)
  obtain ⟨Zy, hZy, hy0, hyw⟩ := exists_single πy mA mB rfl rfl hw.1 hw.2 (i := 1) (j := 2)
    (by decide)
  obtain ⟨Zz, hZz, hz0, hzw⟩ := exists_single πz mA mB rfl rfl hw.1 hw.2 (i := 2) (j := 0)
    (by decide)
  have hπ {d' : ℕ} (π : Axes dx dy dz →ₗ⁅ℂ⁆ Matrix (Fin d') (Fin d') ℂ) {X Y Z : Axes dx dy dz}
      (h : π X = 0 ∨ π Y = 0 ∨ π Z = 0) : π ⁅⁅X, Y⁆, Z⁆ = 0 := by
    rw [LieHom.map_lie, LieHom.map_lie]
    rcases h with h | h | h <;> simp [h]
  have k₁ := kill Φ (LieSubalgebra.lie_mem _ hZx hZy) hZz
  have k₂ := kill Φ (LieSubalgebra.lie_mem _ hZy hZz) hZx
  rw [lam_of_zero (hπ πx (Or.inl hx0)) (hπ πy (Or.inr (Or.inl hy0)))
    (hπ πz (Or.inr (Or.inr hz0))), toOp_apply] at k₁
  rw [lam_of_zero (hπ πx (Or.inr (Or.inr hx0))) (hπ πy (Or.inl hy0))
    (hπ πz (Or.inr (Or.inl hz0))), toOp_apply] at k₂
  have w₁ : (⁅⁅Zx, Zy⁆, Zz⁆).2.2.2 = E 0 0 - E 2 2 := by
    rw [← πw_apply, LieHom.map_lie, LieHom.map_lie, hxw, hyw, hzw, lie_E_E (by decide),
      Ring.lie_def, single_mul_single_same, single_mul_single_same, mul_one]
  have w₂ : (⁅⁅Zy, Zz⁆, Zx⁆).2.2.2 = E 1 1 - E 0 0 := by
    rw [← πw_apply, LieHom.map_lie, LieHom.map_lie, hxw, hyw, hzw, lie_E_E (by decide),
      Ring.lie_def, single_mul_single_same, single_mul_single_same, mul_one]
  rw [w₁] at k₁
  rw [w₂] at k₂
  have h0 := eq_zero_of_lift₂ (eW dx dy dz 3) (fun v h₁ h₂ => no_common_kernel v h₁ h₂) k₁ k₂
  rw [h0, norm_zero] at hΦ
  exact zero_ne_one hΦ

end BoxNoState
