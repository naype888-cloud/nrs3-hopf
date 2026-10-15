/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith

/-!
# A simple quotient comes from one axis

Let `𝔥` be the Lie algebra of the visible axes of the box, and `M_x`, `M_y`, `M_z` the parts of
`𝔥` that vanish on `x`, on `y`, on `z`: three ideals meeting in `0`. If `ψ : 𝔥 → 𝔰` is onto a
simple Lie algebra (`sl(3)` on the closed fiber), each image `ψ(M_i)` is `0` or `𝔰`; if all three
were `𝔰`, so would be `ψ ⁅⁅M_x, M_y⁆, M_z⁆ = ⁅⁅𝔰, 𝔰⁆, 𝔰⁆`, inside `ψ(M_x ⊓ M_y ⊓ M_z) = 0`. So
some `M_i` lies in the kernel: `ψ` factors through one axis.

On that axis the algebra is either abelian, which has no simple quotient, or simple, and then
`ψ` is an isomorphism and both have the same dimension. The open axes have dimension
`d(d ± 1)/2`, never `8 = dim sl(3)`.

## Main results

- `SimpleQuotient.lie_top_eq_top` : a simple Lie algebra is its own derived algebra.
- `SimpleQuotient.exists_le_ker` : with three ideals meeting in `0`, one lies in the kernel.
- `SimpleQuotient.not_surjective_of_abelian` : an abelian Lie algebra has no simple quotient.
- `SimpleQuotient.finrank_eq_of_surjective` : a surjection between simple Lie algebras keeps the
  dimension.
- `SimpleQuotient.so_sp_ne_eight` : `d(d + 1) ≠ 16` and `d(d − 1) ≠ 16`.
-/

@[expose] public section

namespace SimpleQuotient

variable {R L S : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing S] [LieAlgebra R S]

/-- **A simple Lie algebra is its own derived algebra.** -/
theorem lie_top_eq_top [LieAlgebra.IsSimple R S] :
    ⁅(⊤ : LieIdeal R S), (⊤ : LieIdeal R S)⁆ = (⊤ : LieIdeal R S) := by
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (R := R) (L := S)
      ⁅(⊤ : LieIdeal R S), (⊤ : LieIdeal R S)⁆ with h | h
  · exfalso
    apply LieAlgebra.IsSimple.non_abelian (R := R) (L := S)
    refine ⟨fun x y => ?_⟩
    exact (LieSubmodule.lie_eq_bot_iff _ _).mp h x trivial y trivial
  · exact h

theorem top_ne_bot [LieAlgebra.IsSimple R S] : (⊤ : LieIdeal R S) ≠ ⊥ := by
  intro h
  apply LieAlgebra.IsSimple.non_abelian (R := R) (L := S)
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : LieIdeal R S) := h ▸ trivial
  rw [LieSubmodule.mem_bot] at hx
  rw [hx, zero_lie]

/-- **With three ideals meeting in `0`, one lies in the kernel** of a surjection onto a simple
Lie algebra. -/
theorem exists_le_ker [LieAlgebra.IsSimple R S] (ψ : L →ₗ⁅R⁆ S) (hψ : Function.Surjective ψ)
    (M₁ M₂ M₃ : LieIdeal R L) (h : M₁ ⊓ M₂ ⊓ M₃ = ⊥) :
    M₁ ≤ ψ.ker ∨ M₂ ≤ ψ.ker ∨ M₃ ≤ ψ.ker := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂, h₃⟩ := hcon
  have top (M : LieIdeal R L) (hM : ¬ M ≤ ψ.ker) : M.map ψ = ⊤ :=
    (LieAlgebra.IsSimple.eq_bot_or_eq_top _).resolve_left
      (fun hb => hM (LieIdeal.map_eq_bot_iff.mp hb))
  have hle : ⁅⁅M₁, M₂⁆, M₃⁆ ≤ M₁ ⊓ M₂ ⊓ M₃ :=
    (LieSubmodule.lie_le_inf _ _).trans (inf_le_inf_right _ (LieSubmodule.lie_le_inf _ _))
  rw [h, le_bot_iff] at hle
  have hmap := congrArg (LieIdeal.map ψ) hle
  rw [LieIdeal.map_bracket_eq ψ hψ, LieIdeal.map_bracket_eq ψ hψ, top M₁ h₁, top M₂ h₂,
    top M₃ h₃, lie_top_eq_top, lie_top_eq_top, LieIdeal.map_eq_bot_iff.mpr bot_le] at hmap
  exact top_ne_bot hmap

/-- **An abelian Lie algebra has no simple quotient.** -/
theorem not_surjective_of_abelian [LieAlgebra.IsSimple R S] [IsLieAbelian L] (ψ : L →ₗ⁅R⁆ S) :
    ¬ Function.Surjective ψ := by
  intro hψ
  apply LieAlgebra.IsSimple.non_abelian (R := R) (L := S)
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hψ x
  obtain ⟨b, rfl⟩ := hψ y
  rw [← LieHom.map_lie, trivial_lie_zero, map_zero]

/-- **A surjection between simple Lie algebras keeps the dimension.** -/
theorem finrank_eq_of_surjective {K : Type*} [Field K] {L S : Type*} [LieRing L] [LieAlgebra K L]
    [LieRing S] [LieAlgebra K S] [LieAlgebra.IsSimple K L] [LieAlgebra.IsSimple K S]
    (ψ : L →ₗ⁅K⁆ S) (hψ : Function.Surjective ψ) :
    Module.finrank K L = Module.finrank K S := by
  have hker : ψ.ker = ⊥ := by
    refine (LieAlgebra.IsSimple.eq_bot_or_eq_top ψ.ker).resolve_right fun htop => ?_
    apply top_ne_bot (R := K) (S := S)
    rw [eq_bot_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := hψ y
    have : x ∈ ψ.ker := htop ▸ trivial
    rw [LieHom.mem_ker] at this
    rw [this]; exact LieSubmodule.zero_mem _
  have hinj : Function.Injective ψ := (LieHom.ker_eq_bot ψ).mp hker
  exact LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective (ψ : L →ₗ[K] S) ⟨hinj, hψ⟩)

/-- **The open axes never have the dimension of `sl(3)`**: `d(d + 1)/2` and `d(d − 1)/2` are
never `8`. -/
theorem so_sp_ne_eight (d : ℕ) : d * (d + 1) ≠ 16 ∧ d * (d - 1) ≠ 16 := by
  rcases Nat.lt_or_ge d 6 with h | h
  · interval_cases d <;> decide
  · constructor
    · nlinarith
    · have : 6 * 5 ≤ d * (d - 1) := Nat.mul_le_mul h (by omega)
      omega

end SimpleQuotient
