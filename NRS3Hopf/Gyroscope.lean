/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.RotationFiber
public import NRS3Hopf.BoxTwoRelations

/-!
# The box is a gyroscope: the rotation of the closed fiber is conserved by every transport

The transport of the box is the sum over the axes, `H = T_x + T_y + T_z + T°`. The angular
momentum `L` of the closed fiber commutes with `T°` (`RotationFiber.lie_Tc_Lr`), and operators of
different axes commute (`BoxCommute`), so `[H, L_w] = 0`: whatever moves on `x`, `y`, `z`, the
rotation of the fiber is conserved. The open axes carry transport and no conserved rotation
(`OpenNoRotation.open_no_rotation`): `x`, `y`, `z` are the frame, `w` is the rotor.

## Main results

- `Gyroscope.boxTransport` : `H = T_x + T_y + T_z + T°`.
- `Gyroscope.lie_boxTransport_Lw` : `[H, L_w] = 0`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition FourAxes BoxTwoRelations PathGraph3DNRS

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace Gyroscope

variable (dx dy dz : ℕ)

/-- The transport of the box, `H = T_x + T_y + T_z + T°`. -/
def boxTransport : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ :=
  lam (Td dx, Td dy, Td dz, ClosedThree.Tc)

/-- The angular momentum of the fiber, lifted to the box. -/
def Lw : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ :=
  lam ((0 : Matrix (Fin dx) (Fin dx) ℂ), (0 : Matrix (Fin dy) (Fin dy) ℂ),
    (0 : Matrix (Fin dz) (Fin dz) ℂ), RotationFiber.Lr)

theorem Lw_eq : Lw dx dy dz = liftAlong (eW dx dy dz 3) RotationFiber.Lr := by
  simp [Lw, lam, liftAlong_zero]

/-- **The box is a gyroscope**: the rotation of the closed fiber commutes with the transport of
the whole box. -/
theorem lie_boxTransport_Lw : ⁅boxTransport dx dy dz, Lw dx dy dz⁆ = 0 := by
  rw [boxTransport, Lw, ← lam_lie]
  have h : ⁅((Td dx, Td dy, Td dz, ClosedThree.Tc) : Axes dx dy dz),
      ((0 : Matrix (Fin dx) (Fin dx) ℂ), (0 : Matrix (Fin dy) (Fin dy) ℂ),
        (0 : Matrix (Fin dz) (Fin dz) ℂ), RotationFiber.Lr)⁆ = 0 := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · rw [lie_fst]; exact lie_zero _
    · rw [lie_snd_fst]; exact lie_zero _
    · rw [lie_snd_snd_fst]; exact lie_zero _
    · rw [lie_snd_snd_snd]; exact RotationFiber.lie_Tc_Lr
  rw [h, map_zero]

end Gyroscope
