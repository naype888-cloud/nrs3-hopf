/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The fibered wheel: the axes are the spokes, the closed axis `w` is the rim

`S` half-axes leave the origin, each with `m` positions out to its end `±1`; the closed axis `w`
is the rim joining neighbouring ends. Transport moves one step along a spoke, from the origin to
the first position of every spoke, or one step along the rim.

* **The star rotates.** Turning every spoke to the next one, `R : (s, j) ↦ (s + 1, j)`, keeps
  the origin and preserves every link: it is a symmetry of transport, so its eigenvalue `k` is
  conserved.
* **The cube ends where it begins.** `R^S = 1`; for `S = 2h`, `R^h` sends each half-axis to the
  opposite one, `+x` to `−x`.
* **In three dimensions.** With the six half-axes in the order `+x, +y, −z, −x, −y, +z` of the
  rim, one step of the rim is `M : e_x ↦ e_y, e_y ↦ −e_z, e_z ↦ e_x`, with `det M = −1`,
  `M³ = −1` and `M⁶ = 1`: a rotation by `60°` composed with the inversion through the origin.

## Main results

- `FiberedWheel.adj_rot` : the rotation of the star preserves every link.
- `FiberedWheel.rot_iterate`, `FiberedWheel.rot_period` : `R^k (s, j) = (s + k, j)`, `R^S = 1`.
- `FiberedWheel.M_rim` : `det M = −1`, `M³ = −1`, `M⁶ = 1`.
-/

@[expose] public section

namespace FiberedWheel

variable (S m : ℕ)

/-- The positions of the wheel: the origin (`none`) and position `j` of spoke `s`. -/
abbrev Site := Option (ZMod S × Fin m)

variable {S m}

/-- The links of the wheel: origin to the first position of a spoke, one step along a spoke,
and one step along the rim between the ends of neighbouring spokes. -/
def Adj : Site S m → Site S m → Prop
  | none, none => False
  | none, some (_, j) => j.val = 0
  | some (_, j), none => j.val = 0
  | some (s, j), some (t, k) =>
      (s = t ∧ (j.val + 1 = k.val ∨ k.val + 1 = j.val)) ∨
        (j.val + 1 = m ∧ k.val + 1 = m ∧ (t = s + 1 ∨ s = t + 1))

instance : DecidableRel (Adj (S := S) (m := m)) := fun u v => by
  cases u with
  | none => cases v with
    | none => exact inferInstanceAs (Decidable False)
    | some b => exact inferInstanceAs (Decidable (b.2.val = 0))
  | some a => cases v with
    | none => exact inferInstanceAs (Decidable (a.2.val = 0))
    | some b => unfold Adj; infer_instance

/-- The rotation of the star: every spoke to the next one, the origin fixed. -/
def rot : Site S m → Site S m
  | none => none
  | some (s, j) => some (s + 1, j)

/-- **The star rotates**: the rotation preserves every link of the wheel. -/
theorem adj_rot (u v : Site S m) : Adj (rot u) (rot v) ↔ Adj u v := by
  rcases u with _ | ⟨s, j⟩ <;> rcases v with _ | ⟨t, k⟩ <;> simp only [rot, Adj]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h1, h2, h | h⟩)
    · exact Or.inl ⟨add_right_cancel h, h'⟩
    · exact Or.inr ⟨h1, h2, Or.inl (add_right_cancel h)⟩
    · exact Or.inr ⟨h1, h2, Or.inr (add_right_cancel h)⟩
  · rintro (⟨rfl, h'⟩ | ⟨h1, h2, rfl | rfl⟩)
    · exact Or.inl ⟨rfl, h'⟩
    · exact Or.inr ⟨h1, h2, Or.inl (by ring)⟩
    · exact Or.inr ⟨h1, h2, Or.inr (by ring)⟩

theorem rot_iterate (k : ℕ) (s : ZMod S) (j : Fin m) :
    rot^[k] (some (s, j)) = some (s + k, j) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, show rot (some (s, j)) = some (s + 1, j) from rfl, ih]
    push_cast; ring_nf

/-- **The cube ends where it begins**: `S` turns of the star are the identity. -/
theorem rot_period : rot^[S] = (id : Site S m → Site S m) := by
  funext u
  rcases u with _ | ⟨s, j⟩
  · have h (k : ℕ) : rot^[k] (none : Site S m) = none := by
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
    exact h S
  · rw [rot_iterate, ZMod.natCast_self, add_zero]; rfl

/-! ## The rim in three dimensions -/

/-- One step of the rim on the six half-axes `+x, +y, −z, −x, −y, +z`. -/
def M : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 0; 0, -1, 0]

/-- **One step of the rim is a rotation by `60°` with the inversion**: `det M = −1`,
`M³ = −1`, `M⁶ = 1`. -/
theorem M_rim : M.det = -1 ∧ M ^ 3 = -1 ∧ M ^ 6 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

end FiberedWheel
