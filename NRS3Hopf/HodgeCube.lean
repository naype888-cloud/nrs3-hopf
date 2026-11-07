/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

/-!
# The discrete Hodge star on the box with the fiber

The box has `n` axes (`n = 4`: `x, y, z, w`; `n = 3`: the three-torus), one group `Z i` per axis (the three open axes `ℤ` and the
closed fiber `ZMod 3` are instances). A `k`-cochain assigns a number to every cell `(p, S)`: a
site `p` and a set `S` of `k` axes, the cell spanned from `p` by one step along each axis of `S`.

The dual cell of `(p, S)` is spanned by the complementary axes. Indexed from the dual vertex
`p' = p − 1_{S^c}`, it is the cell `(p', S^c)`. The star is then, with `ε(S)` the sign of the
shuffle that puts `S` before `S^c`,

  `(⋆ ω)(p', T) = ε(T^c) · ω(p' + 1_T, T^c)`  (primal to dual),
  `(⋆' η)(p, S) = ε(S^c) · η(p − 1_{S^c}, S^c)`  (dual to primal).

Only the combinatorics is formalised here: the shifts cancel and `⋆' ⋆ = (−1)^{k(n−k)}`.

## Main results

- `HodgeCube.eps_mul_compl` : `ε(S) · ε(S^c) = (−1)^{|S| (n − |S|)}`.
- `HodgeCube.star_star` : `⋆' (⋆ ω) = (−1)^{k(n−k)} ω` on the cells with `k` axes.

Not formalised yet: the coboundary `d`, the codifferential as the adjoint of `d`, and the
relation `δ = ± ⋆ d ⋆`. Nothing is said about a limit in the size of the fiber.
-/

@[expose] public noncomputable section

namespace HodgeCube

variable {n : ℕ} {Z : Fin n → Type*} [∀ i, AddCommGroup (Z i)] [∀ i, One (Z i)]

/-- The sites of the box: one position on each axis. -/
abbrev Site {n : ℕ} (Z : Fin n → Type*) := (i : Fin n) → Z i

/-- The cochains: a real number on every cell `(p, S)`. -/
abbrev Cochain {n : ℕ} (Z : Fin n → Type*) := Site Z × Finset (Fin n) → ℝ

open scoped Classical in
/-- The step of one unit on every axis of `T`. -/
def unit (T : Finset (Fin n)) : Site Z := fun i => if i ∈ T then 1 else 0

open scoped Classical in
/-- The sign of the shuffle that puts `S` before its complement:
`(−1)` to the number of pairs `j ∉ S`, `i ∈ S` with `j < i`. -/
def eps (S : Finset (Fin n)) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ∈ S ∧ ij.2 ∉ S ∧ ij.2 < ij.1)).card

open scoped Classical in
/-- The sign `σ(i, T) = (−1)^{#{j ∈ T : j < i}}`. -/
def sigma (i : Fin n) (T : Finset (Fin n)) : ℤ := (-1) ^ (T.filter (· < i)).card

/-- **The three sign identities of the star on `n` axes.** They are finite statements about the
subsets of `Fin n`, proved by `decide` for the dimensions used. Note the factor `(−1)^{n |S|}`:
it is `1` for every degree when `n` is even, and alternates with the degree when `n` is odd. -/
class HodgeSigns (n : ℕ) : Prop where
  eps_mul_compl : ∀ S : Finset (Fin n), eps S * eps Sᶜ = (-1) ^ (S.card * (n - S.card))
  sigma_antisymm : ∀ (i j : Fin n) (T : Finset (Fin n)), i ≠ j → i ∈ T → j ∈ T →
    sigma i T * sigma j (T.erase i) = -(sigma j T * sigma i (T.erase j))
  sign_star_d : ∀ (S : Finset (Fin n)) (i : Fin n), i ∉ S →
    eps Sᶜ * sigma i Sᶜ * eps (insert i S) = (-1) ^ (n * S.card) * sigma i (insert i S)

instance : HodgeSigns 3 := ⟨by decide, by decide, by decide⟩

instance : HodgeSigns 4 := ⟨by decide, by decide, by decide⟩

/-- **The two shuffle signs multiply to `(−1)^{|S| (n − |S|)}`.** -/
theorem eps_mul_compl [HodgeSigns n] (S : Finset (Fin n)) :
    eps S * eps Sᶜ = (-1) ^ (S.card * (n - S.card)) := HodgeSigns.eps_mul_compl S

/-- The star from the primal cochains to the dual ones. -/
def star (ω : Cochain Z) : Cochain Z := fun c =>
  (eps c.2ᶜ : ℝ) * ω (c.1 + unit c.2, c.2ᶜ)

/-- The star from the dual cochains back to the primal ones. -/
def starInv (η : Cochain Z) : Cochain Z := fun c =>
  (eps c.2ᶜ : ℝ) * η (c.1 - unit c.2ᶜ, c.2ᶜ)

/-- **`⋆' ⋆ = (−1)^{k(n−k)}`**: the shifts cancel and the signs multiply. -/
theorem star_star [HodgeSigns n] (ω : Cochain Z) (p : Site Z) (S : Finset (Fin n)) :
    starInv (star ω) (p, S) = (-1) ^ (S.card * (n - S.card)) * ω (p, S) := by
  have hcc : Sᶜᶜ = S := compl_compl S
  have h := eps_mul_compl S
  simp only [starInv, star, hcc]
  have hp : p - unit Sᶜ + unit Sᶜ = p := sub_add_cancel _ _
  rw [hp, ← mul_assoc]
  have h' : ((eps Sᶜ * eps S : ℤ) : ℝ) = (((-1) ^ (S.card * (n - S.card)) : ℤ) : ℝ) := by
    rw [mul_comm]; exact_mod_cast h
  push_cast at h'
  rw [h']

end HodgeCube
