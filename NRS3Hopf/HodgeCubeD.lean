/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.HodgeCube
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

/-!
# The coboundary of the box with the fiber and its adjoint

On the cells `(p, T)` of `HodgeCube`, the coboundary removes one axis `i` of `T` and takes the
difference between the two opposite faces, the one at `p + 1_i` and the one at `p`:

  `(d ω)(p, T) = Σ_{i ∈ T} σ(i, T) · (ω(p + 1_i, T∖i) − ω(p, T∖i))`,

with `σ(i, T) = (−1)^{#{j ∈ T : j < i}}`. The codifferential adds an axis `i ∉ S`:

  `(δ η)(p, S) = Σ_{i ∉ S} σ(i, S ∪ i) · (η(p − 1_i, S ∪ i) − η(p, S ∪ i))`.

`d ∘ d = 0` and `δ = − ⋆' d ⋆` hold for any groups on the axes. The adjointness uses finite sites
(a finite group on every axis, as `ZMod 3` on the fiber), so that the inner product is a finite
sum.

## Main results

- `HodgeCubeD.sum_cells_swap` : the sum over `(T, i ∈ T)` is the sum over `(S, i ∉ S)` with
  `T = S ∪ i`.
- `HodgeCubeD.d_adjoint` : `⟨d ω, η⟩ = ⟨ω, δ η⟩`.
- `HodgeCubeD.d_d` : `d ∘ d = 0`, for any groups on the axes (the open `ℤ` included).
- `HodgeCubeD.codiff_eq_neg_star_d_star` : `δ = −(−1)^{n k} ⋆' d ⋆` on the `k`-cells.

Not formalised: the adjointness on the open axes `ℤ` (the sums are then over finitely supported
cochains), and any statement about the size of the fiber going to infinity.
-/

@[expose] public noncomputable section

namespace HodgeCubeD

open HodgeCube

variable {n : ℕ} {Z : Fin n → Type*} [∀ i, AddCommGroup (Z i)] [∀ i, One (Z i)]

/-- The coboundary. -/
def d (ω : Cochain Z) : Cochain Z := fun c =>
  ∑ i ∈ c.2, (sigma i c.2 : ℝ) * (ω (c.1 + unit {i}, c.2.erase i) - ω (c.1, c.2.erase i))

/-- The codifferential. -/
def codiff (η : Cochain Z) : Cochain Z := fun c =>
  ∑ i ∈ c.2ᶜ, (sigma i (insert i c.2) : ℝ) *
    (η (c.1 - unit {i}, insert i c.2) - η (c.1, insert i c.2))

variable [∀ i, Fintype (Z i)]

/-- The inner product of two cochains. -/
def ipc (ω η : Cochain Z) : ℝ := ∑ c : Site Z × Finset (Fin n), ω c * η c

/-- **Cells with a removed axis**: the sum over `(T, i ∈ T)` is the sum over `(S, i ∉ S)` with
`T = S ∪ i`. -/
theorem sum_cells_swap (f : Finset (Fin n) → Fin n → ℝ) :
    ∑ T : Finset (Fin n), ∑ i ∈ T, f T i
      = ∑ S : Finset (Fin n), ∑ i ∈ Sᶜ, f (insert i S) i := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.1.erase x.2, x.2⟩) (fun y _ => ⟨insert y.2 y.1, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_compl] at hx ⊢
    exact Finset.notMem_erase _ _
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_compl] at hy ⊢
    exact Finset.mem_insert_self _ _
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    simp [Finset.insert_erase hx]
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_compl] at hy
    simp [Finset.erase_insert hy]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    simp [Finset.insert_erase hx]

/-- The sum over the sites for one added axis `i ∉ S`: the shift by `1_i` moves from `ω` to
`η`. -/
theorem key_shift (ω η : Cochain Z) (S : Finset (Fin n)) (i : Fin n) :
    ∑ p : Site Z, (sigma i (insert i S) : ℝ) * (ω (p + unit {i}, S) - ω (p, S))
        * η (p, insert i S)
      = ∑ p : Site Z, ω (p, S) * ((sigma i (insert i S) : ℝ) *
          (η (p - unit {i}, insert i S) - η (p, insert i S))) := by
  have hs : ∑ p : Site Z, ω (p + unit {i}, S) * η (p, insert i S)
      = ∑ p : Site Z, ω (p, S) * η (p - unit {i}, insert i S) :=
    Fintype.sum_equiv (Equiv.addRight (unit {i})) _ _ (fun p => by simp)
  have e1 : ∀ p : Site Z, (sigma i (insert i S) : ℝ) * (ω (p + unit {i}, S) - ω (p, S))
      * η (p, insert i S) = (sigma i (insert i S) : ℝ) * (ω (p + unit {i}, S) * η (p, insert i S))
        - (sigma i (insert i S) : ℝ) * (ω (p, S) * η (p, insert i S)) := fun p => by ring
  have e2 : ∀ p : Site Z, ω (p, S) * ((sigma i (insert i S) : ℝ) *
      (η (p - unit {i}, insert i S) - η (p, insert i S)))
      = (sigma i (insert i S) : ℝ) * (ω (p, S) * η (p - unit {i}, insert i S))
        - (sigma i (insert i S) : ℝ) * (ω (p, S) * η (p, insert i S)) := fun p => by ring
  simp only [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]

/-- **`d` and `δ` are adjoint**: `⟨d ω, η⟩ = ⟨ω, δ η⟩`. -/
theorem d_adjoint (ω η : Cochain Z) : ipc (d ω) η = ipc ω (codiff η) := by
  classical
  unfold ipc
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  have hL : ∀ T : Finset (Fin n), ∑ p : Site Z, d ω (p, T) * η (p, T)
      = ∑ i ∈ T, ∑ p : Site Z, (sigma i T : ℝ) *
          (ω (p + unit {i}, T.erase i) - ω (p, T.erase i)) * η (p, T) := by
    intro T
    simp only [d, Finset.sum_mul]
    exact Finset.sum_comm
  have hR : ∀ S : Finset (Fin n), ∑ p : Site Z, ω (p, S) * codiff η (p, S)
      = ∑ i ∈ Sᶜ, ∑ p : Site Z, ω (p, S) * ((sigma i (insert i S) : ℝ) *
          (η (p - unit {i}, insert i S) - η (p, insert i S))) := by
    intro S
    simp only [codiff, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [hL, hR]
  refine (sum_cells_swap _).trans ?_
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.erase_insert (Finset.mem_compl.mp hi)]
  exact key_shift ω η S i

/-- **The signs of two removed axes are antisymmetric**: removing `i` then `j` and removing `j`
then `i` give opposite signs. -/
theorem sigma_antisymm [HodgeSigns n] (i j : Fin n) (T : Finset (Fin n)) (hij : i ≠ j)
    (hi : i ∈ T) (hj : j ∈ T) :
    (sigma i T : ℝ) * sigma j (T.erase i) = -((sigma j T : ℝ) * sigma i (T.erase j)) := by
  exact_mod_cast HodgeSigns.sigma_antisymm i j T hij hi hj

/-- A sum over the ordered pairs `i ≠ j` of `T` of an antisymmetric function is zero. -/
theorem sum_pairs_antisymm (T : Finset (Fin n)) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → F j i = -F i j) :
    ∑ i ∈ T, ∑ j ∈ T.erase i, F i j = 0 := by
  have hswap : ∑ i ∈ T, ∑ j ∈ T.erase i, F i j = ∑ j ∈ T, ∑ i ∈ T.erase j, F i j := by
    refine Finset.sum_comm' fun i j => ?_
    simp only [Finset.mem_erase]
    tauto
  have hneg : ∑ j ∈ T, ∑ i ∈ T.erase j, F i j = -∑ i ∈ T, ∑ j ∈ T.erase i, F i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_erase.mp hi
    exact hF j hj i hi'.2 (Ne.symm hi'.1)
  linarith

omit [∀ i, Fintype (Z i)] in
/-- **`d ∘ d = 0`**, on any groups: no finiteness of the sites is used. -/
theorem d_d [HodgeSigns n] (ω : Cochain Z) : d (d ω) = 0 := by
  funext c
  obtain ⟨p, T⟩ := c
  let E : Fin n → Fin n → Finset (Fin n) := fun i j => (T.erase i).erase j
  let s : Fin n → Fin n → ℝ := fun i j => (sigma i T : ℝ) * sigma j (T.erase i)
  let Q : Fin n → Fin n → ℝ := fun i j =>
    (ω (p + unit {i} + unit {j}, E i j) - ω (p + unit {i}, E i j))
      - (ω (p + unit {j}, E i j) - ω (p, E i j))
  have hsum : d (d ω) (p, T) = ∑ i ∈ T, ∑ j ∈ T.erase i, s i j * Q i j := by
    simp only [d]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [s, Q, E]
    ring
  rw [hsum]
  refine sum_pairs_antisymm T (fun i j => s i j * Q i j) fun i hi j hj hij => ?_
  have hQ : Q j i = Q i j := by
    simp only [Q, E]
    rw [Finset.erase_right_comm, add_right_comm]
    ring
  have hs : s j i = -s i j := by
    have := sigma_antisymm i j T hij hi hj
    simp only [s]
    linarith
  show s j i * Q j i = -(s i j * Q i j)
  rw [hQ, hs]
  ring

omit [∀ i, Fintype (Z i)] in
/-- One step along `i` plus the steps along the rest of `T` is the steps along `T`. -/
theorem unit_add_erase {i : Fin n} {T : Finset (Fin n)} (hi : i ∈ T) :
    (unit {i} : Site Z) + unit (T.erase i) = unit T := by
  funext j
  simp only [unit, Pi.add_apply]
  by_cases hj : j = i
  · subst hj
    simp [hi]
  · by_cases hjT : j ∈ T <;> simp [hj, hjT]

omit [∀ i, Fintype (Z i)] in
/-- **`δ = −(−1)^{n k} ⋆' d ⋆`** on the `k`-cells: the codifferential is the star, the coboundary
and the star again. The sign is `−1` in every degree when `n` is even (the box with the fiber,
`n = 4`) and alternates with the degree when `n` is odd (the three-torus, `n = 3`). The shifts of
the dual cells cancel exactly. -/
theorem codiff_eq_neg_star_d_star [HodgeSigns n] (η : Cochain Z) (p : Site Z)
    (S : Finset (Fin n)) :
    codiff η (p, S) = -(((-1 : ℝ) ^ (n * S.card)) * starInv (d (star η)) (p, S)) := by
  simp only [codiff, HodgeCube.starInv, d, HodgeCube.star, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiS : i ∈ Sᶜ := hi
  have hcompl : (Sᶜ.erase i)ᶜ = insert i S := by
    rw [Finset.compl_erase, compl_compl]
  have hu := unit_add_erase (Z := Z) hiS
  have h1 : p - unit Sᶜ + unit {i} + unit (Sᶜ.erase i) = p := by
    rw [add_assoc, hu]; exact sub_add_cancel _ _
  have h2 : p - unit Sᶜ + unit (Sᶜ.erase i) = p - unit {i} := by
    rw [← hu]; abel
  have hs : (eps Sᶜ : ℝ) * sigma i Sᶜ * eps (insert i S)
      = (-1 : ℝ) ^ (n * S.card) * sigma i (insert i S) := by
    exact_mod_cast HodgeSigns.sign_star_d S i (Finset.mem_compl.mp hiS)
  have hτ : ((-1 : ℝ) ^ (n * S.card)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hcompl, h1, h2]
  linear_combination ((-1 : ℝ) ^ (n * S.card) * (η (p, insert i S) - η (p - unit {i}, insert i S)))
      * hs + (-(sigma i (insert i S) : ℝ) * (η (p - unit {i}, insert i S) - η (p, insert i S)))
      * hτ

end HodgeCubeD
