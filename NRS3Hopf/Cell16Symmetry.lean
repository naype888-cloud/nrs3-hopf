/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.Cell16
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# The symmetry group of the closed fibered space

The symmetries of the 16-cell (`Cell16`) are the permutations of its eight points that keep the
joins. They are exactly the **signed permutations of the four axes**: permute the axes
`x, y, z, w` by `π` and reverse the sign of some of them. This is the hyperoctahedral group
`B₄`, with `4! · 2⁴ = 384` elements.

* A symmetry keeps the pairs of opposite points, the only pairs that are not joined, so it moves
  whole axes: it induces a permutation `π` of the axes and, on each axis, keeps or reverses the
  sign.
* The group acts transitively on the points: the origin `+w`, infinity `−w` and the ends of the
  open axes are all alike. Any statement proved at one point and invariant under the symmetries
  holds at every point.

## Main results

- `Cell16.signedPerm` : the signed permutation `(a, b) ↦ (π a, s a xor b)`.
- `Cell16.adj_signedPerm` : signed permutations keep the joins.
- `Cell16.isAut_iff` : a permutation of the points keeps the joins iff it is a signed
  permutation.
- `Cell16.card_aut` : the symmetry group has `384` elements.
- `Cell16.signedPerm_transitive` : every point is the image of `(x, +)`.
-/

@[expose] public section

namespace Cell16

/-- The signed permutation `(a, b) ↦ (π a, s a xor b)` of the points: `π` permutes the axes and
`s a = true` reverses the sign of axis `a`. -/
def signedPerm (π : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool) : Equiv.Perm Pt where
  toFun p := (π p.1, xor (s p.1) p.2)
  invFun p := (π.symm p.1, xor (s (π.symm p.1)) p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp] lemma signedPerm_apply (π : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool) (p : Pt) :
    signedPerm π s p = (π p.1, xor (s p.1) p.2) := rfl

/-- **Signed permutations keep the joins.** -/
lemma adj_signedPerm (π : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool) (u v : Pt) :
    Adj (signedPerm π s u) (signedPerm π s v) ↔ Adj u v := by
  simp [Adj, π.injective.eq_iff]

/-- A permutation of the points that keeps the joins. -/
def IsAut (g : Equiv.Perm Pt) : Prop := ∀ u v, Adj (g u) (g v) ↔ Adj u v

private lemma fst_eq_of_isAut {g : Equiv.Perm Pt} (hg : IsAut g) {u v : Pt} (h : u.1 = v.1) :
    (g u).1 = (g v).1 := by
  by_contra h'
  exact ((hg u v).mp h') h

/-- **The symmetries are the signed permutations.** A permutation of the eight points keeps the
joins exactly when it permutes the axes and reverses the sign of some of them. -/
theorem isAut_iff (g : Equiv.Perm Pt) : IsAut g ↔ ∃ π s, g = signedPerm π s := by
  refine ⟨fun hg => ?_, ?_⟩
  · have hinj : Function.Injective fun a : Fin 4 => (g (a, false)).1 := by
      intro a c h
      by_contra hac
      exact ((hg (a, false) (c, false)).mpr hac) h
    let π := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
    refine ⟨π, fun a => (g (a, false)).2, ?_⟩
    ext ⟨a, b⟩ : 1
    have h1 : (g (a, b)).1 = (g (a, false)).1 := fst_eq_of_isAut hg rfl
    refine Prod.ext h1 ?_
    cases b
    · simp
    · have hne : g (a, true) ≠ g (a, false) := fun h => by simpa using g.injective h
      have h2 : (g (a, true)).2 ≠ (g (a, false)).2 := fun h => hne (Prod.ext h1 h)
      simp only [signedPerm_apply, Bool.xor_true]
      revert h2
      cases (g (a, true)).2 <;> cases (g (a, false)).2 <;> simp
  · rintro ⟨π, s, rfl⟩
    exact adj_signedPerm π s

/-- The signed permutations are determined by `π` and `s`. -/
lemma signedPerm_injective :
    Function.Injective fun q : Equiv.Perm (Fin 4) × (Fin 4 → Bool) => signedPerm q.1 q.2 := by
  rintro ⟨π, s⟩ ⟨π', s'⟩ h
  have h' := fun a => congrArg (fun g : Equiv.Perm Pt => g (a, false)) h
  simp only [signedPerm_apply, Bool.xor_false, Prod.mk.injEq] at h'
  exact Prod.ext (Equiv.ext fun a => (h' a).1) (funext fun a => (h' a).2)

/-- The symmetries as signed permutations. -/
noncomputable def autEquiv : Equiv.Perm (Fin 4) × (Fin 4 → Bool) ≃ {g : Equiv.Perm Pt // IsAut g} :=
  Equiv.ofBijective (fun q => ⟨signedPerm q.1 q.2, adj_signedPerm q.1 q.2⟩)
    ⟨fun q q' h => signedPerm_injective (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨π, s, rfl⟩ := (isAut_iff g).mp hg
      exact ⟨(π, s), rfl⟩⟩

/-- **The symmetry group of the closed fibered space has `384 = 4! · 2⁴` elements**: it is the
hyperoctahedral group `B₄`. -/
theorem card_aut [Fintype {g : Equiv.Perm Pt // IsAut g}] :
    Fintype.card {g : Equiv.Perm Pt // IsAut g} = 384 := by
  rw [← Fintype.card_congr autEquiv, Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rfl

/-- **The symmetries act transitively on the points**: `(a, b)` is the image of `(x, +)` by
the signed permutation that swaps the axes `x` and `a` and gives every axis the sign `!b`. -/
lemma signedPerm_transitive (p : Pt) :
    signedPerm (Equiv.swap 0 p.1) (fun _ => !p.2) (0, true) = p := by
  obtain ⟨a, b⟩ := p
  cases b <;> simp

end Cell16
