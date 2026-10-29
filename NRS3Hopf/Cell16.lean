/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Action.Defs

/-!
# The closed fibered space is a triangulated three-sphere

Take the ends `±x, ±y, ±z` of the three open axes, and on the closed axis `w` the origin as
`+w` and the point at infinity as `−w`. Join every one of these eight points to every other
except its opposite. This is the boundary of the four-dimensional cross-polytope, the 16-cell.

* It has `8` vertices, `24` edges, `32` triangles and `16` tetrahedra, and Euler characteristic
  `8 − 24 + 32 − 16 = 0`, that of the three-sphere.
* Around every point, the origin and infinity included, the neighbours form an octahedron:
  `6` vertices, `12` edges, `8` triangles, Euler characteristic `2`, a two-sphere. Every point
  has a small sphere around it, as in a closed three-manifold.
* Each axis closes through the origin and infinity into a ring of four: `−a → 0 → +a → ∞ → −a`,
  with its two diagonals missing.
* **Faces are words of axis steps.** A face of `k` points is `k` different axes, each with a
  sign, so there are `C(4,k) · 2^k` of them. Written as an ordered word of `k` steps the same
  face has `k!` spellings: the order does not change where the steps arrive. One face is one
  statement; its `k!` words are the ways of saying it.

## Main results

- `Cell16.card_edges`, `Cell16.card_triangles`, `Cell16.card_tetrahedra`, `Cell16.euler` : the
  counts and `χ = 0`.
- `Cell16.link_counts` : the neighbours of the origin form an octahedron, `χ = 2`.
- `Cell16.axis_ring` : each axis is a ring of four through the origin and infinity.
- `Cell16.mem_faces_iff` : a set of points is a face iff its points lie on different axes.
- `Cell16.facesEquiv` : the faces of `k` points are the choices of `k` axes with a sign on each.
- `Cell16.card_faces` : there are `C(4,k) · 2^k` faces of `k` points.
- `Cell16.Word`, `Cell16.Word.toFace` : words of `k` axis steps and the face they reach; the
  map is onto and invariant under reordering (`toFinset_perm`).
- `Cell16.card_word` : there are `k! · C(4,k) · 2^k` words, `k!` for each face.
-/

@[expose] public section

namespace Cell16

/-- The eight points: an axis (`0, 1, 2` for `x, y, z`, `3` for `w`) and a sign. -/
abbrev Pt := Fin 4 × Bool

/-- Two points are joined unless they are opposite ends of the same axis. -/
def Adj (u v : Pt) : Prop := u.1 ≠ v.1

instance : DecidableRel Adj := fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))

/-- The origin `+w` and infinity `−w`. -/
def origin : Pt := (3, true)
def infinity : Pt := (3, false)

/-- The cliques of size `k`: the faces of dimension `k − 1`. -/
def faces (k : ℕ) : Finset (Finset Pt) :=
  (Finset.powersetCard k Finset.univ).filter fun s => ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Adj u v

theorem card_edges : (faces 2).card = 24 := by decide
theorem card_triangles : (faces 3).card = 32 := by decide
theorem card_tetrahedra : (faces 4).card = 16 := by decide

/-- **The Euler characteristic of the three-sphere**: `8 − 24 + 32 − 16 = 0`. -/
theorem euler : (Fintype.card Pt : ℤ) - (faces 2).card + (faces 3).card - (faces 4).card = 0 := by
  rw [card_edges, card_triangles, card_tetrahedra]; decide

/-- The neighbours of a point. -/
def link (p : Pt) : Finset Pt := Finset.univ.filter (Adj p)

/-- The faces of the link of a point. -/
def linkFaces (p : Pt) (k : ℕ) : Finset (Finset Pt) :=
  (Finset.powersetCard k (link p)).filter fun s => ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Adj u v

/-- **Around the origin there is an octahedron**: `6` vertices, `12` edges, `8` triangles,
Euler characteristic `2`. -/
theorem link_counts : (link origin).card = 6 ∧ (linkFaces origin 2).card = 12 ∧
    (linkFaces origin 3).card = 8 ∧
    ((link origin).card : ℤ) - (linkFaces origin 2).card + (linkFaces origin 3).card = 2 := by
  decide

/-- **Each axis closes through the origin and infinity into a ring of four**:
`−a → 0 → +a → ∞ → −a`, without the diagonals. -/
theorem axis_ring (a : Fin 4) (ha : a ≠ 3) :
    Adj (a, false) origin ∧ Adj origin (a, true) ∧ Adj (a, true) infinity ∧
      Adj infinity (a, false) ∧ ¬ Adj (a, false) (a, true) ∧ ¬ Adj origin infinity := by
  simp only [Adj, origin, infinity, ne_eq, not_not, and_true]
  exact ⟨ha, Ne.symm ha, ha, Ne.symm ha⟩

/-! ## Faces are words of axis steps -/

/-- **A face is a set of points on different axes.** -/
theorem mem_faces_iff {k : ℕ} {s : Finset Pt} :
    s ∈ faces k ↔ s.card = k ∧ Set.InjOn Prod.fst (s : Set Pt) := by
  unfold faces
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨-, hc⟩, h⟩
    refine ⟨hc, fun u hu v hv huv => ?_⟩
    by_contra hne
    exact h u hu v hv hne huv
  · rintro ⟨hc, h⟩
    exact ⟨⟨Finset.subset_univ _, hc⟩, fun u hu v hv hne huv => hne (h hu hv huv)⟩

/-- The face with axes `S` and a sign on each: the step `±a` for every axis `a ∈ S`. -/
def ofSigns {k : ℕ} (x : Σ S : {S : Finset (Fin 4) // S.card = k}, (S.1 → Bool)) : Finset Pt :=
  x.1.1.attach.image fun a => (a.1, x.2 a)

lemma mem_ofSigns {k : ℕ} (x : Σ S : {S : Finset (Fin 4) // S.card = k}, (S.1 → Bool))
    (p : Pt) : p ∈ ofSigns x ↔ ∃ h : p.1 ∈ x.1.1, x.2 ⟨p.1, h⟩ = p.2 := by
  obtain ⟨b, c⟩ := p
  simp only [ofSigns, Finset.mem_image, Finset.mem_attach, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a.2, rfl⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨b, h⟩, rfl, hc⟩

lemma ofSigns_mem_faces {k : ℕ} (x : Σ S : {S : Finset (Fin 4) // S.card = k}, (S.1 → Bool)) :
    ofSigns x ∈ faces k := by
  rw [mem_faces_iff]
  have hinj : Function.Injective fun a : {a // a ∈ x.1.1} => ((a.1, x.2 a) : Pt) := by
    intro a b h
    exact Subtype.ext (congrArg Prod.fst h)
  refine ⟨?_, ?_⟩
  · rw [ofSigns, Finset.card_image_of_injective _ hinj, Finset.card_attach]
    exact x.1.2
  · intro u hu v hv huv
    obtain ⟨hu1, hu2⟩ := (mem_ofSigns x u).1 hu
    obtain ⟨hv1, hv2⟩ := (mem_ofSigns x v).1 hv
    have : (⟨u.1, hu1⟩ : {a // a ∈ x.1.1}) = ⟨v.1, hv1⟩ := Subtype.ext huv
    exact Prod.ext huv (by rw [← hu2, ← hv2, this])

/-- The faces of `k` points reached by `ofSigns` are all of them, each once. -/
theorem ofSigns_bijective (k : ℕ) :
    Function.Bijective fun x : (Σ S : {S : Finset (Fin 4) // S.card = k}, (S.1 → Bool)) =>
      (⟨ofSigns x, ofSigns_mem_faces x⟩ : faces k) := by
  constructor
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨T, hT⟩, τ⟩ h
    have h' : ofSigns ⟨⟨S, hS⟩, σ⟩ = ofSigns ⟨⟨T, hT⟩, τ⟩ := congrArg Subtype.val h
    have hST : S = T := by
      ext a
      constructor
      · intro ha
        have : (a, σ ⟨a, ha⟩) ∈ ofSigns ⟨⟨T, hT⟩, τ⟩ := h' ▸ (mem_ofSigns _ _).2 ⟨ha, rfl⟩
        exact ((mem_ofSigns _ _).1 this).1
      · intro ha
        have : (a, τ ⟨a, ha⟩) ∈ ofSigns ⟨⟨S, hS⟩, σ⟩ := h'.symm ▸ (mem_ofSigns _ _).2 ⟨ha, rfl⟩
        exact ((mem_ofSigns _ _).1 this).1
    subst hST
    have : σ = τ := by
      funext a
      have : (a.1, σ a) ∈ ofSigns ⟨⟨S, hS⟩, τ⟩ := h' ▸ (mem_ofSigns _ _).2 ⟨a.2, rfl⟩
      obtain ⟨h1, h2⟩ := (mem_ofSigns _ _).1 this
      exact h2.symm
    subst this
    rfl
  · rintro ⟨s, hs⟩
    obtain ⟨hcard, hinj⟩ := mem_faces_iff.1 hs
    have hS : (s.image Prod.fst).card = k := by
      rw [Finset.card_image_of_injOn hinj, hcard]
    refine ⟨⟨⟨s.image Prod.fst, hS⟩, fun a => decide ((a.1, true) ∈ s)⟩, ?_⟩
    apply Subtype.ext
    ext ⟨b, c⟩
    rw [mem_ofSigns]
    constructor
    · rintro ⟨h, hc⟩
      obtain ⟨⟨b', c'⟩, hp, rfl⟩ := Finset.mem_image.1 h
      cases c' <;> cases c <;> simp_all
    · intro hp
      refine ⟨Finset.mem_image.2 ⟨_, hp, rfl⟩, ?_⟩
      cases c
      · simp only [decide_eq_false_iff_not]
        intro hT
        have := hinj hT hp rfl
        simp at this
      · simpa using hp

/-- **The faces of `k` points are the choices of `k` axes with a sign on each.** -/
noncomputable def facesEquiv (k : ℕ) :
    (Σ S : {S : Finset (Fin 4) // S.card = k}, (S.1 → Bool)) ≃ faces k :=
  Equiv.ofBijective _ (ofSigns_bijective k)

/-- **There are `C(4,k) · 2^k` faces of `k` points**: choose the axes, then a sign on each. -/
theorem card_faces (k : ℕ) : (faces k).card = Nat.choose 4 k * 2 ^ k := by
  have h := Fintype.card_congr (facesEquiv k)
  rw [Fintype.card_coe] at h
  rw [← h, Fintype.card_sigma]
  have hS : ∀ S : {S : Finset (Fin 4) // S.card = k}, Fintype.card (S.1 → Bool) = 2 ^ k := by
    intro S
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, S.2]
  simp only [hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_finset_len, Fintype.card_fin]

/-- A **word** of `k` axis steps: `k` points, any two on different axes, in order. -/
def Word (k : ℕ) : Type := {w : Fin k → Pt // ∀ i j, i ≠ j → Adj (w i) (w j)}

instance (k : ℕ) : Fintype (Word k) :=
  inferInstanceAs (Fintype {w : Fin k → Pt // ∀ i j, i ≠ j → Adj (w i) (w j)})

namespace Word

variable {k : ℕ}

/-- A word is `k` different axes in order, and a sign for each step. -/
def equivEmbSigns (k : ℕ) : Word k ≃ (Fin k ↪ Fin 4) × (Fin k → Bool) where
  toFun w := (⟨fun i => (w.1 i).1, fun i j h => by
      by_contra hne
      exact w.2 i j hne h⟩, fun i => (w.1 i).2)
  invFun e := ⟨fun i => (e.1 i, e.2 i), fun i j hne h => hne (e.1.injective h)⟩
  left_inv w := Subtype.ext rfl
  right_inv e := by ext <;> rfl

/-- The face a word reaches: its points, with the order forgotten. -/
def toFinset (w : Word k) : Finset Pt := Finset.univ.image w.1

lemma toFinset_mem_faces (w : Word k) : w.toFinset ∈ faces k := by
  have hinj : Function.Injective w.1 := fun i j h => by
    by_contra hne
    exact w.2 i j hne (congrArg Prod.fst h)
  rw [mem_faces_iff, toFinset, Finset.card_image_of_injective _ hinj]
  refine ⟨by simp, ?_⟩
  intro u hu v hv huv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hu)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
  by_contra hne
  exact w.2 i j (fun h => hne (h ▸ rfl)) huv

/-- The face a word reaches. -/
def toFace (w : Word k) : faces k := ⟨w.toFinset, w.toFinset_mem_faces⟩

/-- The same word with its steps taken in another order. -/
def perm (w : Word k) (σ : Equiv.Perm (Fin k)) : Word k :=
  ⟨w.1 ∘ σ, fun i j hne => w.2 (σ i) (σ j) (σ.injective.ne hne)⟩

/-- **The order of the steps does not change the face**: both orders arrive at the same place. -/
theorem toFinset_perm (w : Word k) (σ : Equiv.Perm (Fin k)) :
    (w.perm σ).toFinset = w.toFinset := by
  ext p
  simp only [toFinset, perm, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨j, hj⟩ => ⟨σ.symm j, by simpa using hj⟩⟩

/-- **Every face is reached by some word.** -/
theorem toFace_surjective : Function.Surjective (toFace : Word k → faces k) := by
  rintro ⟨s, hs⟩
  obtain ⟨hcard, hinj⟩ := mem_faces_iff.1 hs
  let e : s ≃ Fin k := s.equivFinOfCardEq hcard
  refine ⟨⟨fun i => (e.symm i).1, fun i j hne h => hne ?_⟩, ?_⟩
  · have : (e.symm i).1 = (e.symm j).1 := hinj (e.symm i).2 (e.symm j).2 h
    exact e.symm.injective (Subtype.ext this)
  · apply Subtype.ext
    ext p
    simp only [toFace, toFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hp
      exact ⟨e ⟨p, hp⟩, by simp⟩

end Word

/-- **There are `k! · C(4,k) · 2^k` words of `k` axis steps**: `k!` spellings of each face. -/
theorem card_word (k : ℕ) : Fintype.card (Word k) = k.factorial * (faces k).card := by
  rw [Fintype.card_congr (Word.equivEmbSigns k), Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_bool,
    Nat.descFactorial_eq_factorial_mul_choose, card_faces, mul_assoc]

/-- Edges: `24` faces, `48` words of two steps. -/
theorem card_word_two : Fintype.card (Word 2) = 48 := by
  rw [card_word, card_edges]; rfl

/-- Triangles: `32` faces, `192` words of three steps. -/
theorem card_word_three : Fintype.card (Word 3) = 192 := by
  rw [card_word, card_triangles]; rfl

/-- Tetrahedra: `16` faces, `384` words of four steps, as many as the symmetries of the 16-cell
(`Cell16.card_aut`). -/
theorem card_word_four : Fintype.card (Word 4) = 384 := by
  rw [card_word, card_tetrahedra]; rfl

end Cell16
