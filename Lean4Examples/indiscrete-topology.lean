import Mathlib

open Set Filter Topology

def IndiscreteTopology {X : Type*} : TopologicalSpace X where
  IsOpen U := U = ∅ ∨ U = univ
  isOpen_univ := Or.inr rfl
  isOpen_inter U V := by
    rintro (rfl | rfl) (rfl | rfl)
    constructor
    · exact empty_inter ∅
    · exact Or.inl (empty_inter univ)
    constructor
    · exact inter_empty univ
    · exact Or.inr (univ_inter univ)
  isOpen_sUnion S := fun h => sUnion_mem_empty_univ h

-- The indiscrete topology on a space with at least two points is not Hausdorff.
example {X : Type*} (h' : ∃ x y : X, x ≠ y) :
    ¬ @T2Space X IndiscreteTopology := by
  -- Let T be the indiscrete topology on X.
  -- Suppose T is Hausdorff.
  intro hT2
  -- Let x, y ∈ X be distinct points.
  rcases h' with ⟨x, y, hxy⟩
  -- Since T is Hausdorff, there exist disjoint open sets U, V ∈ X
  -- such that x ∈ U and y ∈ V.
  rcases hT2.t2 hxy with ⟨U, V, hU, hV, hxU, hyV, hUV⟩
  -- Since T is the indiscrete topology, U = ∅ or U = univ
  -- and V = ∅ or V = univ.
  -- If U = ∅, then x ∈ U is contradictory.
  -- If U = univ,
  --   if V = ∅, then y ∈ V is contradictory.
  --   if V = univ, then U and V being disjoint is contradictory.
  rcases hU with (rfl | rfl)
  · exact hxU
  · rcases hV with (rfl | rfl)
    · exact hyV
    · rw [univ_disjoint] at hUV
      rw [hUV] at hxU
      exact hxU

-- In the topological space X with the indiscrete topology,
-- every sequence converges to every point.
-- (thus, the limit of a sequence is not unique)
example [T : TopologicalSpace X] {u : ℕ → X} {a : X} {h : T = IndiscreteTopology} :
  Tendsto u atTop (𝓝 a) := by
  rw [tendsto_nhds]
  intro S hS
  rw [h] at hS
  rcases hS with (rfl | rfl)
  · exact False.elim
  · exact fun _ => univ_mem
