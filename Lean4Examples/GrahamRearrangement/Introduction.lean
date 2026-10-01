import Mathlib

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Introduction and ordering definitions

Paper: Pham--Sauermann, *On Graham's rearrangement conjecture*.
This module contains the introduction-level definitions used throughout the formalization.
-/

section Orderings

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- The nonempty partial sums of a list:
`[x₁, x₁+x₂, ..., x₁+...+xₙ]`. -/
def partialSums : List G → List G
  | [] => []
  | x :: xs => x :: (partialSums xs).map (x + ·)

@[simp] theorem partialSums_nil : partialSums ([] : List G) = [] := rfl

@[simp] theorem partialSums_cons (x : G) (xs : List G) :
    partialSums (x :: xs) = x :: (partialSums xs).map (x + ·) := rfl

@[simp] theorem length_partialSums (xs : List G) :
    (partialSums xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [partialSums, ih]

/-- A list is an ordering of a finite set when it has no duplicates and contains
exactly that set. -/
def IsOrdering (S : Finset G) (xs : List G) : Prop :=
  xs.Nodup ∧ xs.toFinset = S

/-- Definition of a valid ordering from the introduction. -/
def IsValidOrdering (S : Finset G) (xs : List G) : Prop :=
  IsOrdering S xs ∧ (partialSums xs).Nodup

theorem IsOrdering.length_eq_card {S : Finset G} {xs : List G}
    (h : IsOrdering S xs) : xs.length = S.card := by
  calc
    xs.length = xs.toFinset.card := (List.toFinset_card_of_nodup h.1).symm
    _ = S.card := congrArg Finset.card h.2

theorem IsValidOrdering.length_eq_card {S : Finset G} {xs : List G}
    (h : IsValidOrdering S xs) : xs.length = S.card :=
  h.1.length_eq_card

/-- Graham's rearrangement property for one finite subset. -/
def HasValidOrdering (S : Finset G) : Prop :=
  ∃ xs : List G, IsValidOrdering S xs

end Orderings

/-- The finite-subset sum notation Σ(S) used throughout the paper. -/
def subsetSum {G : Type*} [AddCommMonoid G] (S : Finset G) : G :=
  ∑ x ∈ S, x

theorem subsetSum_insert {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (S : Finset G) (x : G) (hx : x ∉ S) :
    subsetSum (insert x S) = x + subsetSum S := by
  simp [subsetSum, hx, add_comm]

theorem subsetSum_union_disjoint {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A B : Finset G} (h : Disjoint A B) :
    subsetSum (A ∪ B) = subsetSum A + subsetSum B := by
  simp [subsetSum, Finset.sum_union h]

/-- Conjecture 1.1. -/
def Conjecture11Statement : Prop :=
  ∀ (p : ℕ), p.Prime →
    ∀ S : Finset (ZMod p), 0 ∉ S → HasValidOrdering S

/-- The theorem-range predicate used in Theorem 1.2. -/
def InGrahamRange (α C : ℝ) (p : ℕ) (S : Finset (ZMod p)) : Prop :=
  0 ∉ S ∧ C ≤ (S.card : ℝ) ∧
    (S.card : ℝ) ≤ (p : ℝ) ^ (1 - α)

/-!
All occurrences of `Real.log` below therefore match the paper's convention that
unqualified logarithms are natural logarithms.
-/

end GrahamRearrangement
