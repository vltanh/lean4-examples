import Mathlib

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Pham--Sauermann: Graham's rearrangement conjecture

A Lean 4 formalization scaffold for Huy Tuan Pham and Lisa Sauermann,
"On Graham's rearrangement conjecture", arXiv:2602.15797.

The paper's genuinely deep probabilistic/Fourier-analytic statements are represented below
as propositions first. Elementary infrastructure is proved directly and later commits can
replace the remaining proposition-level interfaces by proofs.
-/

section Orderings

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- The nonempty partial sums of a list: [x₁, x₁+x₂, ..., x₁+...+xₙ]. -/
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

/-- A list is an ordering of a finite set when it has no duplicates and contains exactly that set. -/
def IsOrdering (S : Finset G) (xs : List G) : Prop :=
  xs.Nodup ∧ xs.toFinset = S

/-- Definition of a valid ordering from the introduction of the paper. -/
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

/-- Graham's rearrangement conjecture for a particular finite subset of an additive monoid. -/
def HasValidOrdering (S : Finset G) : Prop :=
  ∃ xs : List G, IsValidOrdering S xs

end Orderings

section Segments

variable {G : Type*} [AddCommMonoid G]

/-- Inclusive segment sum, using zero-based list positions.

For a well-formed interval `a ≤ b < xs.length`, this is
`xs[a] + xs[a+1] + ... + xs[b]`.
-/
def intervalSum (xs : List G) (a b : ℕ) : G :=
  ((xs.drop a).take (b + 1 - a)).sum

/-- The Section 5 target condition in zero-based indexing: every segment whose
left endpoint is after the first element has nonzero sum. -/
def HasNoZeroTailSegments (xs : List G) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ≤ b → b < xs.length → intervalSum xs a b ≠ 0

/-- Right endpoints of the zero-sum segments that obstruct a valid ordering.
This is the list analogue of `B(σ)` from Section 5. -/
noncomputable def badRightEndpoints (xs : List G) : Finset ℕ := by
  classical
  exact (Finset.range xs.length).filter fun b =>
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ b ∧ intervalSum xs a b = 0

@[simp] theorem mem_badRightEndpoints_iff (xs : List G) (b : ℕ) :
    b ∈ badRightEndpoints xs ↔
      b < xs.length ∧ ∃ a : ℕ, 1 ≤ a ∧ a ≤ b ∧ intervalSum xs a b = 0 := by
  classical
  simp [badRightEndpoints]

end Segments

section BooleanSlice

/-- The sum of a finite subset. -/
def subsetSum {p : ℕ} (R : Finset (ZMod p)) : ZMod p :=
  ∑ x ∈ R, x

/-- Uniform probability mass that a size-`m` subset of `S` has sum `z`.

This is written as a finite ratio rather than introducing a measure space; it is exactly
the probability appearing in Theorem 1.3 and Corollary 1.4.
-/
noncomputable def sliceMass {p : ℕ} (S : Finset (ZMod p)) (m : ℕ) (z : ZMod p) : ℝ :=
  ((S.powersetCard m).filter (fun R => subsetSum R = z)).card /
    (S.powersetCard m).card

theorem sliceMass_nonneg {p : ℕ} (S : Finset (ZMod p)) (m : ℕ) (z : ZMod p) :
    0 ≤ sliceMass S m z := by
  positivity

theorem sliceMass_le_one {p : ℕ} (S : Finset (ZMod p)) (m : ℕ) (z : ZMod p) :
    sliceMass S m z ≤ 1 := by
  unfold sliceMass
  by_cases hzero : (S.powersetCard m).card = 0
  · simp [hzero]
  · apply (div_le_one ?_).2
    · exact_mod_cast Nat.pos_of_ne_zero hzero
    · exact_mod_cast
        (Finset.card_filter_le (S.powersetCard m) (fun R => subsetSum R = z))

end BooleanSlice

/-- Lean transcription of Theorem 1.3 (Boolean-slice anticoncentration). -/
def Theorem13Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ), p.Prime →
    ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
    ∀ (m : ℕ),
      C * Real.log (S.card : ℝ) ≤ (m : ℝ) →
      (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ) →
      ∀ z : ZMod p,
        sliceMass S m z ≤
          1 / (p : ℝ) + C / ((S.card : ℝ) * Real.sqrt (m : ℝ))

/-- Lean transcription of Corollary 1.4. -/
def Corollary14Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), p.Prime →
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : ℕ), 0 < m →
        (m : ℝ) ≤ (1 - ε) * S.card →
        ∀ z : ZMod p,
          sliceMass S m z ≤
            1 / (p : ℝ) +
              C * Real.sqrt (Real.log (S.card : ℝ)) /
                ((S.card : ℝ) * Real.sqrt (m : ℝ))

/-- Lean transcription of Theorem 1.2, the main result of the paper. -/
def Theorem12Statement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ (p : ℕ), p.Prime →
      ∀ (S : Finset (ZMod p)),
        0 ∉ S →
        Cα ≤ (S.card : ℝ) →
        (S.card : ℝ) ≤ (p : ℝ) ^ (1 - α) →
        HasValidOrdering S

end GrahamRearrangement
