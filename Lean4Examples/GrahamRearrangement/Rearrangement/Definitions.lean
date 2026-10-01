import Lean4Examples.GrahamRearrangement.Combinatorial

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: Rearrangement definitions and deterministic repair setup

This module contains zero-sum interval definitions, indexed orderings, admissible
local swaps, blocked candidates, the three bad-event predicates, and the deterministic
repair interface.
-/

section Segments

variable {G : Type*} [AddCommMonoid G]

/-- Inclusive segment sum, using zero-based list positions.

For a well-formed interval `a ≤ b < xs.length`, this is
`xs[a] + xs[a+1] + ... + xs[b]`.
-/
def intervalSum (xs : List G) (a b : ℕ) : G :=
  ((xs.drop a).take (b + 1 - a)).sum

/-- Section 5 target condition in zero-based indexing:
every interval starting after the first entry has nonzero sum. -/
def HasNoZeroTailSegments (xs : List G) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ≤ b → b < xs.length → intervalSum xs a b ≠ 0

/-- Right endpoints of zero-sum intervals, the list analogue of `B(σ)`. -/
noncomputable def badRightEndpoints (xs : List G) : Finset ℕ := by
  classical
  exact (Finset.range xs.length).filter fun b =>
    ∃ a : ℕ, 1 ≤ a ∧ a < b ∧ intervalSum xs a b = 0

@[simp] theorem mem_badRightEndpoints_iff (xs : List G) (b : ℕ) :
    b ∈ badRightEndpoints xs ↔
      b < xs.length ∧ ∃ a : ℕ, 1 ≤ a ∧ a < b ∧ intervalSum xs a b = 0 := by
  classical
  simp [badRightEndpoints]

end Segments

section IndexedRepair

/-- An indexed ordering of `S`. The index set has exactly `|S|` points. -/
def IsIndexedOrdering {p : ℕ} (S : Finset (ZMod p))
    (σ : Fin S.card → ZMod p) : Prop :=
  Function.Injective σ ∧
    ∀ x : ZMod p, x ∈ S ↔ ∃ i, σ i = x

/-- Convert an indexed ordering into the corresponding list. -/
def indexedToList {n p : ℕ} (σ : Fin n → ZMod p) : List (ZMod p) :=
  List.ofFn σ

/-- Inclusive interval sum for an indexed ordering. -/
def indexedIntervalSum {n p : ℕ} (σ : Fin n → ZMod p)
    (a b : ℕ) : ZMod p :=
  ∑ i ∈ Finset.Icc a b, if hi : i < n then σ ⟨i, hi⟩ else 0

/-- Zero-sum right endpoints in zero-based indexing. -/
noncomputable def indexedBadRightEndpoints {n p : ℕ}
    (σ : Fin n → ZMod p) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun b =>
    ∃ a : ℕ, 1 ≤ a ∧ a < b ∧ indexedIntervalSum σ a b = 0

/-- Apply a permutation of positions to an indexed ordering. -/
def applyPositionPerm {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) : Fin n → ZMod p :=
  σ ∘ π

/-- Two swaps have disjoint supports. -/
def swapPairsDisjoint {n : ℕ} (q r : Fin n × Fin n) : Prop :=
  q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2

/-- A list of disjoint local swaps, each moving an endpoint by at most `5D`. -/
def IsAdmissibleSwapList {n : ℕ} (D : ℕ)
    (P : List (Fin n × Fin n)) : Prop :=
  P.Pairwise swapPairsDisjoint ∧
    ∀ q ∈ P, q.1.val < q.2.val ∧ q.2.val ≤ q.1.val + 5 * D

/-- Permutation obtained from a list of transpositions. -/
def swapsPerm {n : ℕ} : List (Fin n × Fin n) → Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | q :: qs => (Equiv.swap q.1 q.2).trans (swapsPerm qs)

/-- Admissible permutations from Section 5. -/
def IsAdmissiblePermutation {n : ℕ} (D : ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : List (Fin n × Fin n),
    IsAdmissibleSwapList D P ∧ swapsPerm P = π

/-- `π` fixes every position strictly before `b`. -/
def FixedBelow {n : ℕ} (b : Fin n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, i.val < b.val → π i = i

/-- A candidate `y` is blocked exactly when performing the local swap `(b,y)`
creates a zero-sum interval crossing exactly one endpoint of the swap.

This is the zero-based transcription of the definition preceding Lemma 5.3.
-/
def IsBlockedAt {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p)
    (b : Fin n) (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  b.val < y.val ∧ y.val ≤ b.val + 5 * D ∧
    ∃ s t : Fin n,
      1 ≤ s.val ∧ s.val < t.val ∧
      indexedIntervalSum
          (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
          s.val t.val = 0 ∧
      ((b.val < s.val ∧ s.val ≤ y.val) ∨
        (b.val ≤ t.val ∧ t.val < y.val))

/-- All blocked local choices for a fixed bad endpoint and current admissible permutation. -/
noncomputable def blockedCandidates {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun y => IsBlockedAt D σ b π y

/-- Bad event `𝓑₁` from Lemma 5.1. -/
def BadEvent1 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ indexedBadRightEndpoints σ, n ≤ b + 30 * D

/-- Bad event `𝓑₂` from Lemma 5.2. -/
def BadEvent2 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ z : Fin n,
    D < ((indexedBadRightEndpoints σ).filter
      (fun b => Nat.dist b z.val ≤ 10 * D)).card

/-- Bad event `𝓑₃` from Lemma 5.3. -/
def BadEvent3 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b : Fin n,
    b.val ∈ indexedBadRightEndpoints σ ∧
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      FixedBelow b π ∧
      2 * D ≤ (blockedCandidates D σ b π).card

/-- A starting ordering for which all three Section 5 bad events fail. -/
def Section5Good {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ¬ BadEvent1 D σ ∧ ¬ BadEvent2 D σ ∧ ¬ BadEvent3 D σ

/-- Indexed and list formulations of being an ordering agree. -/
theorem indexedToList_isOrdering {p : ℕ} {S : Finset (ZMod p)}
    {σ : Fin S.card → ZMod p} (hσ : IsIndexedOrdering S σ) :
    IsOrdering S (indexedToList σ) := by
  sorry

/-- Distinct partial sums are equivalent to having no zero-sum interval starting
after the first element. This is the equivalence used at the start of Section 5. -/
theorem valid_iff_noZeroTailSegments {p : ℕ} {S : Finset (ZMod p)}
    {xs : List (ZMod p)} (hord : IsOrdering S xs) :
    IsValidOrdering S xs ↔ HasNoZeroTailSegments xs := by
  sorry

/-- Deterministic local-repair argument in the proof of Theorem 1.2:
if none of `𝓑₁,𝓑₂,𝓑₃` occurs, the bad right endpoints can be repaired one by one
by disjoint local swaps. -/
theorem section5_local_repair {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p) (hgood : Section5Good D σ) :
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      HasNoZeroTailSegments (indexedToList (applyPositionPerm σ π)) := by
  sorry

end IndexedRepair

end GrahamRearrangement
