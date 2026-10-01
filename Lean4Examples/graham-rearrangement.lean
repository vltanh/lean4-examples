import Mathlib

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Pham--Sauermann: Graham's rearrangement conjecture

Source: Huy Tuan Pham and Lisa Sauermann,
"On Graham's rearrangement conjecture", arXiv:2602.15797.

This file follows the paper's structure. Elementary definitions are implemented directly.
The Fourier/probabilistic estimates and the long Section 5 counting arguments are stated at
their natural interfaces and admitted with `sorry`, so that the formal dependency graph of
the paper is explicit.

No compilation/CI assumptions are made by this file.
-/

-- ============================================================================
-- 1. Valid orderings
-- ============================================================================

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

-- ============================================================================
-- 2. Preliminaries: Facts 2.1--2.5
-- ============================================================================

section Preliminaries

/-- Distance from a real number to the nearest integer.

For a real number with fractional part in `[0,1)`, the nearest integer is either
its floor or its ceiling, hence this minimum.
-/
noncomputable def distToInt (y : ℝ) : ℝ :=
  min (Int.fract y) (1 - Int.fract y)

/-- The paper's `‖x‖ₚ`, using the canonical representative of `x : ZMod p`. -/
noncomputable def zmodNorm {p : ℕ} (x : ZMod p) : ℝ :=
  distToInt ((x.val : ℝ) / (p : ℝ))

/-- The additive character `eₚ(x) = exp(2π i x / p)`. -/
noncomputable def ep (p : ℕ) (x : ZMod p) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ))

/-- Fact 2.1. -/
theorem fact2_1 (ys : List ℝ) :
    distToInt ys.sum ^ 2 ≤
      (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
  sorry

/-- Fact 2.2. -/
theorem fact2_2 (y : ℝ) :
    1 - 20 * distToInt y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * distToInt y ^ 2 := by
  sorry

/-- Fact 2.3. -/
theorem fact2_3 {p : ℕ} (hp : p.Prime) (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum := by
  sorry

/-- The `k`-fold sumset used in Fact 2.4. -/
def kfoldSumset {p : ℕ} (A : Finset (ZMod p)) : ℕ → Finset (ZMod p)
  | 0 => {0}
  | k + 1 => kfoldSumset A k + A

/-- Fact 2.4, the repeated Cauchy--Davenport consequence. -/
theorem fact2_4 {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {A : Finset (ZMod p)} (hA : A.Nonempty)
    (hproper : kfoldSumset A k ≠ Finset.univ) :
    1 + k * (A.card - 1) ≤ (kfoldSumset A k).card := by
  sorry

/-- Fact 2.5. -/
theorem fact2_5 {p : ℕ} (hp : p.Prime) (x : ZMod p) :
    (ep p x).re ≤ 1 - 2 * zmodNorm x ^ 2 := by
  sorry

end Preliminaries

-- ============================================================================
-- 3. Anticoncentration on Boolean slices
-- ============================================================================

section BooleanSlice

/-- The sum `Σ(R)` of a finite subset. -/
def subsetSum {p : ℕ} (R : Finset (ZMod p)) : ZMod p :=
  ∑ x ∈ R, x

/-- Uniform probability mass that a size-`m` subset of `S` has sum `z`.

Writing the probability as a ratio of finite cardinalities avoids introducing a
measure space for the Boolean slice.
-/
noncomputable def sliceMass {p : ℕ} (S : Finset (ZMod p))
    (m : ℕ) (z : ZMod p) : ℝ :=
  ((S.powersetCard m).filter (fun R => subsetSum R = z)).card /
    (S.powersetCard m).card

theorem sliceMass_nonneg {p : ℕ} (S : Finset (ZMod p))
    (m : ℕ) (z : ZMod p) :
    0 ≤ sliceMass S m z := by
  positivity

theorem sliceMass_le_one {p : ℕ} (S : Finset (ZMod p))
    (m : ℕ) (z : ZMod p) :
    sliceMass S m z ≤ 1 := by
  unfold sliceMass
  by_cases hzero : (S.powersetCard m).card = 0
  · simp [hzero]
  · apply (div_le_one ?_).2
    · exact_mod_cast Nat.pos_of_ne_zero hzero
    · exact_mod_cast
        (Finset.card_filter_le (S.powersetCard m) (fun R => subsetSum R = z))

/-- Theorem 1.3, in finite-cardinality probability language. -/
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

/-- Theorem 1.3. The paper proves this with the absolute constant `2^24`. -/
theorem theorem13 : Theorem13Statement := by
  sorry

end BooleanSlice

-- ============================================================================
-- 4. Combinatorial anticoncentration deductions
-- ============================================================================

section Chains

/-- All nested chains `R₀ ⊆ ... ⊆ Rₖ₋₁ ⊆ S` with prescribed sizes. -/
noncomputable def chainFamily {p k : ℕ} (S : Finset (ZMod p))
    (m : Fin k → ℕ) : Finset (Fin k → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter fun R =>
    (∀ i, R i ⊆ S ∧ (R i).card = m i) ∧
      ∀ i j, i ≤ j → R i ⊆ R j

/-- Probability mass of prescribed sums along a uniformly random nested chain. -/
noncomputable def chainMass {p k : ℕ} (S : Finset (ZMod p))
    (m : Fin k → ℕ) (z : Fin k → ZMod p) : ℝ := by
  classical
  let F := chainFamily S m
  exact (F.filter (fun R => ∀ i, subsetSum (R i) = z i)).card / F.card

/-- Extend the prescribed chain sizes by `m₀ = 0` and `mₖ₊₁ = n`. -/
def extendedSize {k : ℕ} (n : ℕ) (m : Fin k → ℕ) (i : ℕ) : ℕ :=
  if hi0 : i = 0 then 0
  else if hi : i ≤ k then m ⟨i - 1, by omega⟩
  else n

/-- The consecutive gap `mᵢ₊₁ - mᵢ`. -/
def chainGap {k : ℕ} (n : ℕ) (m : Fin k → ℕ) (i : Fin (k + 1)) : ℕ :=
  extendedSize n m (i.val + 1) - extendedSize n m i.val

/-- One factor in Corollary 4.2. -/
noncomputable def chainFactor (p n : ℕ) (C : ℝ) (gap : ℕ) : ℝ :=
  1 / (p : ℝ) +
    C * Real.sqrt (Real.log (n : ℝ)) /
      ((n : ℝ) * Real.sqrt (gap : ℝ))

/-- The right-hand side in Corollary 4.2:
sum over the omitted gap `j`, product over all remaining gaps. -/
noncomputable def chainUpperBound {k : ℕ} (p n : ℕ)
    (C : ℝ) (m : Fin k → ℕ) : ℝ := by
  classical
  exact ∑ j : Fin (k + 1),
    ∏ i ∈ (Finset.univ.filter fun i : Fin (k + 1) => i ≠ j),
      chainFactor p n C (chainGap n m i)

/-- Corollary 1.4. -/
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

/-- Corollary 4.2: anticoncentration for a random chain of subsets. -/
def Corollary42Statement : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (p : ℕ), p.Prime →
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : Fin k → ℕ),
        StrictMono m →
        (∀ i, 1 ≤ m i ∧ m i < S.card) →
      ∀ z : Fin k → ZMod p,
        chainMass S m z ≤ chainUpperBound p S.card Ck m

/-- Corollary 1.4, deduced in Section 4 from Theorem 1.3 and Lemma 4.1. -/
theorem corollary14 : Corollary14Statement := by
  sorry

/-- Corollary 4.2, the chain anticoncentration estimate used throughout Section 5. -/
theorem corollary42 : Corollary42Statement := by
  sorry

end Chains

-- ============================================================================
-- 5. Rearrangement conjecture: zero-sum intervals and local repairs
-- ============================================================================

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

section UniformOrderings

/-- All indexed orderings of `S`; this is the finite sample space for Section 5. -/
noncomputable def indexedOrderings {p : ℕ} (S : Finset (ZMod p)) :
    Finset (Fin S.card → ZMod p) := by
  classical
  exact Finset.univ.filter fun σ => IsIndexedOrdering S σ

/-- Uniform mass of an event on indexed orderings of `S`. -/
noncomputable def orderingEventMass {p : ℕ} (S : Finset (ZMod p))
    (E : (Fin S.card → ZMod p) → Prop) : ℝ := by
  classical
  let Ω := indexedOrderings S
  exact (Ω.filter E).card / Ω.card

/-- The combined probabilistic output of Lemmas 5.1--5.3 in the regime of
Theorem 1.2. The three constants are exactly `1/100`, `3/100`, and `1/25`. -/
def Section5BadEventBoundsStatement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ (p : ℕ), p.Prime →
      ∀ (S : Finset (ZMod p)),
        0 ∉ S →
        Cα ≤ (S.card : ℝ) →
        (S.card : ℝ) ≤ (p : ℝ) ^ (1 - α) →
        let D := Nat.ceil (3 / α)
        orderingEventMass S (fun σ => BadEvent1 D σ) ≤ (1 / 100 : ℝ) ∧
        orderingEventMass S (fun σ => BadEvent2 D σ) ≤ (3 / 100 : ℝ) ∧
        orderingEventMass S (fun σ => BadEvent3 D σ) ≤ (1 / 25 : ℝ)

/-- Lemmas 5.1--5.3, including their quantitative hypotheses and union-bound setup. -/
theorem section5_bad_event_bounds : Section5BadEventBoundsStatement := by
  sorry

end UniformOrderings

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- Theorem 1.2. -/
def Theorem12Statement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ (p : ℕ), p.Prime →
      ∀ (S : Finset (ZMod p)),
        0 ∉ S →
        Cα ≤ (S.card : ℝ) →
        (S.card : ℝ) ≤ (p : ℝ) ^ (1 - α) →
        HasValidOrdering S

/-- The final Section 5 reduction: the three bad-event estimates have total mass
strictly below one, hence some starting ordering is good; the deterministic local
repair then produces a valid ordering. -/
theorem theorem12_of_section5_bounds
    (hbad : Section5BadEventBoundsStatement) : Theorem12Statement := by
  sorry

/-- Theorem 1.2 of Pham--Sauermann. -/
theorem theorem12 : Theorem12Statement :=
  theorem12_of_section5_bounds section5_bad_event_bounds

end GrahamRearrangement
