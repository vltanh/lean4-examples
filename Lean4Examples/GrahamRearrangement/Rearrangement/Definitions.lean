import Lean4Examples.GrahamRearrangement.Combinatorial

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: exact definitions

The implementation uses `Fin n` for the paper's index set `{1,...,n}`.  The
translation is explicit: `paperPos i = i.val + 1`.
-/

noncomputable section

def paperPos {n : ℕ} (i : Fin n) : ℕ := i.val + 1

theorem paperPos_pos {n : ℕ} (i : Fin n) : 1 ≤ paperPos i := by
  simp [paperPos]

theorem paperPos_le {n : ℕ} (i : Fin n) : paperPos i ≤ n := by
  simp [paperPos]
  exact i.isLt

theorem paperPos_lt_iff {n : ℕ} {i j : Fin n} :
    paperPos i < paperPos j ↔ i.val < j.val := by
  simp [paperPos]

/-- An indexed ordering of S, corresponding to a bijection {1,...,|S|} -> S. -/
def IsIndexedOrdering {p : ℕ} (S : Finset (ZMod p))
    (σ : Fin S.card → ZMod p) : Prop :=
  Function.Injective σ ∧ ∀ x, x ∈ S ↔ ∃ i, σ i = x

def indexedToList {n p : ℕ} (σ : Fin n → ZMod p) : List (ZMod p) :=
  List.ofFn σ

/-- Paper interval sum Σ(σ,[a,b]), written in zero-based representatives. -/
def indexedIntervalSum {n p : ℕ} (σ : Fin n → ZMod p)
    (a b : Fin n) : ZMod p :=
  ∑ i ∈ Finset.Icc a.val b.val,
    if hi : i < n then σ ⟨i, hi⟩ else 0

/-- Sum of the image of an arbitrary finite index set. -/
def indexSetSum {n p : ℕ} (σ : Fin n → ZMod p)
    (J : Finset (Fin n)) : ZMod p :=
  ∑ i ∈ J, σ i

/-- The forward paper interval {b,...,b+r}, clipped to {1,...,n}. -/
def forwardWindow {n : ℕ} (b : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    b.val ≤ i.val ∧ i.val ≤ b.val + r

/-- Symmetric paper window {z-r,...,z+r}, clipped to {1,...,n}. -/
def symmetricWindow {n : ℕ} (z : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => Nat.dist i.val z.val ≤ r

/-- B(σ): right endpoints of zero-sum intervals [a,b] with 2≤a<b≤n. -/
def badRightEndpoints {n p : ℕ}
    (σ : Fin n → ZMod p) : Finset (Fin n) :=
  Finset.univ.filter fun b =>
    ∃ a : Fin n,
      2 ≤ paperPos a ∧ paperPos a < paperPos b ∧
        indexedIntervalSum σ a b = 0

@[simp] theorem mem_badRightEndpoints_iff {n p : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n) :
    b ∈ badRightEndpoints σ ↔
      ∃ a : Fin n,
        2 ≤ paperPos a ∧ paperPos a < paperPos b ∧
          indexedIntervalSum σ a b = 0 := by
  simp [badRightEndpoints]

theorem badRightEndpoint_ge_three {n p : ℕ}
    {σ : Fin n → ZMod p} {b : Fin n}
    (hb : b ∈ badRightEndpoints σ) :
    3 ≤ paperPos b := by
  rcases (mem_badRightEndpoints_iff σ b).1 hb with ⟨a, ha2, hab, _⟩
  omega

/-- Exact target condition used in Section 5: no zero-sum [a,b] with 2≤a<b. -/
def HasNoZeroPaperSegments {n p : ℕ} (σ : Fin n → ZMod p) : Prop :=
  ∀ a b : Fin n,
    2 ≤ paperPos a → paperPos a < paperPos b →
      indexedIntervalSum σ a b ≠ 0

/-- Apply a permutation of paper positions. Composition order agrees with σ∘π. -/
def applyPositionPerm {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) : Fin n → ZMod p :=
  σ ∘ π

def swapPairsDisjoint {n : ℕ} (q r : Fin n × Fin n) : Prop :=
  q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2

/-- An admissible collection P of disjoint pairs (x,y), x<y, y-x≤5D. -/
def IsAdmissibleCollection {n : ℕ} (D : ℕ)
    (P : Finset (Fin n × Fin n)) : Prop :=
  P.toSet.Pairwise swapPairsDisjoint ∧
    ∀ q ∈ P,
      paperPos q.1 < paperPos q.2 ∧
        paperPos q.2 - paperPos q.1 ≤ 5 * D

def swapsPermList {n : ℕ} :
    List (Fin n × Fin n) → Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | q :: qs => (Equiv.swap q.1 q.2).trans (swapsPermList qs)

/-- Canonical composition of the disjoint swaps in P. -/
def collectionPerm {n : ℕ}
    (P : Finset (Fin n × Fin n)) : Equiv.Perm (Fin n) :=
  swapsPermList P.toList

def IsAdmissiblePermutation {n : ℕ} (D : ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Finset (Fin n × Fin n),
    IsAdmissibleCollection D P ∧ collectionPerm P = π

def FixedBelow {n : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, paperPos i < paperPos b → π i = i

def FixedThrough {n : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, paperPos i ≤ paperPos b → π i = i

/-- The paper's definition of y blocked for σ,b,π. -/
def IsBlockedAt {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p)
    (b : Fin n) (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  paperPos b < paperPos y ∧
  paperPos y ≤ paperPos b + 5 * D ∧
  ∃ s t : Fin n,
    2 ≤ paperPos s ∧ paperPos s < paperPos t ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y)) s t = 0 ∧
    ((paperPos b < paperPos s ∧ paperPos s ≤ paperPos y) ∨
      (paperPos b ≤ paperPos t ∧ paperPos t < paperPos y))

def blockedCandidates {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun y => IsBlockedAt D σ b π y

/-- Bad event B₁, exactly as in Lemma 5.1. -/
def BadEvent1 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ badRightEndpoints σ,
    n ≤ paperPos b + 30 * D

/-- Bad event B₂, exactly as in Lemma 5.2. -/
def BadEvent2 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ z : Fin n,
    D < ((badRightEndpoints σ) ∩ symmetricWindow z (10 * D)).card

/-- Bad event B₃, exactly as in Lemma 5.3. -/
def BadEvent3 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ badRightEndpoints σ,
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      FixedBelow b π ∧
      2 * D ≤ (blockedCandidates D σ b π).card

/-- Auxiliary bad event B₀ from Lemma 5.4. -/
def BadEvent0 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ badRightEndpoints σ,
    paperPos b + 30 * D ≤ n ∧
    ∃ J J' : Finset (Fin n),
      J ⊆ forwardWindow b (20 * D) ∧
      J' ⊆ forwardWindow b (20 * D) ∧
      J ≠ J' ∧
      indexSetSum σ J = indexSetSum σ J'

def Section5Good {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ¬ BadEvent1 D σ ∧ ¬ BadEvent2 D σ ∧ ¬ BadEvent3 D σ

/-- All indexed orderings of S: the finite sample space for the random bijection σ. -/
def indexedOrderings {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    Finset (Fin S.card → ZMod p) :=
  Finset.univ.filter fun σ => IsIndexedOrdering S σ

def orderingEventMass {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E] : ℝ :=
  uniformMass (indexedOrderings S) E

/-- List interval sum, retained only for translating back to the introduction. -/
def listIntervalSum {G : Type*} [AddCommMonoid G]
    (xs : List G) (a b : ℕ) : G :=
  ((xs.drop a).take (b + 1 - a)).sum

theorem indexedToList_isOrdering {p : ℕ} {S : Finset (ZMod p)}
    {σ : Fin S.card → ZMod p} (hσ : IsIndexedOrdering S σ) :
    IsOrdering S (indexedToList σ) := by
  constructor
  · rw [indexedToList, List.nodup_iff_getElem_injective]
    intro i hi j hj hij
    exact Fin.mk.inj (hσ.1 (by simpa using hij))
  · ext x
    simp only [indexedToList, List.mem_toFinset, List.mem_ofFn]
    rw [hσ.2]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩

/-- The exact bridge between paper intervals and list intervals. -/
theorem indexedIntervalSum_eq_listIntervalSum {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n) (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b =
      listIntervalSum (indexedToList σ) a.val b.val := by
  unfold indexedIntervalSum listIntervalSum indexedToList
  rw [List.sum_take_drop_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro i hi
  simp only
  have hin : i < n := lt_of_le_of_lt (Finset.mem_Icc.1 hi).2 b.isLt
  simp [hin]

/-- Distinct partial sums are equivalent to the absence of zero proper intervals
starting at paper position at least 2, provided the entries themselves are nonzero. -/
theorem valid_iff_noZeroPaperSegments {p : ℕ}
    {S : Finset (ZMod p)} (hzero : 0 ∉ S)
    {σ : Fin S.card → ZMod p} (hσ : IsIndexedOrdering S σ) :
    IsValidOrdering S (indexedToList σ) ↔ HasNoZeroPaperSegments σ := by
  have hord := indexedToList_isOrdering hσ
  rw [IsValidOrdering]
  simp only [hord, true_and]
  rw [List.nodup_iff_pairwise_ne]
  constructor
  · intro hps a b ha hab hsum
    have hab0 : a.val < b.val := by simpa [paperPos] using hab
    have hcollision :
        (partialSums (indexedToList σ))[a.val - 1]? =
          (partialSums (indexedToList σ))[b.val]? := by
      exact partialSums_collision_of_intervalSum_zero
        σ a b ha hab hsum
    exact hps hcollision
  · intro hseg
    intro i hi j hj hij
    by_cases hijOrd : i < j
    · have hzeroInterval :=
        intervalSum_zero_of_partialSums_collision σ i j hijOrd hij
      by_cases hi0 : i = 0
      · subst hi0
        have hxS : σ ⟨j, by simpa [indexedToList] using hj⟩ ∈ S :=
          (hσ.2 _).2 ⟨_, rfl⟩
        exact hzero hxS (single_or_prefix_zero hzeroInterval)
      · have ha : 2 ≤ paperPos ⟨i, by simpa [indexedToList] using hi⟩ := by
          simp [paperPos]
          omega
        exact hseg _ _ ha (by simp [paperPos, hijOrd]) hzeroInterval
    · have hji : j < i := lt_of_le_of_ne (Nat.le_of_not_gt hijOrd) (by
        intro h; subst h; exact hi.ne hj)
      exact (h _ hj _ hi (by simpa [eq_comm] using hij)).symm

end

end GrahamRearrangement
