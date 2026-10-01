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

def indexInterval {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.val ≤ i.val ∧ i.val ≤ b.val

theorem card_indexInterval {n : ℕ} (a b : Fin n)
    (hab : a.val ≤ b.val) :
    (indexInterval a b).card = b.val - a.val + 1 := by
  classical
  rw [show indexInterval a b =
      (Finset.Icc a.val b.val).attachFin n (fun _ hi =>
        lt_of_le_of_lt hi.2 b.isLt) by
      ext i
      simp [indexInterval]]
  simp [Nat.card_Icc, hab]

/-- Half-open index interval [a,b), used after exposing the value at b. -/
def indexHalfOpen {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.val ≤ i.val ∧ i.val < b.val

theorem card_indexHalfOpen {n : ℕ} (a b : Fin n)
    (hab : a.val ≤ b.val) :
    (indexHalfOpen a b).card = b.val - a.val := by
  classical
  rw [show indexHalfOpen a b =
      (Finset.Ico a.val b.val).attachFin n (fun _ hi =>
        lt_trans hi.2 b.isLt) by
      ext i
      simp [indexHalfOpen]]
  simp [Nat.card_Ico, hab]

/-- Sum of the image of an arbitrary finite index set. -/
def indexSetSum {n p : ℕ} (σ : Fin n → ZMod p)
    (J : Finset (Fin n)) : ZMod p :=
  ∑ i ∈ J, σ i

theorem indexSetSum_indexInterval {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n) :
    indexSetSum σ (indexInterval a b) =
      indexedIntervalSum σ a b := by
  unfold indexSetSum indexInterval indexedIntervalSum
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    simp at hi
    exact ⟨Finset.mem_Icc.2 hi.2, by simp [i.isLt]⟩
  · intro i hi
    simp
  · intro i₁ hi₁ i₂ hi₂ h
    exact Fin.ext h
  · intro j hj
    have hjn : j < n := lt_of_le_of_lt (Finset.mem_Icc.1 hj).2 b.isLt
    refine ⟨⟨j, hjn⟩, ?_, rfl⟩
    simp [indexInterval, Finset.mem_Icc.1 hj]
  · intro i hi
    simp [i.isLt]

/-- The forward paper interval {b,...,b+r}, clipped to {1,...,n}. -/
def forwardWindow {n : ℕ} (b : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    b.val ≤ i.val ∧ i.val ≤ b.val + r

theorem card_forwardWindow_eq {n : ℕ} (b : Fin n) (r : ℕ)
    (hfit : b.val + r < n) :
    (forwardWindow b r).card = r + 1 := by
  classical
  rw [show forwardWindow b r =
      (Finset.Icc b.val (b.val + r)).attachFin n
        (fun i hi => lt_of_le_of_lt hi.2 hfit) by
      ext i
      simp [forwardWindow]]
  simp [Nat.card_Icc]

theorem card_forwardWindow_le {n : ℕ} (b : Fin n) (r : ℕ) :
    (forwardWindow b r).card ≤ r + 1 := by
  classical
  let f : Fin n → ℕ := fun i => i.val - b.val
  apply Finset.card_le_of_injOn f
  · intro i hi
    simp only [forwardWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    exact Finset.mem_range.2 (by omega)
  · intro i hi j hj h
    apply Fin.ext
    simp only [forwardWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi hj
    dsimp [f] at h
    omega

/-- Symmetric paper window {z-r,...,z+r}, clipped to {1,...,n}. -/
def symmetricWindow {n : ℕ} (z : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => Nat.dist i.val z.val ≤ r

theorem card_symmetricWindow_le {n : ℕ} (z : Fin n) (r : ℕ) :
    (symmetricWindow z r).card ≤ 2 * r + 1 := by
  classical
  let f : Fin n → ℕ := fun i => i.val + r - z.val
  apply Finset.card_le_of_injOn f
  · intro i hi
    simp only [symmetricWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    exact Finset.mem_range.2 (by
      rw [Nat.dist_eq] at hi
      omega)
  · intro i hi j hj h
    apply Fin.ext
    dsimp [f] at h
    omega

def backwardWindow {n : ℕ} (x : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun q =>
    q.val ≤ x.val ∧ x.val < q.val + r

theorem card_backwardWindow_le {n : ℕ} (x : Fin n) (r : ℕ) :
    (backwardWindow x r).card ≤ r := by
  classical
  let f : Fin n → ℕ := fun q => x.val - q.val
  apply Finset.card_le_of_injOn f
  · intro q hq
    simp only [backwardWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    exact Finset.mem_range.2 (by omega)
  · intro q hq q' hq' h
    apply Fin.ext
    simp only [backwardWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq hq'
    dsimp [f] at h
    omega

def tailTuples {n : ℕ} (b' : Fin n) (D : ℕ) :
    Finset (Fin D → Fin n) :=
  Finset.univ.filter fun x =>
    StrictMono x ∧ ∀ i, paperPos b' < paperPos (x i)

def tailSizes {n D : ℕ} (b' : Fin n)
    (x : Fin D → Fin n) : Fin D → ℕ :=
  fun i => (x i).val - b'.val

def constraintSet {n D : ℕ}
    (u x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) (i : Fin D) :
    Finset (Fin n) :=
  (indexInterval (u i) (x i)).image (πi i)

def interestingLeftSupport {n D : ℕ}
    (b : Fin n) (x : Fin D → Fin n) : Finset (Fin n) :=
  symmetricWindow b (5 * D) ∪
    Finset.univ.biUnion fun i => backwardWindow (x i) (5 * D)

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

def SwapCrosses {n : ℕ} (q : Fin n × Fin n)
    (I : Finset (Fin n)) : Prop :=
  (q.1 ∈ I ∧ q.2 ∉ I) ∨ (q.1 ∉ I ∧ q.2 ∈ I)

def IsAdmissiblePermutation {n : ℕ} (D : ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Finset (Fin n × Fin n),
    IsAdmissibleCollection D P ∧ collectionPerm P = π

def IsInterestingPermutation {n k : ℕ} (D : ℕ)
    (I : Fin k → Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Finset (Fin n × Fin n),
    IsAdmissibleCollection D P ∧
    collectionPerm P = π ∧
    ∀ q ∈ P, ∃ i, SwapCrosses q (I i)

def interestingPermutations {n k : ℕ} (D : ℕ)
    (I : Fin k → Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (IsInterestingPermutation D I)

def FixedBelow {n : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, paperPos i < paperPos b → π i = i

def FixedOutside {n : ℕ} (b b' : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n,
    (paperPos i < paperPos b ∨ paperPos b' < paperPos i) → π i = i

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

/-- Image of an index set under an ordering. -/
def indexImageSet {n p : ℕ} (σ : Fin n → ZMod p)
    (I : Finset (Fin n)) : Finset (ZMod p) :=
  I.image σ

theorem indexSetSum_eq_subsetSum_image {n p : ℕ}
    {σ : Fin n → ZMod p} (hσ : Function.Injective σ)
    (I : Finset (Fin n)) :
    indexSetSum σ I = subsetSum (indexImageSet σ I) := by
  unfold indexSetSum subsetSum indexImageSet
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact hσ hij

/-- Agreement of two indexed orderings on an exposed set of positions. -/
def AgreesOn {n p : ℕ} (F : Finset (Fin n))
    (σ τ : Fin n → ZMod p) : Prop :=
  ∀ i ∈ F, σ i = τ i

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

def orderingConditionalMass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (given event : (Fin S.card → ZMod p) → Prop)
    [DecidablePred given] [DecidablePred event] : ℝ :=
  uniformConditionalMass (indexedOrderings S) given event

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

end

end GrahamRearrangement
