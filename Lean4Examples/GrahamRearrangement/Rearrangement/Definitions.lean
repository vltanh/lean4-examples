import Lean4Examples.GrahamRearrangement.Combinatorial

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: exact definitions

The implementation uses `Fin n` for the paper's index set `{1,...,n}`.  The
translation is explicit: `paperPos i = i.val + 1`.
-/

noncomputable section

/-- Reversal of the finite paper index set: position a is sent to n+1-a. -/
def reverseIndex (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨n - 1 - i.val, by omega⟩
  invFun i := ⟨n - 1 - i.val, by omega⟩
  left_inv i := by apply Fin.ext; omega
  right_inv i := by apply Fin.ext; omega

@[simp] theorem reverseIndex_apply_val {n : ℕ} (i : Fin n) :
    (reverseIndex n i).val = n - 1 - i.val := rfl

@[simp] theorem reverseIndex_involutive {n : ℕ} (i : Fin n) :
    reverseIndex n (reverseIndex n i) = i := by
  apply Fin.ext
  omega

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

/-- Open-closed interval (a,b], used when splitting a right-extending
zero-sum interval at an exposed endpoint. -/
def indexOpenClosed {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.val < i.val ∧ i.val ≤ b.val

theorem card_indexOpenClosed {n : ℕ} (a b : Fin n)
    (hab : a.val ≤ b.val) :
    (indexOpenClosed a b).card = b.val - a.val := by
  classical
  rw [show indexOpenClosed a b =
      (Finset.Ioc a.val b.val).attachFin n (fun _ hi =>
        lt_of_le_of_lt hi.2 b.isLt) by
      ext i
      simp [indexOpenClosed]]
  simp [Nat.card_Ioc, hab]

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

def headTuples {n : ℕ} (b : Fin n) (D : ℕ) :
    Finset (Fin D → Fin n) :=
  Finset.univ.filter fun x =>
    StrictMono x ∧ ∀ i, paperPos (x i) < paperPos b

def headSizes {n D : ℕ} (b : Fin n)
    (x : Fin D → Fin n) : Fin D → ℕ :=
  fun i => b.val - (x ⟨D - 1 - i.val, by omega⟩).val

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
/-- Conjugation of a position permutation by order reversal. -/
def reverseConjugate {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  (reverseIndex n).trans (π.trans (reverseIndex n))

@[simp] theorem reverseConjugate_apply {n : ℕ}
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    reverseConjugate π i =
      reverseIndex n (π (reverseIndex n i)) := rfl

theorem paperPos_reverseIndex {n : ℕ} (i : Fin n) :
    paperPos (reverseIndex n i) = n + 1 - paperPos i := by
  simp [paperPos, reverseIndex_apply_val]
  omega

def applyPositionPerm {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) : Fin n → ZMod p :=
  σ ∘ π

theorem indexSetSum_applyPositionPerm_image
    {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    indexSetSum (applyPositionPerm σ π) J =
      indexSetSum σ (J.image π) := by
  unfold indexSetSum applyPositionPerm
  rw [Finset.sum_image]
  · rfl
  · intro i hi j hj hij
    exact π.injective hij

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

/-- The transpositions in an admissible collection commute because their
supports are disjoint, exactly as stated in Section 5. -/
theorem admissible_transpositions_commute {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {q r : Fin n × Fin n} (hq : q ∈ P) (hr : r ∈ P)
    (hqr : q ≠ r) :
    (Equiv.swap q.1 q.2).trans (Equiv.swap r.1 r.2) =
      (Equiv.swap r.1 r.2).trans (Equiv.swap q.1 q.2) := by
  have hd := hP.1 hq hr hqr
  have hqne : q.1 ≠ q.2 := by
    have := (hP.2 q hq).1
    simpa [paperPos] using ne_of_lt this
  have hrne : r.1 ≠ r.2 := by
    have := (hP.2 r hr).1
    simpa [paperPos] using ne_of_lt this
  exact Section5External.disjoint_swaps_commute
    q.1 q.2 r.1 r.2 hqne hrne
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

/-- Consequently, `π_P` is independent of the enumeration of the admissible
collection `P`. -/
theorem collectionPerm_order_independent {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (l : List (Fin n × Fin n))
    (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = collectionPerm P := by
  unfold collectionPerm
  exact Section5External.disjoint_swaps_order_independent
    P hP.1 l hl hln

/-- The paper's observation that an admissible collection can be uniquely
reconstructed from its permutation. -/
theorem admissibleCollection_reconstruct {n D : ℕ}
    {P Q : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (hQ : IsAdmissibleCollection D Q)
    (hperm : collectionPerm P = collectionPerm Q) :
    P = Q := by
  unfold collectionPerm at hperm
  apply Section5External.disjoint_swaps_reconstruct
    P Q hP.1 hQ.1
  · intro q hq
    simpa [paperPos] using (hP.2 q hq).1
  · intro q hq
    simpa [paperPos] using (hQ.2 q hq).1
  · exact hperm

def supportedAdmissibleCollections {n : ℕ}
    (D : ℕ) (Q : Finset (Fin n)) :
    Finset (Finset (Fin n × Fin n)) :=
  Finset.univ.filter fun P =>
    IsAdmissibleCollection D P ∧
      ∀ q ∈ P, q.1 ∈ Q

def IsAdmissiblePermutation {n : ℕ} (D : ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Finset (Fin n × Fin n),
    IsAdmissibleCollection D P ∧ collectionPerm P = π

def Lemma55Event {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (b b' : Fin n)
    (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) : Prop :=
  ∃ x ∈ tailTuples b' D,
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (πi i))
          (u i) (x i) = 0

def Lemma56Event {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (b b' : Fin n)
    (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) : Prop :=
  ∃ x ∈ headTuples b D,
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (πi i))
          (x i) (u i) = 0

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

structure RepairParams (n D : ℕ) where
  b : Fin n
  b' : Fin n
  y : Fin D → Fin n
  u : Fin D → Fin n
deriving DecidableEq, Fintype

def strictForwardWindow {n : ℕ} (b : Fin n) (r : ℕ) :
    Finset (Fin n) :=
  (forwardWindow b r).erase b

theorem mem_strictForwardWindow {n r : ℕ} {b x : Fin n} :
    x ∈ strictForwardWindow b r ↔
      paperPos b < paperPos x ∧
        paperPos x ≤ paperPos b + r := by
  simp [strictForwardWindow,forwardWindow,paperPos]
  omega

theorem card_strictForwardWindow_le {n : ℕ}
    (b : Fin n) (r : ℕ) :
    (strictForwardWindow b r).card ≤ r := by
  have hb : b ∈ forwardWindow b r := by
    simp [forwardWindow]
  unfold strictForwardWindow
  rw [Finset.card_erase_of_mem hb]
  have hw := card_forwardWindow_le b r
  omega

def canonicalLocalEnd {n : ℕ} (b : Fin n) (D : ℕ)
    (hfit : paperPos b + 5 * D ≤ n) : Fin n :=
  ⟨b.val + 5 * D, by
    simp [paperPos] at hfit
    omega⟩

theorem canonicalLocalEnd_gap {n D : ℕ} (b : Fin n)
    (hfit : paperPos b + 5 * D ≤ n) :
    paperPos (canonicalLocalEnd b D hfit) - paperPos b = 5 * D := by
  simp [canonicalLocalEnd,paperPos]

def rightRepairParameters (n D : ℕ) :
    Finset (RepairParams n D) := by
  classical
  exact Finset.univ.biUnion fun b =>
    if hfit : paperPos b + 30 * D ≤ n then
      let b' := canonicalLocalEnd b D (by omega)
      let Y := Finset.univ.pi fun _ : Fin D =>
        strictForwardWindow b (5 * D)
      Y.biUnion fun y =>
        Y.image fun u => ⟨b,b',y,u⟩
    else ∅

def leftRepairParameters (n D : ℕ) :
    Finset (RepairParams n D) := by
  classical
  exact Finset.univ.biUnion fun b =>
    if hfit : paperPos b + 30 * D ≤ n then
      let b' := canonicalLocalEnd b D (by omega)
      let Y := Finset.univ.pi fun _ : Fin D =>
        strictForwardWindow b (5 * D)
      let U := Finset.univ.pi fun _ : Fin D =>
        indexHalfOpen b b'
      Y.biUnion fun y =>
        U.image fun u => ⟨b,b',y,u⟩
    else ∅

theorem mem_rightRepairParameters {n D : ℕ}
    {θ : RepairParams n D} :
    θ ∈ rightRepairParameters n D ↔
      2 ≤ paperPos θ.b ∧
      paperPos θ.b + 30 * D ≤ n ∧
      paperPos θ.b' - paperPos θ.b = 5 * D ∧
      (∀ i,
        paperPos θ.b < paperPos (θ.y i) ∧
          paperPos (θ.y i) ≤ paperPos θ.b') ∧
      (∀ i,
        paperPos θ.b < paperPos (θ.u i) ∧
          paperPos (θ.u i) ≤ paperPos θ.b') := by
  classical
  constructor
  · intro h
    simp [rightRepairParameters] at h
    rcases h with ⟨b,hfit,y,hy,u,hu,rfl⟩
    have hb2 : 2 ≤ paperPos b := by
      by_contra hsmall
      omega
    refine ⟨hb2,hfit,canonicalLocalEnd_gap b (by omega),?_,?_⟩
    · intro i
      exact (mem_strictForwardWindow.mp
        (Finset.mem_pi.mp hy i (Finset.mem_univ i))).trans_le
          (by simp [canonicalLocalEnd,paperPos])
    · intro i
      exact (mem_strictForwardWindow.mp
        (Finset.mem_pi.mp hu i (Finset.mem_univ i))).trans_le
          (by simp [canonicalLocalEnd,paperPos])
  · rintro ⟨hb2,hfit,hgap,hy,hu⟩
    simp [rightRepairParameters]
    refine ⟨θ.b,hfit,θ.y,?_,θ.u,?_,?_⟩
    · apply Finset.mem_pi.mpr
      intro i hi
      exact mem_strictForwardWindow.mpr
        ⟨(hy i).1, by
          have hgap' := hgap
          simp [paperPos] at hgap'
          omega⟩
    · apply Finset.mem_pi.mpr
      intro i hi
      exact mem_strictForwardWindow.mpr
        ⟨(hu i).1, by
          have hgap' := hgap
          simp [paperPos] at hgap'
          omega⟩
    · cases θ
      simp [canonicalLocalEnd,paperPos] at hgap ⊢
      omega

theorem mem_leftRepairParameters {n D : ℕ}
    {θ : RepairParams n D} :
    θ ∈ leftRepairParameters n D ↔
      2 ≤ paperPos θ.b ∧
      paperPos θ.b + 30 * D ≤ n ∧
      paperPos θ.b' - paperPos θ.b = 5 * D ∧
      (∀ i,
        paperPos θ.b < paperPos (θ.y i) ∧
          paperPos (θ.y i) ≤ paperPos θ.b') ∧
      (∀ i,
        paperPos θ.b ≤ paperPos (θ.u i) ∧
          paperPos (θ.u i) < paperPos θ.b') := by
  classical
  constructor
  · intro h
    simp [leftRepairParameters] at h
    rcases h with ⟨b,hfit,y,hy,u,hu,rfl⟩
    have hb2 : 2 ≤ paperPos b := by
      by_contra hsmall
      omega
    let b' := canonicalLocalEnd b D (by omega)
    refine ⟨hb2,hfit,canonicalLocalEnd_gap b (by omega),?_,?_⟩
    · intro i
      have h := mem_strictForwardWindow.mp
        (Finset.mem_pi.mp hy i (Finset.mem_univ i))
      simpa [b',canonicalLocalEnd,paperPos] using h
    · intro i
      have h := Finset.mem_pi.mp hu i (Finset.mem_univ i)
      simpa [indexHalfOpen,paperPos,b',canonicalLocalEnd] using h
  · rintro ⟨hb2,hfit,hgap,hy,hu⟩
    simp [leftRepairParameters]
    refine ⟨θ.b,hfit,θ.y,?_,θ.u,?_,?_⟩
    · apply Finset.mem_pi.mpr
      intro i hi
      exact mem_strictForwardWindow.mpr
        ⟨(hy i).1, by
          have hgap' := hgap
          simp [paperPos] at hgap'
          omega⟩
    · apply Finset.mem_pi.mpr
      intro i hi
      simp [indexHalfOpen,paperPos]
      exact hu i
    · cases θ
      simp [canonicalLocalEnd,paperPos] at hgap ⊢
      omega

theorem rightRepairParameters_card_le (n D : ℕ) :
    (rightRepairParameters n D).card ≤
      n * (5 * D) ^ (2 * D) := by
  classical
  unfold rightRepairParameters
  calc
    _ ≤ ∑ b : Fin n,
        (if hfit : paperPos b + 30 * D ≤ n then
          let Y := Finset.univ.pi fun _ : Fin D =>
            strictForwardWindow b (5 * D)
          Y.card * Y.card
        else 0) := by
          apply card_biUnion_le_sum
    _ ≤ ∑ _b : Fin n, (5 * D) ^ (2 * D) := by
          gcongr with b
          split
          · let Y := Finset.univ.pi fun _ : Fin D =>
              strictForwardWindow b (5 * D)
            have hY : Y.card ≤ (5 * D) ^ D :=
              card_pi_le_pow
                (fun _ : Fin D => strictForwardWindow b (5 * D))
                (5 * D) (fun _ => card_strictForwardWindow_le b (5 * D))
            calc
              Y.card * Y.card ≤ (5 * D) ^ D * (5 * D) ^ D :=
                Nat.mul_le_mul hY hY
              _ = (5 * D) ^ (2 * D) := by
                rw [← pow_add]
                congr
                omega
          · simp
    _ = n * (5 * D) ^ (2 * D) := by simp

theorem leftRepairParameters_card_le (n D : ℕ) :
    (leftRepairParameters n D).card ≤
      n * (5 * D) ^ (2 * D) := by
  classical
  unfold leftRepairParameters
  calc
    _ ≤ ∑ b : Fin n,
        (if hfit : paperPos b + 30 * D ≤ n then
          let b' := canonicalLocalEnd b D (by omega)
          let Y := Finset.univ.pi fun _ : Fin D =>
            strictForwardWindow b (5 * D)
          let U := Finset.univ.pi fun _ : Fin D =>
            indexHalfOpen b b'
          Y.card * U.card
        else 0) := by
          apply card_biUnion_le_sum
    _ ≤ ∑ _b : Fin n, (5 * D) ^ (2 * D) := by
          gcongr with b
          split
          · let b' := canonicalLocalEnd b D (by omega)
            let Y := Finset.univ.pi fun _ : Fin D =>
              strictForwardWindow b (5 * D)
            let U := Finset.univ.pi fun _ : Fin D =>
              indexHalfOpen b b'
            have hY : Y.card ≤ (5 * D) ^ D :=
              card_pi_le_pow
                (fun _ : Fin D => strictForwardWindow b (5 * D))
                (5 * D) (fun _ => card_strictForwardWindow_le b (5 * D))
            have hU : U.card ≤ (5 * D) ^ D := by
              apply card_pi_le_pow
              intro i
              rw [card_indexHalfOpen b b' (by
                simp [b',canonicalLocalEnd,paperPos]; omega)]
              simp [b',canonicalLocalEnd,paperPos]
            calc
              Y.card * U.card ≤ (5 * D) ^ D * (5 * D) ^ D :=
                Nat.mul_le_mul hY hU
              _ = (5 * D) ^ (2 * D) := by
                rw [← pow_add]
                congr
                omega
          · simp
    _ = n * (5 * D) ^ (2 * D) := by simp

/-- Right-extending witness event used in the proof of Lemma 5.3. -/
def RightRepairEvent {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) : Prop :=
  ∃ b b' : Fin n,
    2 ≤ paperPos b ∧
    paperPos b + 30 * D ≤ n ∧
    paperPos b' - paperPos b = 5 * D ∧
    ∃ y u : Fin D → Fin n,
      (∀ i,
        paperPos b < paperPos (y i) ∧
          paperPos (y i) ≤ paperPos b') ∧
      (∀ i,
        paperPos b < paperPos (u i) ∧
          paperPos (u i) ≤ paperPos b') ∧
      Lemma55Event σ b b' u
        (fun i => Equiv.swap b (y i))

/-- Left-extending witness event used in the proof of Lemma 5.3. -/
def LeftRepairEvent {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) : Prop :=
  ∃ b b' : Fin n,
    2 ≤ paperPos b ∧
    paperPos b + 30 * D ≤ n ∧
    paperPos b' - paperPos b = 5 * D ∧
    ∃ y u : Fin D → Fin n,
      (∀ i,
        paperPos b < paperPos (y i) ∧
          paperPos (y i) ≤ paperPos b') ∧
      (∀ i,
        paperPos b ≤ paperPos (u i) ∧
          paperPos (u i) < paperPos b') ∧
      Lemma56Event σ b b' u
        (fun i => Equiv.swap b (y i))

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
