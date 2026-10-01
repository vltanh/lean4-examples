import Lean4Examples.GrahamRearrangement.Rearrangement.Definitions

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: interval and partial-sum lemmas

These are the bookkeeping equivalences connecting the introduction's list definition
of a valid ordering with the paper's interval notation in Section 5.
-/

section ListIntervals

variable {G : Type*} [AddCommGroup G]

def listPrefixSum (xs : List G) (k : ℕ) : G :=
  (xs.take k).sum

theorem getElem_partialSums (xs : List G) (i : ℕ)
    (hi : i < xs.length) :
    (partialSums xs)[i]'(by simpa [length_partialSums] using hi) =
      listPrefixSum xs (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [partialSums, listPrefixSum]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simp [partialSums, listPrefixSum, ih i hi', add_assoc]

/-- Sum on the slice [a,b] is the difference of the two relevant prefix sums. -/
theorem listIntervalSum_eq_prefix_sub (xs : List G) (a b : ℕ)
    (hab : a ≤ b) (hb : b < xs.length) :
    listIntervalSum xs a b =
      listPrefixSum xs (b + 1) - listPrefixSum xs a := by
  unfold listIntervalSum listPrefixSum
  have hdecomp :
      xs.take (b + 1) =
        xs.take a ++ (xs.drop a).take (b + 1 - a) := by
    apply List.ext_getElem
    · simp [hab, hb]
    · intro i hi1 hi2
      by_cases hia : i < a
      · simp [List.getElem_take, hia]
      · have hai : a ≤ i := Nat.le_of_not_gt hia
        simp [List.getElem_take, List.getElem_drop, hia, hai]
  rw [hdecomp, List.sum_append]
  abel

theorem listPrefix_eq_iff_interval_zero (xs : List G)
    (a b : ℕ) (hab : a ≤ b) (hb : b < xs.length) :
    listPrefixSum xs a = listPrefixSum xs (b + 1) ↔
      listIntervalSum xs a b = 0 := by
  rw [listIntervalSum_eq_prefix_sub xs a b hab hb]
  exact eq_comm.trans sub_eq_zero.symm

theorem partialSums_nodup_iff_prefix (xs : List G) :
    (partialSums xs).Nodup ↔
      ∀ i j : ℕ, i < j → j < xs.length →
        listPrefixSum xs (i + 1) ≠ listPrefixSum xs (j + 1) := by
  rw [List.nodup_iff_getElem_injective]
  constructor
  · intro hinj i j hij hj heq
    have hi : i < xs.length := lt_trans hij hj
    have hget :
        (partialSums xs)[i]'(by simpa [length_partialSums] using hi) =
          (partialSums xs)[j]'(by simpa [length_partialSums] using hj) := by
      simpa [getElem_partialSums xs i hi, getElem_partialSums xs j hj] using heq
    have := hinj i (by simpa [length_partialSums] using hi)
      j (by simpa [length_partialSums] using hj) hget
    omega
  · intro hp i hi j hj heq
    by_cases hij : i = j
    · exact hij
    · wlog hlt : i < j generalizing i j
      · have hji : j < i := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hij)
        exact (this j hj i hi heq.symm (Ne.symm hij) hji).symm
      have hprefix :
          listPrefixSum xs (i + 1) =
            listPrefixSum xs (j + 1) := by
        simpa [getElem_partialSums xs i (by simpa [length_partialSums] using hi),
          getElem_partialSums xs j (by simpa [length_partialSums] using hj)] using heq
      exact (hp i j hlt (by simpa [length_partialSums] using hj) hprefix).elim

end ListIntervals

section IndexedIntervals

theorem indexedIntervalSum_eq_prefix_sub {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b =
      listPrefixSum (indexedToList σ) (b.val + 1) -
        listPrefixSum (indexedToList σ) a.val := by
  rw [indexedIntervalSum_eq_listIntervalSum σ a b hab]
  apply listIntervalSum_eq_prefix_sub
  · exact hab
  · simpa [indexedToList] using b.isLt

theorem indexed_interval_zero_iff_prefix_eq {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b = 0 ↔
      listPrefixSum (indexedToList σ) a.val =
        listPrefixSum (indexedToList σ) (b.val + 1) := by
  rw [indexedIntervalSum_eq_prefix_sub σ a b hab]
  exact sub_eq_zero

theorem indexed_singleton_sum {n p : ℕ}
    (σ : Fin n → ZMod p) (a : Fin n) :
    indexedIntervalSum σ a a = σ a := by
  unfold indexedIntervalSum
  simp

/-- Distinct partial sums are equivalent to the Section 5 interval condition,
using 0∉S to discard singleton zero intervals. -/
theorem valid_iff_noZeroPaperSegments {p : ℕ}
    {S : Finset (ZMod p)} (hzero : 0 ∉ S)
    {σ : Fin S.card → ZMod p} (hσ : IsIndexedOrdering S σ) :
    IsValidOrdering S (indexedToList σ) ↔ HasNoZeroPaperSegments σ := by
  have hord := indexedToList_isOrdering hσ
  rw [IsValidOrdering]
  simp only [hord, true_and, partialSums_nodup_iff_prefix]
  constructor
  · intro hprefix a b ha hab hsum
    have habv : a.val < b.val := by simpa [paperPos] using hab
    have ha0 : 0 < a.val := by
      simpa [paperPos] using ha
    let i := a.val - 1
    have hi : i < b.val := by
      dsimp [i]
      omega
    have hb : b.val < (indexedToList σ).length := by
      simpa [indexedToList] using b.isLt
    have hEq :
        listPrefixSum (indexedToList σ) (i + 1) =
          listPrefixSum (indexedToList σ) (b.val + 1) := by
      have hz :=
        (indexed_interval_zero_iff_prefix_eq σ a b
          (Nat.le_of_lt habv)).1 hsum
      simpa [i, Nat.sub_add_cancel (Nat.le_of_lt ha0)] using hz
    exact hprefix i b.val hi hb hEq
  · intro hseg i j hij hj hEq
    have hjn : j < S.card := by
      simpa [indexedToList] using hj
    have hi1 : i + 1 < S.card := lt_of_lt_of_le
      (Nat.succ_lt_succ hij) (Nat.le_of_lt_succ hjn)
    let a : Fin S.card := ⟨i + 1, hi1⟩
    let b : Fin S.card := ⟨j, hjn⟩
    have habv : a.val ≤ b.val := by
      dsimp [a, b]
      omega
    have hzeroInterval :
        indexedIntervalSum σ a b = 0 := by
      apply (indexed_interval_zero_iff_prefix_eq σ a b habv).2
      simpa [a, b] using hEq
    by_cases hadj : i + 1 = j
    · have hsingle : σ b = 0 := by
        have : a = b := by
          apply Fin.ext
          simpa [a, b] using hadj
        subst this
        simpa [indexed_singleton_sum] using hzeroInterval
      have hbS : σ b ∈ S := (hσ.2 (σ b)).2 ⟨b, rfl⟩
      exact hzero hbS hsingle
    · have hproper : paperPos a < paperPos b := by
        simp [paperPos, a, b]
        omega
      have ha2 : 2 ≤ paperPos a := by
        simp [paperPos, a]
      exact hseg a b ha2 hproper hzeroInterval

end IndexedIntervals

end GrahamRearrangement
