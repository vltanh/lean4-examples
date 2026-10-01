import Lean4Examples.GrahamRearrangement.BooleanSlice

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 4: definitions

Finite sample spaces and expressions used in the combinatorial anticoncentration
deductions.
-/

noncomputable section

/-- All nested chains R₁ ⊂ ... ⊂ Rₖ ⊂ S with prescribed cardinalities.
The paper writes strict inclusions; strict growth of the supplied sizes makes the
subset conditions strict automatically. -/
def chainFamily {p k : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : Fin k → ℕ) : Finset (Fin k → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter fun R =>
    (∀ i, R i ⊆ S ∧ (R i).card = m i) ∧
      ∀ i j, i ≤ j → R i ⊆ R j

/-- Uniform probability mass of prescribed sums on a nested-chain sample space. -/
def chainMass {p k : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : Fin k → ℕ) (z : Fin k → ZMod p) : ℝ :=
  uniformMass (chainFamily S m)
    (fun R => ∀ i, subsetSum (R i) = z i)

/-- Extend m₁,...,mₖ by m₀=0 and mₖ₊₁=n. -/
def extendedSize {k : ℕ} (n : ℕ) (m : Fin k → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if hi : i ≤ k then m ⟨i - 1, by omega⟩
  else n

/-- Consecutive gap mᵢ₊₁-mᵢ. -/
def chainGap {k : ℕ} (n : ℕ) (m : Fin k → ℕ)
    (i : Fin (k + 1)) : ℕ :=
  extendedSize n m (i.val + 1) - extendedSize n m i.val

/-- One Corollary 4.2 factor. -/
def chainFactor (p n : ℕ) (C : ℝ) (gap : ℕ) : ℝ :=
  1 / (p : ℝ) +
    C * Real.sqrt (Real.log (n : ℝ)) /
      ((n : ℝ) * Real.sqrt (gap : ℝ))

/-- Right-hand side of Corollary 4.2. -/
def chainUpperBound {k : ℕ} (p n : ℕ) (C : ℝ)
    (m : Fin k → ℕ) : ℝ :=
  ∑ j : Fin (k + 1),
    ∏ i ∈ (Finset.univ.erase j),
      chainFactor p n C (chainGap n m i)

/-- Exact hypotheses on the size tuple in Corollary 4.2. -/
def IsChainSizeTuple {k : ℕ} (n : ℕ) (m : Fin k → ℕ) : Prop :=
  StrictMono m ∧ ∀ i, 1 ≤ m i ∧ m i < n

/-- Finite family over which Lemma 4.3 sums. -/
def chainSizeTuples (n k : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact Finset.univ.filter (IsChainSizeTuple n)

/-- Generic weighted sum over increasing h-tuples, using only the first h
gaps (from 0 to m₁, ..., m_{h-1} to m_h). -/
def prefixKernelSum (n h : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ chainSizeTuples n h,
    ∏ i : Fin h,
      w (chainGap n m ⟨i.val, Nat.lt.step i.isLt⟩)

/-- Generic sum with one of the k+1 consecutive gaps omitted. -/
def omittedKernelSum (n k : ℕ) (w : ℕ → ℝ)
    (j : Fin (k + 1)) : ℝ :=
  ∑ m ∈ chainSizeTuples n k,
    ∏ i ∈ Finset.univ.erase j, w (chainGap n m i)

def leftPrefixTuple {k : ℕ}
    (m : Fin k → ℕ) (j : Fin (k + 1)) :
    Fin j.val → ℕ :=
  fun i => m ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩

def reverseRightTuple {k : ℕ} (n : ℕ)
    (m : Fin k → ℕ) (j : Fin (k + 1)) :
    Fin (k - j.val) → ℕ :=
  fun i =>
    n - m ⟨k - 1 - i.val, by
      have hij : i.val < k - j.val := i.isLt
      omega⟩

theorem leftPrefixTuple_mem {n k : ℕ}
    {m : Fin k → ℕ} (hm : m ∈ chainSizeTuples n k)
    (j : Fin (k + 1)) :
    leftPrefixTuple m j ∈ chainSizeTuples n j.val := by
  rcases Finset.mem_filter.mp hm with ⟨_, hmono, hrange⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  constructor
  · intro a b hab
    exact hmono (by simpa [leftPrefixTuple] using hab)
  · intro i
    exact hrange ⟨i.val, lt_of_lt_of_le i.isLt
      (Nat.le_of_lt_succ j.isLt)⟩

theorem reverseRightTuple_mem {n k : ℕ}
    {m : Fin k → ℕ} (hm : m ∈ chainSizeTuples n k)
    (j : Fin (k + 1)) :
    reverseRightTuple n m j ∈
      chainSizeTuples n (k - j.val) := by
  rcases Finset.mem_filter.mp hm with ⟨_, hmono, hrange⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  constructor
  · intro a b hab
    dsimp [reverseRightTuple]
    have hidx :
        k - 1 - b.val < k - 1 - a.val := by omega
    have hlt := hmono (show
      (⟨k - 1 - b.val, by omega⟩ : Fin k) <
      ⟨k - 1 - a.val, by omega⟩ by simpa)
    omega
  · intro i
    have hri := hrange ⟨k - 1 - i.val, by omega⟩
    dsimp [reverseRightTuple]
    constructor <;> omega

theorem fullTuple_eq_of_left_reverseRight_eq {n k : ℕ}
    (m m' : Fin k → ℕ) (j : Fin (k + 1))
    (h :
      (leftPrefixTuple m j, reverseRightTuple n m j) =
        (leftPrefixTuple m' j, reverseRightTuple n m' j)) :
    m = m' := by
  funext i
  have hleft := congrArg Prod.fst h
  have hright := congrArg Prod.snd h
  by_cases hi : i.val < j.val
  · exact congrFun hleft ⟨i.val, hi⟩
  · have hir : k - 1 - i.val < k - j.val := by omega
    have hr := congrFun hright ⟨k - 1 - i.val, hir⟩
    dsimp [reverseRightTuple] at hr
    omega

theorem extendedSize_step_le {n k : ℕ}
    {m : Fin k → ℕ} (hm : IsChainSizeTuple n m)
    {i : ℕ} (hi : i ≤ k) :
    extendedSize n m i ≤ extendedSize n m (i + 1) := by
  rcases hm with ⟨hmono, hrange⟩
  by_cases h0 : i = 0
  · subst i
    by_cases hk : k = 0
    · simp [extendedSize]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      simp [extendedSize, hkpos, (hrange ⟨0,hkpos⟩).1]
  · by_cases hik : i = k
    · subst i
      by_cases hk : k = 0
      · contradiction
      · have hlast := (hrange ⟨k-1, by omega⟩).2
        simp [extendedSize, h0, hlast]
    · have hi' : i < k := lt_of_le_of_ne hi hik
      have him1 : i - 1 < k := by omega
      have hii : i < k := hi'
      have hlt :
          m ⟨i - 1, him1⟩ < m ⟨i, hii⟩ := by
        apply hmono
        simp
        omega
      simp [extendedSize, h0, hi, hi', hlt]

theorem sum_chainGap {n k : ℕ}
    (m : Fin k → ℕ) (hm : IsChainSizeTuple n m) :
    ∑ i : Fin (k + 1), chainGap n m i = n := by
  rw [show (∑ i : Fin (k + 1), chainGap n m i) =
      ∑ i in Finset.range (k + 1),
        (extendedSize n m (i + 1) - extendedSize n m i) by
      apply Fin.sum_univ_eq_sum_range]
  have htel :
      ∀ r ≤ k + 1,
        (∑ i in Finset.range r,
          (extendedSize n m (i + 1) - extendedSize n m i)) =
          extendedSize n m r - extendedSize n m 0 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have hstep := extendedSize_step_le hm (show r ≤ k by omega)
      omega
  rw [htel (k + 1) (by rfl)]
  simp [extendedSize]

/-- Split the prefix tuple sum according to its last value. -/
theorem prefixKernelSum_succ (n h : ℕ) (w : ℕ → ℝ) :
    prefixKernelSum n (h + 1) w =
      ∑ m ∈ chainSizeTuples n h,
        (∏ i : Fin h,
          w (chainGap n m ⟨i.val, Nat.lt.step i.isLt⟩)) *
        ∑ d ∈ Finset.Icc 1
            (n - extendedSize n m h - 1), w d := by
  classical
  unfold prefixKernelSum
  apply Finset.sum_bij
    (fun M _ => fun i : Fin h => M i.castSucc)
  · intro M hM
    have hprefix : (fun i : Fin h => M i.castSucc) ∈
        chainSizeTuples n h := by
      exact leftPrefixTuple_mem hM ⟨h, by omega⟩
    exact hprefix
  · intro M hM
    rw [Fin.prod_univ_succ]
    rfl
  · intro M hM N hN hMN
    have hlastM := M ⟨h, by omega⟩
    have hlastN := N ⟨h, by omega⟩
    apply funext
    intro i
    by_cases hi : i.val < h
    · exact congrFun hMN ⟨i.val,hi⟩
    · have : i.val = h := by omega
      subst i
      exact Fin.ext rfl
  · intro m hm
    refine ⟨?_, ?_, rfl⟩
    let M : Fin (h + 1) → ℕ := fun i =>
      if hi : i.val < h then m ⟨i.val,hi⟩
      else extendedSize n m h + 1
    refine ⟨M, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_filter.mp hm with ⟨_, hmono, hrange⟩
      constructor
      · intro a b hab
        simp [M]
        split <;> split <;> omega
      · intro i
        simp [M]
        split
        · exact hrange _
        · have hlast : extendedSize n m h < n := by
            cases h with
            | zero => simp [extendedSize]
            | succ h =>
              exact (hrange ⟨h, by omega⟩).2
          omega
    · funext i
      simp [M]

theorem omitted_product_split {n k : ℕ} (w : ℕ → ℝ)
    (m : Fin k → ℕ) (j : Fin (k + 1)) :
    (∏ i ∈ Finset.univ.erase j, w (chainGap n m i)) =
      (∏ i : Fin j.val,
        w (chainGap n (leftPrefixTuple m j)
          ⟨i.val, Nat.lt.step i.isLt⟩)) *
      (∏ i : Fin (k - j.val),
        w (chainGap n (reverseRightTuple n m j)
          ⟨i.val, Nat.lt.step i.isLt⟩)) := by
  classical
  apply Finset.prod_bij
    (fun i _ =>
      if h : i.val < j.val then
        Sum.inl ⟨i.val,h⟩
      else
        Sum.inr ⟨k - i.val, by omega⟩)
  · intro i hi
    simp
  · intro i hi
    simp [leftPrefixTuple, reverseRightTuple, chainGap, extendedSize]
  · intro i hi i' hi' h
    cases h <;> omega
  · intro s hs
    cases s with
    | inl i =>
      exact ⟨⟨i.val, by omega⟩, by simp [i.isLt], by simp [i.isLt]⟩
    | inr i =>
      exact ⟨⟨k - i.val, by omega⟩, by simp [i.isLt], by simp [i.isLt]⟩
  · simp [Finset.prod_sum_type]

/-- The kernel appearing in Lemma 4.3. -/
def lemma43Kernel (p n : ℕ) (C : ℝ) (d : ℕ) : ℝ :=
  chainFactor p n C d

/-- The summand in Lemma 4.3 for a single increasing k-tuple. -/
def lemma43Summand {k : ℕ} (p n : ℕ) (C : ℝ)
    (m : Fin k → ℕ) : ℝ :=
  chainUpperBound p n C m

/-- Full left side of Lemma 4.3. -/
def lemma43LHS (p n k : ℕ) (C : ℝ) : ℝ :=
  ∑ m ∈ chainSizeTuples n k, lemma43Summand p n C m

/-- Right side of Lemma 4.3. -/
def lemma43RHS (p n k : ℕ) (C : ℝ) : ℝ :=
  (k + 1 : ℝ) *
    ((n : ℝ) / p +
      2 * C * Real.sqrt (Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ)) ^ k

/-- Corollary 1.4 exactly. -/
def Corollary14Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : NeZero p := ⟨hp.ne_zero⟩
        ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
        ∀ (m : ℕ), 0 < m →
          (m : ℝ) ≤ (1 - ε) * S.card →
          ∀ z : ZMod p,
            sliceMass S m z ≤
              1 / (p : ℝ) +
                Cε * Real.sqrt (Real.log (S.card : ℝ)) /
                  ((S.card : ℝ) * Real.sqrt (m : ℝ))

/-- Corollary 4.2 exactly. -/
def Corollary42Statement : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : NeZero p := ⟨hp.ne_zero⟩
        ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
        ∀ (m : Fin k → ℕ), IsChainSizeTuple S.card m →
        ∀ z : Fin k → ZMod p,
          chainMass S m z ≤ chainUpperBound p S.card Ck m

/-- Lemma 4.3 exactly, expressed using the finite family of increasing tuples. -/
def Lemma43Statement : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∀ Ck : ℝ, 0 < Ck →
      ∀ (p : ℕ), p.Prime →
      ∀ n : ℕ, 2 ≤ n →
        lemma43LHS p n k Ck ≤ lemma43RHS p n k Ck

end

end GrahamRearrangement
