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
