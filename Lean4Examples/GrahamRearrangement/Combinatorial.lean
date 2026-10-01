import Lean4Examples.GrahamRearrangement.BooleanSlice

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 4: Combinatorial anticoncentration deductions
-/

section Chains

/-- All nested chains `R₀ ⊆ ... ⊆ Rₖ₋₁ ⊆ S` with prescribed sizes. -/
noncomputable def chainFamily {p k : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : Fin k → ℕ) : Finset (Fin k → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter fun R =>
    (∀ i, R i ⊆ S ∧ (R i).card = m i) ∧
      ∀ i j, i ≤ j → R i ⊆ R j

/-- Probability mass of prescribed sums along a uniformly random nested chain. -/
noncomputable def chainMass {p k : ℕ} [NeZero p] (S : Finset (ZMod p))
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
      ∀ (p : ℕ) (hp : p.Prime),
        letI : NeZero p := ⟨hp.ne_zero⟩
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

end GrahamRearrangement
