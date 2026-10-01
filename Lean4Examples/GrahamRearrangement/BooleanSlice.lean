import Lean4Examples.GrahamRearrangement.Preliminaries

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: Anticoncentration on Boolean slices
-/

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
  unfold sliceMass
  exact div_nonneg (by positivity) (by positivity)

theorem sliceMass_le_one {p : ℕ} (S : Finset (ZMod p))
    (m : ℕ) (z : ZMod p) :
    sliceMass S m z ≤ 1 := by
  unfold sliceMass
  by_cases hzero : (S.powersetCard m).card = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < (S.powersetCard m).card := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    exact (div_le_one hpos).2 (by
      exact_mod_cast
        (Finset.card_filter_le (S.powersetCard m) (fun R => subsetSum R = z)))

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

end GrahamRearrangement
