import Lean4Examples.GrahamRearrangement.Rearrangement.BadEvents

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Main theorem

Theorem 1.2 and the final reduction from the Section 5 bad-event estimates.
-/

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
