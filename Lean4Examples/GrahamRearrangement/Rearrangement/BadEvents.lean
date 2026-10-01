import Lean4Examples.GrahamRearrangement.Rearrangement.Definitions

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: Random orderings and bad-event bounds
-/

section UniformOrderings

/-- All indexed orderings of `S`; this is the finite sample space for Section 5. -/
noncomputable def indexedOrderings {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    Finset (Fin S.card → ZMod p) := by
  classical
  exact Finset.univ.filter fun σ => IsIndexedOrdering S σ

/-- Uniform mass of an event on indexed orderings of `S`. -/
noncomputable def orderingEventMass {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (E : (Fin S.card → ZMod p) → Prop) : ℝ := by
  classical
  let Ω := indexedOrderings S
  exact (Ω.filter E).card / Ω.card

/-- The combined probabilistic output of Lemmas 5.1--5.3 in the regime of
Theorem 1.2. The three constants are exactly `1/100`, `3/100`, and `1/25`. -/
def Section5BadEventBoundsStatement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : NeZero p := ⟨hp.ne_zero⟩
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

end GrahamRearrangement
