import Lean4Examples.GrahamRearrangement.Rearrangement.Repair

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5 bad-event bounds

Assembly of Lemmas 5.1, 5.2, and 5.3 with the Section 5 choice of parameters.
-/

noncomputable section

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
          orderingEventMass S (BadEvent1 D) ≤ (1 / 100 : ℝ) ∧
          orderingEventMass S (BadEvent2 D) ≤ (3 / 100 : ℝ) ∧
          orderingEventMass S (BadEvent3 D) ≤ (1 / 25 : ℝ)

/-- Lemmas 5.1--5.3 with their exact quantitative constants. -/
theorem section5_bad_event_bounds :
    Section5BadEventBoundsStatement := by
  intro α hα0 hαh
  obtain ⟨P, _⟩ :=
    exists_section5Parameters hα0 hαh
  refine ⟨P.Cα, P.Cα_pos, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hzero hC hupper
  have hreg : Section5Regime P p S :=
    ⟨hzero, hC, hupper⟩
  have h1 := lemma5_1 hα0 hαh P hp S hreg
  have h2 := lemma5_2 hα0 hαh P hp S hreg
  have h3 := lemma5_3 hα0 hαh P hp S hreg
  have hD : P.D = Nat.ceil (3 / α) := by
    simpa [section5D] using P.D_eq
  simpa [hD] using And.intro h1 (And.intro h2 h3)

end

end GrahamRearrangement
