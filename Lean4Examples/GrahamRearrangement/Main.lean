import Lean4Examples.GrahamRearrangement.Rearrangement.BadEvents

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Main theorem

Theorem 1.2, including the paper's reduction to 0 < α < 1/2 and the final
probabilistic-existence/greedy-repair argument.
-/

noncomputable section

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

theorem exists_section5_good_ordering
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (h1 :
      orderingEventMass S (BadEvent1 D) ≤ (1 / 100 : ℝ))
    (h2 :
      orderingEventMass S (BadEvent2 D) ≤ (3 / 100 : ℝ))
    (h3 :
      orderingEventMass S (BadEvent3 D) ≤ (1 / 25 : ℝ)) :
    ∃ σ ∈ indexedOrderings S, Section5Good D σ := by
  have hspace :=
    Section5External.indexedOrderings_nonempty S
  have h :=
    Section5External.exists_avoiding_three_events
      (indexedOrderings S) hspace
      (BadEvent1 D) (BadEvent2 D) (BadEvent3 D)
      (1 / 100 : ℝ) (3 / 100 : ℝ) (1 / 25 : ℝ)
      (by simpa [orderingEventMass] using h1)
      (by simpa [orderingEventMass] using h2)
      (by simpa [orderingEventMass] using h3)
      (by norm_num)
  rcases h with ⟨σ, hσ, hnot1, hnot2, hnot3⟩
  exact ⟨σ, hσ, hnot1, hnot2, hnot3⟩

/-- The final Section 5 reduction from the three probability bounds to a valid
ordering. -/
theorem theorem12_of_section5_bounds
    (hbad : Section5BadEventBoundsStatement) :
    Theorem12Statement := by
  intro α hα0 hα1
  let β : ℝ := min α (1 / 4)
  have hβ0 : 0 < β := by
    dsimp [β]
    exact lt_min hα0 (by norm_num)
  have hβh : β < 1 / 2 := by
    exact lt_of_le_of_lt (min_le_right α (1 / 4 : ℝ)) (by norm_num)
  have hβα : β ≤ α := by
    exact min_le_left α (1 / 4 : ℝ)
  rcases hbad β hβ0 hβh with
    ⟨Cβ, hCβ, hbounds⟩
  refine ⟨Cβ, hCβ, ?_⟩
  intro p hp S hzero hC hsize
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpone : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hexp : 1 - α ≤ 1 - β := by
    linarith
  have hpow :
      (p : ℝ) ^ (1 - α) ≤ (p : ℝ) ^ (1 - β) :=
    External.rpow_exponent_mono_of_one_le hpone hexp
  have hsizeβ :
      (S.card : ℝ) ≤ (p : ℝ) ^ (1 - β) :=
    le_trans hsize hpow
  have hb :=
    hbounds p hp S hzero hC hsizeβ
  let D := Nat.ceil (3 / β)
  have hDpos : 0 < D := by
    have :=
      section5D_pos hβ0 hβh
    simpa [D, section5D] using this
  have hb1 :
      orderingEventMass S (BadEvent1 D) ≤ (1 / 100 : ℝ) := by
    simpa [D] using hb.1
  have hb2 :
      orderingEventMass S (BadEvent2 D) ≤ (3 / 100 : ℝ) := by
    simpa [D] using hb.2.1
  have hb3 :
      orderingEventMass S (BadEvent3 D) ≤ (1 / 25 : ℝ) := by
    simpa [D] using hb.2.2
  obtain ⟨σ, hσmem, hgood⟩ :=
    exists_section5_good_ordering S hb1 hb2 hb3
  have hσ : IsIndexedOrdering S σ := by
    simpa [indexedOrderings] using
      (Finset.mem_filter.1 hσmem).2
  obtain ⟨π, hπadm, hnozero⟩ :=
    section5_local_repair hDpos σ hgood
  have hσ' :
      IsIndexedOrdering S (applyPositionPerm σ π) :=
    applyPositionPerm_isIndexedOrdering hσ π
  have hvalid :
      IsValidOrdering S
        (indexedToList (applyPositionPerm σ π)) :=
    (valid_iff_noZeroPaperSegments hzero hσ').2 hnozero
  exact ⟨indexedToList (applyPositionPerm σ π), hvalid⟩

/-- Theorem 1.2 of Pham--Sauermann. -/
theorem theorem12 : Theorem12Statement :=
  theorem12_of_section5_bounds section5_bad_event_bounds

end

end GrahamRearrangement
