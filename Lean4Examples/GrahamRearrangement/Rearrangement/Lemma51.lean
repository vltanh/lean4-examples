import Lean4Examples.GrahamRearrangement.Rearrangement.External

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.1
-/

noncomputable section

def leftEndpointCandidates {n : ℕ} (b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun a =>
    2 ≤ paperPos a ∧ paperPos a < paperPos b

def nearRightEnd {n : ℕ} (D : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun b => n ≤ paperPos b + 30 * D

theorem badEndpoint_event_subset {n p : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n) :
    b ∈ badRightEndpoints σ →
      ∃ a ∈ leftEndpointCandidates b,
        indexedIntervalSum σ a b = 0 := by
  intro hb
  rcases (mem_badRightEndpoints_iff σ b).1 hb with ⟨a, ha2, hab, hsum⟩
  exact ⟨a, by simp [leftEndpointCandidates, ha2, hab], hsum⟩

theorem fixed_interval_sum_mass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (a b : Fin S.card) (hab : a.val ≤ b.val) :
    orderingEventMass S (fun σ => indexedIntervalSum σ a b = 0) =
      sliceMass S (b.val - a.val + 1) 0 := by
  have h :=
    Section5External.fixedIndexSet_sumMass S (indexInterval a b) (0 : ZMod p)
  rw [card_indexInterval a b hab] at h
  apply Eq.trans _ h
  apply uniformMass_congr
  intro σ hσ
  rw [← indexSetSum_indexInterval]
  rfl

theorem endpoint_cor42_sum_bound {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card) :
    ∑ a ∈ leftEndpointCandidates b,
      ((1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((b.val - a.val + 1 : ℕ) : ℝ))) +
       (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((S.card - (b.val - a.val + 1) : ℕ) : ℝ)))) ≤
      2 * (S.card : ℝ) / p +
        4 * chainConstant 1 *
          Real.sqrt (Real.log (S.card : ℝ)) /
            Real.sqrt (S.card : ℝ) := by
  have hS : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  have hcount : (leftEndpointCandidates b).card ≤ S.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hfirst :
      ∑ a ∈ leftEndpointCandidates b,
        1 / Real.sqrt ((b.val - a.val + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt (S.card : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.Icc 1 S.card, 1 / Real.sqrt (i : ℝ) := by
        apply Finset.sum_le_sum_of_injOn
          (f := fun a : Fin S.card => b.val - a.val + 1)
        · intro a ha
          have hab := (Finset.mem_filter.1 ha).2.2
          have ha2 := (Finset.mem_filter.1 ha).2.1
          simp only [paperPos] at hab ha2
          exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
        · intro a ha a' ha' heq
          apply Fin.ext
          omega
        · intro a ha
          rfl
        · intro i hi hnot
          positivity
      _ ≤ 2 * Real.sqrt (S.card : ℝ) :=
        External.sum_inv_sqrt_le_two_sqrt S.card
  have hsecond :
      ∑ a ∈ leftEndpointCandidates b,
        1 / Real.sqrt ((S.card - (b.val - a.val + 1) : ℕ) : ℝ) ≤
        2 * Real.sqrt (S.card : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.Icc 1 S.card, 1 / Real.sqrt (i : ℝ) := by
        apply Finset.sum_le_sum_of_injOn
          (f := fun a : Fin S.card =>
            S.card - (b.val - a.val + 1))
        · intro a ha
          have hab := (Finset.mem_filter.1 ha).2.2
          have ha2 := (Finset.mem_filter.1 ha).2.1
          simp only [paperPos] at hab ha2
          exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
        · intro a ha a' ha' heq
          apply Fin.ext
          omega
        · intro a ha
          rfl
        · intro i hi hnot
          positivity
      _ ≤ 2 * Real.sqrt (S.card : ℝ) :=
        External.sum_inv_sqrt_le_two_sqrt S.card
  have hSroot : 0 < Real.sqrt (S.card : ℝ) := by
    positivity
  have hSsq : (Real.sqrt (S.card : ℝ)) ^ 2 = S.card := by
    rw [Real.sq_sqrt]
    positivity
  calc
    _ = 2 * ((leftEndpointCandidates b).card : ℝ) / p +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
            (S.card : ℝ) *
          (∑ a ∈ leftEndpointCandidates b,
            1 / Real.sqrt ((b.val - a.val + 1 : ℕ) : ℝ)) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
            (S.card : ℝ) *
          (∑ a ∈ leftEndpointCandidates b,
            1 / Real.sqrt
              ((S.card - (b.val - a.val + 1) : ℕ) : ℝ)) := by
          ring
    _ ≤ 2 * (S.card : ℝ) / p +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
            (S.card : ℝ) * (2 * Real.sqrt (S.card : ℝ)) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
            (S.card : ℝ) * (2 * Real.sqrt (S.card : ℝ)) := by
          gcongr
          exact_mod_cast hcount
    _ = 2 * (S.card : ℝ) / p +
        4 * chainConstant 1 *
          Real.sqrt (Real.log (S.card : ℝ)) /
            Real.sqrt (S.card : ℝ) := by
          field_simp
          nlinarith

theorem fixed_badEndpoint_mass_le_three {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (fun σ => b ∈ badRightEndpoints σ) ≤
      3 * (S.card : ℝ) ^ (-α) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hS : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  calc
    orderingEventMass S (fun σ => b ∈ badRightEndpoints σ)
      ≤ ∑ a ∈ leftEndpointCandidates b,
          orderingEventMass S
            (fun σ => indexedIntervalSum σ a b = 0) := by
          exact External.finite_union_bound
            (indexedOrderings S) (leftEndpointCandidates b)
              (fun a σ => indexedIntervalSum σ a b = 0)
          |>.trans' (uniformMass_mono _ _ _ (by
            intro σ hb
            exact badEndpoint_event_subset σ b hb))
    _ = ∑ a ∈ leftEndpointCandidates b,
        sliceMass S (b.val - a.val + 1) 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          have hab : a.val ≤ b.val := by
            have := (Finset.mem_filter.1 ha).2.2
            simpa [paperPos] using le_of_lt this
          exact fixed_interval_sum_mass S a b hab
    _ ≤ ∑ a ∈ leftEndpointCandidates b,
      ((1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((b.val - a.val + 1 : ℕ) : ℝ))) +
       (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((S.card - (b.val - a.val + 1) : ℕ) : ℝ)))) := by
          gcongr with a ha
          have hab := (Finset.mem_filter.1 ha).2.2
          have ha2 := (Finset.mem_filter.1 ha).2.1
          have hr : 0 < b.val - a.val + 1 := by omega
          have hrS : b.val - a.val + 1 < S.card := by
            have ha1 : 1 ≤ a.val := by simpa [paperPos] using ha2
            omega
          exact corollary42_one_bound hp S hS hr hrS 0
    _ ≤ 2 * (S.card : ℝ) / p +
        4 * chainConstant 1 *
          Real.sqrt (Real.log (S.card : ℝ)) /
            Real.sqrt (S.card : ℝ) :=
          endpoint_cor42_sum_bound hα0 hαh P hp S hreg b
    _ ≤ 3 * (S.card : ℝ) ^ (-α) := by
          have hpBound := section5_card_over_p hα0 hαh hp hreg
          have hC :=
            section5_chainConstant_bound hreg 1 (Or.inl rfl)
          nlinarith

/-- Lemma 5.1. -/
theorem lemma5_1 {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent1 P.D) ≤ 1 / 100 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hsubset : ∀ σ, BadEvent1 P.D σ →
      ∃ b ∈ nearRightEnd P.D, b ∈ badRightEndpoints σ := by
    intro σ h
    rcases h with ⟨b, hb, hnear⟩
    exact ⟨b, by simp [nearRightEnd, hnear], hb⟩
  calc
    orderingEventMass S (BadEvent1 P.D)
      ≤ orderingEventMass S
          (fun σ => ∃ b ∈ nearRightEnd P.D,
            b ∈ badRightEndpoints σ) :=
        uniformMass_mono _ _ _ hsubset
    _ ≤ ∑ b ∈ nearRightEnd P.D,
          orderingEventMass S (fun σ => b ∈ badRightEndpoints σ) := by
          exact External.finite_union_bound
            (indexedOrderings S) (nearRightEnd P.D)
              (fun b σ => b ∈ badRightEndpoints σ)
    _ ≤ ∑ _b ∈ nearRightEnd P.D,
          3 * (S.card : ℝ) ^ (-α) := by
          gcongr with b hb
          exact fixed_badEndpoint_mass_le_three hα0 hαh P hp S hreg b
    _ = ((nearRightEnd P.D).card : ℝ) *
          (3 * (S.card : ℝ) ^ (-α)) := by simp [mul_comm]
    _ ≤ (30 * P.D + 1 : ℝ) *
          (3 * (S.card : ℝ) ^ (-α)) := by
          gcongr
          exact_mod_cast
            (show (nearRightEnd (n := S.card) P.D).card ≤ 30 * P.D + 1 by
              unfold nearRightEnd
              exact card_near_right_end_le _ _)
    _ ≤ 1 / 100 := by
          have hpow := section5_Calpha_power hα0 P
          have hcard := hreg.2.1
          have hDpos := section5Parameters_D_pos hα0 hαh P
          have hnum :
              (30 * P.D + 1 : ℝ) * 3 ≤ 100 * P.D := by
            nlinarith
          have hlarge :
              100 * P.D ≤ (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) := by
            have : (1 : ℝ) ≤ (2 : ℝ) ^ (40 * P.D) := by positivity
            nlinarith
          have hpowercard :
              (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) ≤
                (S.card : ℝ) ^ α := by
            have hmono :=
              Real.rpow_le_rpow (by positivity) hcard (le_of_lt hα0)
            exact le_trans hpow hmono
          have hcardpos : 0 < (S.card : ℝ) := by positivity
          rw [show (S.card : ℝ) ^ (-α) =
            1 / (S.card : ℝ) ^ α by
              rw [Real.rpow_neg (le_of_lt hcardpos)]]
          apply (div_le_iff₀ (Real.rpow_pos_of_pos hcardpos α)).2
          nlinarith

end

end GrahamRearrangement
