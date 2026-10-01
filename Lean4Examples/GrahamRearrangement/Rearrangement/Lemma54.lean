import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma51

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.4 and equation (5.1)
-/

noncomputable section

def exposedWindow {n : ℕ} (D : ℕ) (b : Fin n) : Finset (Fin n) :=
  forwardWindow b (20 * D)

theorem exposedWindow_card {n D : ℕ} (b : Fin n)
    (hfit : paperPos b + 20 * D ≤ n) :
    (exposedWindow D b).card = 20 * D + 1 := by
  unfold exposedWindow
  apply card_forwardWindow_eq
  simp [paperPos] at hfit ⊢
  omega

theorem collision_event_determined
    {n p : ℕ} {F J J' : Finset (Fin n)}
    (hJ : J ⊆ F) (hJ' : J' ⊆ F)
    {σ τ : Fin n → ZMod p}
    (hag : AgreesOn F σ τ) :
    (indexSetSum σ J = indexSetSum σ J') ↔
      (indexSetSum τ J = indexSetSum τ J') := by
  have hsumJ : indexSetSum σ J = indexSetSum τ J := by
    unfold indexSetSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hag i (hJ hi)
  have hsumJ' : indexSetSum σ J' = indexSetSum τ J' := by
    unfold indexSetSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hag i (hJ' hi)
  rw [hsumJ, hsumJ']

theorem conditional_badEndpoint_mass_le_four
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card)
    (hbfit : paperPos b + 30 * P.D ≤ S.card)
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingConditionalMass S
      (fun σ => AgreesOn (exposedWindow P.D b) σ τ)
      (fun σ => b ∈ badRightEndpoints σ) ≤
        4 * (S.card : ℝ) ^ (-α) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let F := exposedWindow P.D b
  let T := S \ indexImageSet τ F
  have hfit20 : paperPos b + 20 * P.D ≤ S.card := by omega
  have hFcard : F.card = 20 * P.D + 1 := by
    simpa [F] using exposedWindow_card (D := P.D) b hfit20
  have himage :
      (indexImageSet τ F).card = F.card :=
    Section5External.exposed_image_card S hτ F
  have hTcard :
      T.card = S.card - (20 * P.D + 1) := by
    unfold T
    rw [Finset.card_sdiff]
    · rw [himage, hFcard]
    · intro x hx
      simp [indexImageSet] at hx
      rcases hx with ⟨i, hiF, rfl⟩
      exact (hτ.2 _).2 ⟨i, rfl⟩
  have hhalf : S.card / 2 ≤ T.card := by
    rw [hTcard]
    have h50 := section5_card_ge_fiftyD hreg
    omega
  have hT2 : 2 ≤ T.card := by
    have hS2 := section5_card_ge_two hα0 hαh hreg
    have h50 := section5_card_ge_fiftyD hreg
    omega
  let A := leftEndpointCandidates b
  let I : Fin S.card → Finset (Fin S.card) :=
    fun a => indexHalfOpen a b
  let z : Fin S.card → ZMod p := fun _ => -τ b
  have hdisj : ∀ a ∈ A, Disjoint F (I a) := by
    intro a ha
    rw [Finset.disjoint_left]
    intro i hiF hiI
    simp only [F, exposedWindow, forwardWindow, Finset.mem_filter,
      Finset.mem_univ, true_and] at hiF
    simp only [I, indexHalfOpen, Finset.mem_filter, Finset.mem_univ,
      true_and] at hiI
    omega
  have hsubset :
      ∀ σ,
        AgreesOn F σ τ →
        b ∈ badRightEndpoints σ →
        ∃ a ∈ A, indexSetSum σ (I a) = z a := by
    intro σ hag hb
    rcases (mem_badRightEndpoints_iff σ b).1 hb with
      ⟨a, ha2, hab, hzero⟩
    refine ⟨a, by simp [A, leftEndpointCandidates, ha2, hab], ?_⟩
    have habv : a.val ≤ b.val := by
      simpa [paperPos] using le_of_lt hab
    have hsplit :=
      interval_sum_eq_halfOpen_add_endpoint σ a b habv
    have hbF : b ∈ F := by
      simp [F, exposedWindow, forwardWindow]
    have hsigma_b : σ b = τ b := hag b hbF
    unfold I z
    rw [hzero] at hsplit
    rw [hsigma_b] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  have hcond :
      orderingConditionalMass S
        (fun σ => AgreesOn F σ τ)
        (fun σ => b ∈ badRightEndpoints σ) ≤
      ∑ a ∈ A, sliceMass T (I a).card (z a) := by
    calc
      orderingConditionalMass S
          (fun σ => AgreesOn F σ τ)
          (fun σ => b ∈ badRightEndpoints σ)
        ≤ orderingConditionalMass S
            (fun σ => AgreesOn F σ τ)
            (fun σ => ∃ a ∈ A, indexSetSum σ (I a) = z a) := by
          apply uniformMass_mono
          intro σ hs hb
          exact hsubset σ (by simpa [orderingConditionalMass,
            uniformConditionalMass] using hs) hb
      _ ≤ ∑ a ∈ A, sliceMass T (I a).card (z a) := by
          exact Section5External.conditional_index_family_sumMass_le_zmod
            S τ hτ F A I z hdisj
  have hsum :
      (∑ a ∈ A, sliceMass T (I a).card (z a)) ≤
        2 * (T.card : ℝ) / p +
          4 * chainConstant 1 *
            Real.sqrt (Real.log (T.card : ℝ)) /
              Real.sqrt (T.card : ℝ) := by
    have hterm :
        ∀ a ∈ A,
          sliceMass T (I a).card (z a) ≤
            (1 / (p : ℝ) +
              chainConstant 1 *
                Real.sqrt (Real.log (T.card : ℝ)) /
                ((T.card : ℝ) * Real.sqrt ((I a).card : ℝ))) +
            (1 / (p : ℝ) +
              chainConstant 1 *
                Real.sqrt (Real.log (T.card : ℝ)) /
                ((T.card : ℝ) *
                  Real.sqrt ((T.card - (I a).card : ℕ) : ℝ))) := by
      intro a ha
      have ha' := (Finset.mem_filter.1 ha).2
      have habv : a.val < b.val := by
        simpa [A, leftEndpointCandidates, paperPos] using ha'.2
      have hcardI :
          (I a).card = b.val - a.val := by
        unfold I
        exact card_indexHalfOpen a b (Nat.le_of_lt habv)
      have hrpos : 0 < (I a).card := by
        rw [hcardI]
        omega
      have hrlt : (I a).card < T.card := by
        rw [hcardI, hTcard]
        have hbfit' : b.val + 30 * P.D < S.card := by
          simp [paperPos] at hbfit
          omega
        have ha2 : 1 ≤ a.val := by
          simpa [A, leftEndpointCandidates, paperPos] using ha'.1
        omega
      simpa using
        corollary42_one_bound hp T hT2 hrpos hrlt (z a)
    calc
      (∑ a ∈ A, sliceMass T (I a).card (z a))
        ≤ ∑ a ∈ A,
            ((1 / (p : ℝ) +
              chainConstant 1 *
                Real.sqrt (Real.log (T.card : ℝ)) /
                ((T.card : ℝ) * Real.sqrt ((I a).card : ℝ))) +
            (1 / (p : ℝ) +
              chainConstant 1 *
                Real.sqrt (Real.log (T.card : ℝ)) /
                ((T.card : ℝ) *
                  Real.sqrt ((T.card - (I a).card : ℕ) : ℝ)))) := by
            gcongr with a ha
            exact hterm a ha
      _ ≤ 2 * (T.card : ℝ) / p +
          4 * chainConstant 1 *
            Real.sqrt (Real.log (T.card : ℝ)) /
              Real.sqrt (T.card : ℝ) := by
            -- Reindex the half-open interval lengths and use the standard
            -- reciprocal-square-root sum estimate.
            exact External.two_sided_interval_kernel_sum_le
              T.card p (chainConstant 1)
  have hpBound := section5_card_over_p hα0 hαh hp hreg
  have hC := section5_chainConstant_bound hreg 1 (Or.inl rfl)
  have hcompare :
      2 * (T.card : ℝ) / p +
          4 * chainConstant 1 *
            Real.sqrt (Real.log (T.card : ℝ)) /
              Real.sqrt (T.card : ℝ)
        ≤ 4 * (S.card : ℝ) ^ (-α) := by
    have hTle : T.card ≤ S.card := Finset.card_sdiff_le _ _
    have hlog :
        Real.sqrt (Real.log (T.card : ℝ)) ≤
          Real.sqrt (Real.log (S.card : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Real.log_le_sub_one_of_pos
        (by positivity)
        |> le_trans ?_
    have hroot :
        Real.sqrt (S.card : ℝ) ≤
          2 * Real.sqrt (T.card : ℝ) := by
      have := Real.sqrt_le_sqrt (show (S.card : ℝ) ≤ 4 * T.card by
        exact_mod_cast (le_trans (Nat.le_mul_of_div_le_left hhalf (by omega))
          (by omega)))
      nlinarith
    have hpT : (T.card : ℝ) / p ≤ (S.card : ℝ) ^ (-α) := by
      have : (T.card : ℝ) / p ≤ (S.card : ℝ) / p := by gcongr
      exact le_trans this hpBound
    have hCT :
        4 * chainConstant 1 *
            Real.sqrt (Real.log (T.card : ℝ)) /
              Real.sqrt (T.card : ℝ)
          ≤ 2 * (S.card : ℝ) ^ (-α) := by
      have hnonneg :
          0 ≤ 4 * chainConstant 1 *
            Real.sqrt (Real.log (T.card : ℝ)) := by positivity
      have hden : 0 < Real.sqrt (T.card : ℝ) := by positivity
      have hdenS : 0 < Real.sqrt (S.card : ℝ) := by positivity
      have haux :
          4 * chainConstant 1 *
              Real.sqrt (Real.log (T.card : ℝ)) /
                Real.sqrt (T.card : ℝ)
            ≤ 2 *
              (4 * chainConstant 1 *
                Real.sqrt (Real.log (S.card : ℝ)) /
                  Real.sqrt (S.card : ℝ)) := by
        gcongr
      exact le_trans haux (by nlinarith [hC])
    nlinarith
  exact le_trans hcond (le_trans hsum hcompare)

/-- Equation (5.1). -/
theorem equation_5_1
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card)
    (hbfit : paperPos b + 30 * P.D ≤ S.card)
    (J J' : Finset (Fin S.card))
    (hJ : J ⊆ exposedWindow P.D b)
    (hJ' : J' ⊆ exposedWindow P.D b)
    (hne : J ≠ J') :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ =>
        b ∈ badRightEndpoints σ ∧
          indexSetSum σ J = indexSetSum σ J') ≤
      8 / (S.card : ℝ) ^ (1 + α) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let F := exposedWindow P.D b
  have hfit20 : paperPos b + 20 * P.D ≤ S.card := by omega
  have hFcard : F.card = 20 * P.D + 1 := by
    simpa [F] using exposedWindow_card (D := P.D) b hfit20
  have hcollision :
      orderingEventMass S
        (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
        2 / (S.card : ℝ) := by
    have hraw :=
      Section5External.distinct_index_subset_sums_mass_le
        S F J J' hJ hJ' hne (by
          rw [hFcard]
          have h50 := section5_card_ge_fiftyD hreg
          omega)
    have hn50 := section5_card_ge_fiftyD hreg
    rw [hFcard] at hraw
    calc
      orderingEventMass S
          (fun σ => indexSetSum σ J = indexSetSum σ J')
        ≤ 1 / ((S.card - (20 * P.D + 1) + 1 : ℕ) : ℝ) := hraw
      _ ≤ 2 / (S.card : ℝ) := by
        have hden :
            S.card / 2 ≤ S.card - (20 * P.D + 1) + 1 := by omega
        positivity
  have hdetermined :
      ∀ σ τ,
        AgreesOn F σ τ →
        ((indexSetSum σ J = indexSetSum σ J') ↔
          (indexSetSum τ J = indexSetSum τ J')) := by
    intro σ τ hag
    exact collision_event_determined hJ hJ' hag
  have hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        indexSetSum τ J = indexSetSum τ J' →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ)
          (fun σ => b ∈ badRightEndpoints σ) ≤
            4 * (S.card : ℝ) ^ (-α) := by
    intro τ hτ hcoll
    exact conditional_badEndpoint_mass_le_four
      hα0 hαh P hp S hreg b hbfit τ hτ
  have hjoint :=
    Section5External.joint_event_le_of_agreesOn_fibers
      S F
      (fun σ => indexSetSum σ J = indexSetSum σ J')
      (fun σ => b ∈ badRightEndpoints σ)
      (2 / (S.card : ℝ))
      (4 * (S.card : ℝ) ^ (-α))
      hcollision hdetermined hfiber
  have hnpos : 0 < (S.card : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt
      (section5_card_ge_two hα0 hαh hreg)
  calc
    orderingEventMass S
      (fun σ =>
        b ∈ badRightEndpoints σ ∧
          indexSetSum σ J = indexSetSum σ J')
      = orderingEventMass S
          (fun σ =>
            indexSetSum σ J = indexSetSum σ J' ∧
              b ∈ badRightEndpoints σ) := by
          congr 1
          funext σ
          tauto
    _ ≤ (2 / (S.card : ℝ)) *
          (4 * (S.card : ℝ) ^ (-α)) := hjoint
    _ = 8 / (S.card : ℝ) ^ (1 + α) := by
      rw [Real.rpow_add (le_of_lt hnpos)]
      rw [Real.rpow_one, Real.rpow_neg (le_of_lt hnpos)]
      field_simp
      ring

def bad0Parameters {n : ℕ} (D : ℕ) :
    Finset (Fin n × Finset (Fin n) × Finset (Fin n)) := by
  classical
  exact Finset.univ.biUnion fun b =>
    if hfit : paperPos b + 30 * D ≤ n then
      (forwardWindow b (20 * D)).powerset.biUnion fun J =>
        ((forwardWindow b (20 * D)).powerset.filter
          (fun J' => J ≠ J')).image fun J' => (b, J, J')
    else ∅

theorem mem_bad0Parameters {n D : ℕ}
    {b : Fin n} {J J' : Finset (Fin n)} :
    (b, J, J') ∈ bad0Parameters (n := n) D ↔
      paperPos b + 30 * D ≤ n ∧
      J ⊆ forwardWindow b (20 * D) ∧
      J' ⊆ forwardWindow b (20 * D) ∧ J ≠ J' := by
  classical
  by_cases hfit : paperPos b + 30 * D ≤ n
  · simp [bad0Parameters, hfit]
  · simp [bad0Parameters, hfit]

theorem bad0Parameters_card_le {n D : ℕ} :
    (bad0Parameters (n := n) D).card ≤ n * 2 ^ (40 * D + 2) := by
  classical
  calc
    (bad0Parameters (n := n) D).card
      ≤ ∑ b : Fin n,
          ((forwardWindow b (20 * D)).powerset.card *
            (forwardWindow b (20 * D)).powerset.card) := by
          unfold bad0Parameters
          apply Finset.card_biUnion_le_sum
          intro b hb
          split
          · apply le_trans (Finset.card_biUnion_le_sum _ _)
            (Finset.sum_le_sum fun J hJ => ?_)
            exact Finset.card_image_le
          · simp
    _ ≤ ∑ _b : Fin n, 2 ^ (40 * D + 2) := by
          gcongr with b
          rw [Finset.card_powerset, Finset.card_powerset]
          have hw := card_forwardWindow_le b (20 * D)
          have hp : 2 ^ (forwardWindow b (20 * D)).card ≤
              2 ^ (20 * D + 1) := Nat.pow_le_pow_right (by omega) hw
          calc
            2 ^ (forwardWindow b (20 * D)).card *
                2 ^ (forwardWindow b (20 * D)).card
              ≤ 2 ^ (20 * D + 1) * 2 ^ (20 * D + 1) :=
                Nat.mul_le_mul hp hp
            _ = 2 ^ (40 * D + 2) := by
                rw [← pow_add]
                congr
                omega
    _ = n * 2 ^ (40 * D + 2) := by simp [mul_comm]

/-- Lemma 5.4. -/
theorem lemma5_4
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent0 P.D) ≤ (1 / 100 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Θ := bad0Parameters (n := S.card) P.D
  let E :
      (Fin S.card × Finset (Fin S.card) × Finset (Fin S.card)) →
        (Fin S.card → ZMod p) → Prop :=
    fun θ σ =>
      θ.1 ∈ badRightEndpoints σ ∧
        indexSetSum σ θ.2.1 = indexSetSum σ θ.2.2
  have hcover :
      ∀ σ ∈ indexedOrderings S, BadEvent0 P.D σ →
        ∃ θ ∈ Θ, E θ σ := by
    intro σ hσ h0
    rcases h0 with
      ⟨b, hb, hbfit, J, J', hJ, hJ', hne, hsum⟩
    refine ⟨(b, J, J'), ?_, hb, hsum⟩
    simp [Θ, bad0Parameters, hJ, hJ', hne, hbfit]
  have hbound :
      ∀ θ ∈ Θ,
        orderingEventMass S (E θ) ≤
          8 / (S.card : ℝ) ^ (1 + α) := by
    intro θ hθ
    rcases θ with ⟨b, J, J'⟩
    have hθ' := (mem_bad0Parameters).1 hθ
    exact equation_5_1 hα0 hαh P hp S hreg
      b hθ'.1 J J' hθ'.2.1 hθ'.2.2.1 hθ'.2.2.2
  have hmass :
      orderingEventMass S (BadEvent0 P.D) ≤
        (Θ.card : ℝ) *
          (8 / (S.card : ℝ) ^ (1 + α)) := by
    unfold orderingEventMass
    exact Section5External.witness_union_bound
      (indexedOrderings S) Θ (BadEvent0 P.D) E
      (8 / (S.card : ℝ) ^ (1 + α))
      hcover (by simpa [orderingEventMass] using hbound)
  have hΘ :
      Θ.card ≤ S.card * 2 ^ (40 * P.D + 2) := by
    exact bad0Parameters_card_le (n := S.card) (D := P.D)
  calc
    orderingEventMass S (BadEvent0 P.D)
      ≤ (Θ.card : ℝ) *
          (8 / (S.card : ℝ) ^ (1 + α)) := hmass
    _ ≤ (S.card * 2 ^ (40 * P.D + 2) : ℕ) *
          (8 / (S.card : ℝ) ^ (1 + α)) := by
          gcongr
          exact_mod_cast hΘ
    _ = (2 : ℝ) ^ (40 * P.D + 5) /
          (S.card : ℝ) ^ α := by
          have hnpos : 0 < (S.card : ℝ) := by positivity
          rw [Real.rpow_add (le_of_lt hnpos), Real.rpow_one]
          field_simp
          ring_nf
          rw [pow_add]
          norm_num
    _ ≤ (1 / 100 : ℝ) := by
          have hpow := section5_Calpha_power hα0 P
          have hcard := hreg.2.1
          have hmono :=
            Real.rpow_le_rpow (le_of_lt P.Cα_pos) hcard (le_of_lt hα0)
          have hden :
              (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) ≤
                (S.card : ℝ) ^ α :=
            le_trans hpow hmono
          have hpos : 0 < (S.card : ℝ) ^ α := by positivity
          apply (div_le_iff₀ hpos).2
          rw [pow_add]
          norm_num
          nlinarith

end

end GrahamRearrangement
