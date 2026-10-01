import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma52

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.5
-/

noncomputable section

theorem card_interestingLeftSupport_le
    {n D : ℕ} (hD : 7 ≤ D)
    (b : Fin n) (x : Fin D → Fin n) :
    (interestingLeftSupport b x).card ≤ 7 * D ^ 2 := by
  unfold interestingLeftSupport
  calc
    _ ≤ (symmetricWindow b (5 * D)).card +
        ∑ i : Fin D, (backwardWindow (x i) (5 * D)).card := by
          exact Finset.card_union_biUnion_le
    _ ≤ (10 * D + 1) + D * (5 * D) := by
          gcongr
          · simpa [mul_assoc] using card_symmetricWindow_le b (5 * D)
          · calc
              ∑ i : Fin D, (backwardWindow (x i) (5 * D)).card
                ≤ ∑ _i : Fin D, 5 * D := by
                    gcongr with i
                    exact card_backwardWindow_le (x i) (5 * D)
              _ = D * (5 * D) := by simp
    _ ≤ 7 * D ^ 2 := by omega

theorem permuted_interval_sum_eq
    {n p : ℕ} (σ : Fin n → ZMod p)
    (π ρ : Equiv.Perm (Fin n)) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum
        (applyPositionPerm (applyPositionPerm σ π) ρ) a b =
      indexSetSum σ
        ((indexInterval a b).image ρ |>.image π) := by
  rw [← indexSetSum_indexInterval]
  unfold indexSetSum applyPositionPerm
  rw [Finset.sum_image]
  · rw [Finset.sum_image]
    · rfl
    · intro i hi j hj h
      exact ρ.injective h
  · intro i hi j hj h
    exact π.injective h

theorem lemma55_reduce_to_interesting
    {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hπ :
      ∃ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π ∧
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π) (πi i))
            (u i) (x i) = 0) :
    ∃ π ∈ interestingPermutations D
        (fun i => constraintSet u x πi i),
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (πi i))
          (u i) (x i) = 0 := by
  classical
  rcases hπ with ⟨π, ⟨P, hPadm, hPπ⟩, hzero⟩
  let I : Fin D → Finset (Fin n) :=
    fun i => constraintSet u x πi i
  obtain ⟨P', hPsub, hP'disj, hcross, himage⟩ :=
    Section5External.trim_irrelevant_disjoint_swaps P
      hPadm.1 I
  let π' := collectionPerm P'
  refine ⟨π', ?_, ?_⟩
  · simp only [interestingPermutations, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨P', ?_, rfl, hcross⟩
    constructor
    · exact hP'disj
    · intro q hq
      exact hPadm.2 q (hPsub hq)
  · intro i
    have hab : (u i).val ≤ (x i).val := by
      by_cases h : (u i).val ≤ (x i).val
      · exact h
      · have := hzero i
        simp [indexedIntervalSum, Nat.not_le.mp h] at this
    rw [permuted_interval_sum_eq σ π' (πi i) (u i) (x i) hab]
    rw [permuted_interval_sum_eq σ π (πi i) (u i) (x i) hab] at hzero
    simpa [I, constraintSet, π'] using
      congrArg (indexSetSum σ) (himage i) ▸ hzero i

theorem interesting_left_support
    {n D : ℕ}
    (hD : 0 < D)
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    {π : Equiv.Perm (Fin n)}
    (hπ : π ∈ interestingPermutations D
      (fun i => constraintSet u x πi i)) :
    ∃ P : Finset (Fin n × Fin n),
      IsAdmissibleCollection D P ∧
      collectionPerm P = π ∧
      ∀ q ∈ P, q.1 ∈ interestingLeftSupport b x := by
  classical
  rcases (Finset.mem_filter.1 hπ).2 with
    ⟨P, hPadm, hPπ, hcross⟩
  refine ⟨P, hPadm, hPπ, ?_⟩
  intro q hq
  rcases hcross q hq with ⟨i, hi⟩
  have hlen := hPadm.2 q hq
  by_cases hlocal :
      q.1 ∈ symmetricWindow b (5 * D)
  · exact Finset.mem_union_left _ hlocal
  · have htail :
        q.1 ∈ backwardWindow (x i) (5 * D) := by
      -- If q does not start near [b,b'], crossing πᵢ([uᵢ,xᵢ])
      -- can only occur at its right endpoint xᵢ, because πᵢ fixes
      -- positions outside the exposed window.
      exact Section5External.interesting_crossing_forces_tail_start
        hD b b' hgap u x πi hu hfix q i hlen hi hlocal
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ i, htail⟩)

theorem interestingPermutations_card_le
    {n D : ℕ}
    (hD7 : 7 ≤ D)
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i)) :
    (interestingPermutations D
      (fun i => constraintSet u x πi i)).card ≤
        D ^ (14 * D ^ 2) := by
  apply Section5External.interestingPermutations_card_le_of_left_support
    hD7 (fun i => constraintSet u x πi i)
      (interestingLeftSupport b x)
  · exact card_interestingLeftSupport_le hD7 b x
  · intro π hπ
    exact interesting_left_support
      (by omega) b b' hgap u x hu πi hfix hπ

theorem lemma55_fixed_x_pi_mass_le
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b b' : Fin S.card)
    (hgap : paperPos b' - paperPos b = 5 * P.D)
    (u x : Fin P.D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hx : x ∈ tailTuples b' P.D)
    (πi : Fin P.D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (π : Equiv.Perm (Fin S.card)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π) (πi i))
            (u i) (x i) = 0) ≤
      chainUpperBound p (S.card - (5 * P.D + 1))
        (chainConstant P.D) (tailSizes b' x) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let F := indexInterval b b'
  have hbb' : b.val ≤ b'.val := by
    simpa [paperPos] using Nat.le_of_sub_eq (by omega) hgap
  have hFcard : F.card = 5 * P.D + 1 := by
    rw [show F.card = b'.val - b.val + 1 by
      exact card_indexInterval b b' hbb']
    simpa [paperPos] using congrArg (fun t => t + 1) hgap
  have hinv :=
    Section5External.ordering_perm_invariant
      S π
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm σ (πi i)) (u i) (x i) = 0)
  rw [hinv]
  apply Section5External.event_le_of_agreesOn_fibers
    S F
    (fun σ =>
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm σ (πi i)) (u i) (x i) = 0)
  intro τ hτ
  let T := S \ indexImageSet τ F
  have himage :=
    Section5External.exposed_image_card S hτ F
  have hTcard :
      T.card = S.card - (5 * P.D + 1) := by
    unfold T
    rw [Finset.card_sdiff]
    · rw [himage, hFcard]
    · intro z hz
      simp [indexImageSet] at hz
      rcases hz with ⟨i, hi, rfl⟩
      exact (hτ.2 _).2 ⟨i, rfl⟩
  have hT2 : 2 ≤ T.card := by
    rw [hTcard]
    have h50 := section5_card_ge_fiftyD hreg
    omega
  have hD := section5Parameters_D_pos hα0 hαh P
  have htuple : IsChainSizeTuple T.card (tailSizes b' x) := by
    exact Section5External.tailSizes_valid
      b b' hgap x hx hTcard
  have hchain :
      ∀ z : Fin P.D → ZMod p,
        chainMass T (tailSizes b' x) z ≤
          chainUpperBound p T.card (chainConstant P.D)
            (tailSizes b' x) := by
    intro z
    exact chainConstant_spec P.D hD p hp T hT2
      (tailSizes b' x) htuple z
  simpa [T, hTcard] using
    Section5External.fixed_tail_tuple_conditional_chainBound
      S τ hτ F b b' u x πi hu hfix
      (chainConstant P.D) htuple hchain

/-- Lemma 5.5. -/
theorem lemma5_5
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b b' : Fin S.card)
    (hb2 : 2 ≤ paperPos b)
    (hb' : paperPos b' ≤ S.card - 2)
    (hgap : paperPos b' - paperPos b = 5 * P.D)
    (u : Fin P.D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin P.D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ => Lemma55Event σ b b' u πi) ≤
        1 / (S.card : ℝ) ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hD7 : 7 ≤ P.D := by
    rw [P.D_eq]
    exact section5D_ge_seven hα0 hαh
  have hD := section5Parameters_D_pos hα0 hαh P
  let X := tailTuples b' P.D
  let choices :
      (Fin P.D → Fin S.card) →
        Finset (Equiv.Perm (Fin S.card)) :=
    fun x => interestingPermutations P.D
      (fun i => constraintSet u x πi i)
  let weight : (Fin P.D → Fin S.card) → ℝ :=
    fun x =>
      chainUpperBound p (S.card - (5 * P.D + 1))
        (chainConstant P.D) (tailSizes b' x)
  have hcover :
      ∀ σ ∈ indexedOrderings S, Lemma55Event σ b b' u πi →
        ∃ x ∈ X, ∃ π ∈ choices x,
          ∀ i,
            indexedIntervalSum
              (applyPositionPerm
                (applyPositionPerm σ π) (πi i))
              (u i) (x i) = 0 := by
    intro σ hσ h
    rcases h with ⟨x, hx, π, hπ, hz⟩
    obtain ⟨π', hπ', hz'⟩ :=
      lemma55_reduce_to_interesting σ b b' u x πi
        ⟨π, hπ, hz⟩
    exact ⟨x, hx, π', hπ', hz'⟩
  have hcount :
      ∀ x ∈ X, (choices x).card ≤
        P.D ^ (14 * P.D ^ 2) := by
    intro x hx
    exact interestingPermutations_card_le
      hD7 b b' hgap u x hu πi hfix
  have hpoint :
      ∀ x ∈ X, ∀ π ∈ choices x,
        orderingEventMass S
          (fun σ =>
            ∀ i,
              indexedIntervalSum
                (applyPositionPerm
                  (applyPositionPerm σ π) (πi i))
                (u i) (x i) = 0) ≤ weight x := by
    intro x hx π hπ
    exact lemma55_fixed_x_pi_mass_le
      hα0 hαh P hp S hreg b b' hgap
      u x hu hx πi hfix π
  let s := S.card - (5 * P.D + 1)
  have hsum :
      (∑ x ∈ X, weight x) ≤
        lemma43LHS p s P.D (chainConstant P.D) := by
    apply Section5External.chainUpperBound_sum_le_lemma43
      (chainConstant P.D) X (fun x => tailSizes b' x)
    · intro x hx
      exact Section5External.tailSizes_valid
        b b' hgap x hx rfl
    · intro x hx y hy hxy
      funext i
      have := congrFun hxy i
      unfold tailSizes at this
      apply Fin.ext
      omega
  have hw : ∀ x ∈ X, 0 ≤ weight x := by
    intro x hx
    unfold weight chainUpperBound
    positivity
  have hunion :
      orderingEventMass S
        (fun σ => Lemma55Event σ b b' u πi) ≤
        (P.D ^ (14 * P.D ^ 2) : ℝ) *
          lemma43LHS p s P.D (chainConstant P.D) := by
    unfold orderingEventMass
    exact Section5External.bounded_choice_witness_union
      (indexedOrderings S) X choices
      (fun σ => Lemma55Event σ b b' u πi)
      (fun x π σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π) (πi i))
            (u i) (x i) = 0)
      (P.D ^ (14 * P.D ^ 2)) weight
      (lemma43LHS p s P.D (chainConstant P.D))
      hcover hcount
      (by simpa [orderingEventMass] using hpoint)
      hsum hw
  have hs2 : 2 ≤ s := by
    unfold s
    have h50 := section5_card_ge_fiftyD hreg
    omega
  have h43 :=
    lemma4_3 P.D hD (chainConstant P.D)
      (chainConstant_pos P.D) p hp s hs2
  have hhalf : S.card / 2 ≤ s := by
    unfold s
    have h50 := section5_card_ge_fiftyD hreg
    omega
  have hbase :
      lemma43Base p s (chainConstant P.D) ≤
        2 * (S.card : ℝ) ^ (-α) := by
    apply Section5External.half_ground_lemma43Base_le
    · exact section5_card_ge_two hα0 hαh hreg
    · exact hhalf
    · omega
    · exact section5_card_over_p hα0 hαh hp hreg
    · exact section5_chainConstant_bound hreg P.D (Or.inr rfl)
  have hpow :=
    Section5External.two_neg_alpha_pow_le_cube
      (n := S.card) (D := P.D) (α := α)
      (by omega) hα0
      (section5Parameters_alphaD hα0 P)
  calc
    orderingEventMass S
        (fun σ => Lemma55Event σ b b' u πi)
      ≤ (P.D ^ (14 * P.D ^ 2) : ℝ) *
          lemma43LHS p s P.D (chainConstant P.D) := hunion
    _ ≤ (P.D ^ (14 * P.D ^ 2) : ℝ) *
          lemma43RHS p s P.D (chainConstant P.D) := by
          gcongr
    _ = (P.D ^ (14 * P.D ^ 2) : ℝ) *
        (P.D + 1 : ℝ) *
        (lemma43Base p s (chainConstant P.D)) ^ P.D := by rfl
    _ ≤ (P.D ^ (14 * P.D ^ 2) : ℝ) *
        (P.D + 1 : ℝ) *
        (2 * (S.card : ℝ) ^ (-α)) ^ P.D := by
          gcongr
    _ ≤ (P.D ^ (14 * P.D ^ 2) : ℝ) *
        (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
          (S.card : ℝ) ^ 3 := by
          nlinarith
    _ ≤ 1 / (S.card : ℝ) ^ 2 := by
          have hC := P.Cα_second
          have hnC := hreg.2.1
          have hnpos : 0 < (S.card : ℝ) := by positivity
          apply (div_le_iff₀ (pow_pos hnpos 3)).2
          nlinarith

end

end GrahamRearrangement
