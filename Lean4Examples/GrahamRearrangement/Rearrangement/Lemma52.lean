import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma54

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.2
-/

noncomputable section

def Lemma52Witness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b₀ : Fin n)
    (b : Fin D → Fin n) : Prop :=
  (∀ i, paperPos b₀ < paperPos (b i) ∧
    paperPos (b i) ≤ paperPos b₀ + 20 * D) ∧
  ∃ a : Fin D → Fin n,
    StrictMono a ∧
    (∀ i, paperPos (a i) < paperPos b₀) ∧
    ∀ i, indexedIntervalSum σ (a i) (b i) = 0

def lemma52Parameters (n D : ℕ) :
    Finset (Fin n × (Fin D → Fin n)) :=
  Finset.univ.filter fun θ =>
    paperPos θ.1 + 30 * D ≤ n ∧
      ∀ i, paperPos θ.1 < paperPos (θ.2 i) ∧
        paperPos (θ.2 i) ≤ paperPos θ.1 + 20 * D

theorem badEvent2_core_has_witness
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h2 : BadEvent2 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    ∃ θ ∈ lemma52Parameters n D,
      θ.1 ∈ badRightEndpoints σ ∧
      Lemma52Witness σ θ.1 θ.2 := by
  classical
  obtain ⟨b₀, hb₀, b, hbinj, hbmem, hbwin⟩ :=
    Section5External.dense_window_extract
      (badRightEndpoints σ) hD h2
  have hb₀fit : paperPos b₀ + 30 * D ≤ n := by
    by_contra h
    have hlate : n ≤ paperPos b₀ + 30 * D := by omega
    exact h1 ⟨b₀, hb₀, hlate⟩
  choose a ha2 hab hzero using
    fun i => (mem_badRightEndpoints_iff σ (b i)).1 (hbmem i)
  have hainj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hbij : b i ≠ b j := hbinj hne
    have hor : (b i).val < (b j).val ∨ (b j).val < (b i).val := by
      omega
    rcases hor with hlt | hlt
    · let c : Fin n := ⟨(b i).val + 1, by omega⟩
      let J := indexInterval c (b j)
      have hJsub : J ⊆ forwardWindow b₀ (20 * D) := by
        intro x hx
        simp only [J, indexInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx
        simp only [forwardWindow, Finset.mem_filter,
          Finset.mem_univ, true_and]
        have hwi := hbwin i
        have hwj := hbwin j
        simp [paperPos] at hwi hwj
        omega
      have hJsum : indexSetSum σ J = 0 := by
        rw [indexSetSum_indexInterval]
        have hzi :=
          (indexed_interval_zero_iff_prefix_eq σ (a i) (b i)
            (by simpa [paperPos] using le_of_lt (hab i))).1 (hzero i)
        have hzj :=
          (indexed_interval_zero_iff_prefix_eq σ (a j) (b j)
            (by simpa [paperPos] using le_of_lt (hab j))).1 (hzero j)
        have hpref :
            listPrefixSum (indexedToList σ) ((b i).val + 1) =
              listPrefixSum (indexedToList σ) ((b j).val + 1) := by
          rw [← hzi, ← hzj, hij]
        exact (indexed_interval_zero_iff_prefix_eq σ c (b j)
          (by dsimp [c]; omega)).2 (by simpa [c] using hpref)
      have hJne : J ≠ ∅ := by
        intro h
        have : c ∈ J := by
          simp [J, indexInterval, c, hlt]
        simpa [h] using this
      exact h0 ⟨b₀, hb₀, hb₀fit, J, ∅, hJsub,
        by simp, hJne, by simpa [hJsum]⟩
    · let c : Fin n := ⟨(b j).val + 1, by omega⟩
      let J := indexInterval c (b i)
      have hJsub : J ⊆ forwardWindow b₀ (20 * D) := by
        intro x hx
        simp only [J, indexInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx
        simp only [forwardWindow, Finset.mem_filter,
          Finset.mem_univ, true_and]
        have hwi := hbwin i
        have hwj := hbwin j
        simp [paperPos] at hwi hwj
        omega
      have hJsum : indexSetSum σ J = 0 := by
        rw [indexSetSum_indexInterval]
        have hzi :=
          (indexed_interval_zero_iff_prefix_eq σ (a i) (b i)
            (by simpa [paperPos] using le_of_lt (hab i))).1 (hzero i)
        have hzj :=
          (indexed_interval_zero_iff_prefix_eq σ (a j) (b j)
            (by simpa [paperPos] using le_of_lt (hab j))).1 (hzero j)
        have hpref :
            listPrefixSum (indexedToList σ) ((b j).val + 1) =
              listPrefixSum (indexedToList σ) ((b i).val + 1) := by
          rw [← hzj, ← hzi, hij]
        exact (indexed_interval_zero_iff_prefix_eq σ c (b i)
          (by dsimp [c]; omega)).2 (by simpa [c] using hpref)
      have hJne : J ≠ ∅ := by
        intro h
        have : c ∈ J := by
          simp [J, indexInterval, c, hlt]
        simpa [h] using this
      exact h0 ⟨b₀, hb₀, hb₀fit, J, ∅, hJsub,
        by simp, hJne, by simpa [hJsum]⟩
  have hab₀ : ∀ i, paperPos (a i) < paperPos b₀ := by
    intro i
    by_contra hnot
    have hge : paperPos b₀ ≤ paperPos (a i) := le_of_not_gt hnot
    let J := indexInterval (a i) (b i)
    have hJsub : J ⊆ forwardWindow b₀ (20 * D) := by
      intro x hx
      simp only [J, indexInterval, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx
      simp only [forwardWindow, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hwi := hbwin i
      simp [paperPos] at hwi hge
      omega
    have hJsum : indexSetSum σ J = 0 := by
      rw [indexSetSum_indexInterval]
      exact hzero i
    have hJne : J ≠ ∅ := by
      intro h
      have : a i ∈ J := by
        simp [J, indexInterval]
        exact ⟨le_rfl, by simpa [paperPos] using le_of_lt (hab i)⟩
      simpa [h] using this
    exact h0 ⟨b₀, hb₀, hb₀fit, J, ∅, hJsub,
      by simp, hJne, by simpa [hJsum]⟩
  obtain ⟨ρ, hmono⟩ :=
    Section5External.exists_sorting_perm a hainj
  let a' : Fin D → Fin n := a ∘ ρ
  let b' : Fin D → Fin n := b ∘ ρ
  refine ⟨(b₀, b'), ?_, hb₀, ?_⟩
  · simp only [lemma52Parameters, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro i
    exact hbwin (ρ i)
  · refine ⟨?_, a', ?_, ?_, ?_⟩
    · intro i
      exact hbwin (ρ i)
    · exact hmono
    · intro i
      exact hab₀ (ρ i)
    · intro i
      exact hzero (ρ i)

theorem lemma52_fixed_parameter_mass_le
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (θ : Fin S.card × (Fin P.D → Fin S.card))
    (hθ : θ ∈ lemma52Parameters S.card P.D)
    (hbfit : paperPos θ.1 + 30 * P.D ≤ S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ => Lemma52Witness σ θ.1 θ.2) ≤
      (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
        (S.card : ℝ) ^ 3 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let b₀ := θ.1
  let b := θ.2
  let F := forwardWindow b₀ (20 * P.D)
  have hfit20 : paperPos b₀ + 20 * P.D ≤ S.card := by omega
  have hFcard : F.card = 20 * P.D + 1 := by
    simpa [F] using card_forwardWindow_eq b₀ (20 * P.D) (by
      simp [paperPos] at hfit20 ⊢
      omega)
  have hD : 0 < P.D :=
    section5Parameters_D_pos hα0 hαh P
  have hS2 := section5_card_ge_two hα0 hαh hreg
  have hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ)
          (fun σ => Lemma52Witness σ b₀ b) ≤
        (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
          (S.card : ℝ) ^ 3 := by
    intro τ hτ
    let T := S \ indexImageSet τ F
    have himage :=
      Section5External.exposed_image_card S hτ F
    have hTcard : T.card = S.card - (20 * P.D + 1) := by
      unfold T
      rw [Finset.card_sdiff]
      · rw [himage, hFcard]
      · intro x hx
        simp [indexImageSet] at hx
        rcases hx with ⟨i, hi, rfl⟩
        exact (hτ.2 _).2 ⟨i, rfl⟩
    have hhalf : S.card / 2 ≤ T.card := by
      rw [hTcard]
      have h50 := section5_card_ge_fiftyD hreg
      omega
    have hT2 : 2 ≤ T.card := by
      have h50 := section5_card_ge_fiftyD hreg
      rw [hTcard]
      omega
    let target : Fin P.D → ZMod p :=
      fun i => - indexSetSum τ (indexInterval b₀ (b i))
    have hchain :
        ∀ (m : Fin P.D → ℕ), IsChainSizeTuple T.card m →
          ∀ z : Fin P.D → ZMod p,
            chainMass T m z ≤
              chainUpperBound p T.card (chainConstant P.D) m := by
      intro m hm z
      exact chainConstant_spec P.D hD p hp T hT2 m hm z
    have hcond :
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ)
          (fun σ => Lemma52Witness σ b₀ b) ≤
          lemma43LHS p T.card P.D (chainConstant P.D) := by
      have hprefix :=
        Section5External.conditional_prefix_chain_union_bound
          S τ hτ F b₀ target (chainConstant P.D) hchain
      apply le_trans ?_ hprefix
      apply uniformMass_mono
      intro σ hag hw
      rcases hw with ⟨hbwin, a, hmono, hab₀, hzero⟩
      refine ⟨a, hmono, hab₀, ?_⟩
      intro i
      have hbiF : b i ∈ F := by
        have hwin := hbwin i
        simp only [F, forwardWindow, Finset.mem_filter,
          Finset.mem_univ, true_and]
        simp [paperPos] at hwin ⊢
        exact ⟨le_of_lt hwin.1, hwin.2⟩
      have hb₀F : b₀ ∈ F := by
        simp [F, forwardWindow]
      have hsum :
          indexSetSum σ (indexHalfOpen (a i) b₀) +
            indexSetSum σ (indexInterval b₀ (b i)) = 0 := by
        have hab1 : (a i).val ≤ b₀.val := by
          simpa [paperPos] using le_of_lt (hab₀ i)
        have hb0b : b₀.val ≤ (b i).val := by
          simpa [paperPos] using le_of_lt (hbwin i).1
        have := hzero i
        rw [← indexSetSum_indexInterval] at this
        rw [show indexInterval (a i) (b i) =
            indexHalfOpen (a i) b₀ ∪ indexInterval b₀ (b i) by
              ext x
              simp [indexInterval, indexHalfOpen]
              omega] at this
        rw [Finset.sum_union] at this
        · exact this
        · rw [Finset.disjoint_left]
          intro x hx hy
          simp [indexHalfOpen, indexInterval] at hx hy
          omega
      have htail :
          indexSetSum σ (indexInterval b₀ (b i)) =
            indexSetSum τ (indexInterval b₀ (b i)) := by
        unfold indexSetSum
        apply Finset.sum_congr rfl
        intro x hx
        apply hag x
        simp only [F, forwardWindow, Finset.mem_filter,
          Finset.mem_univ, true_and]
        simp only [indexInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx
        have hwin := hbwin i
        simp [paperPos] at hwin
        omega
      rw [htail] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    have h43 :=
      lemma4_3 P.D hD (chainConstant P.D)
        (chainConstant_pos P.D) p hp T.card hT2
    have hbase :
        lemma43Base p T.card (chainConstant P.D) ≤
          2 * (S.card : ℝ) ^ (-α) := by
      apply Section5External.half_ground_lemma43Base_le
      · exact hS2
      · exact hhalf
      · exact Finset.card_sdiff_le _ _
      · exact section5_card_over_p hα0 hαh hp hreg
      · exact section5_chainConstant_bound hreg P.D (Or.inr rfl)
    have hpow :
        (2 * (S.card : ℝ) ^ (-α)) ^ P.D ≤
          (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3 := by
      apply Section5External.two_neg_alpha_pow_le_cube
      · omega
      · exact hα0
      · exact section5Parameters_alphaD hα0 P
    calc
      orderingConditionalMass S
          (fun σ => AgreesOn F σ τ)
          (fun σ => Lemma52Witness σ b₀ b)
        ≤ lemma43LHS p T.card P.D (chainConstant P.D) := hcond
      _ ≤ lemma43RHS p T.card P.D (chainConstant P.D) := h43
      _ = (P.D + 1 : ℝ) *
          (lemma43Base p T.card (chainConstant P.D)) ^ P.D := rfl
      _ ≤ (P.D + 1 : ℝ) *
          (2 * (S.card : ℝ) ^ (-α)) ^ P.D := by
          gcongr
      _ ≤ (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
          (S.card : ℝ) ^ 3 := by
          nlinarith [hpow]
  exact Section5External.event_le_of_agreesOn_fibers
    S F (fun σ => Lemma52Witness σ b₀ b)
    ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
      (S.card : ℝ) ^ 3)
    hfiber

/-- Lemma 5.2. -/
theorem lemma5_2
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent2 P.D) ≤ (3 / 100 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hD := section5Parameters_D_pos hα0 hαh P
  let Core : (Fin S.card → ZMod p) → Prop :=
    fun σ => BadEvent2 P.D σ ∧
      ¬ BadEvent0 P.D σ ∧ ¬ BadEvent1 P.D σ
  have hcover :
      ∀ σ ∈ indexedOrderings S, Core σ →
        ∃ θ ∈ lemma52Parameters S.card P.D,
          Lemma52Witness σ θ.1 θ.2 := by
    intro σ hσ hcore
    obtain ⟨θ, hθ, hb, hw⟩ :=
      badEvent2_core_has_witness hD σ
        hcore.1 hcore.2.1 hcore.2.2
    exact ⟨θ, hθ, hw⟩
  have hparam :
      ∀ θ ∈ lemma52Parameters S.card P.D,
        orderingEventMass S
          (fun σ => Lemma52Witness σ θ.1 θ.2) ≤
        (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
          (S.card : ℝ) ^ 3 := by
    intro θ hθ
    have hb :
        paperPos θ.1 + 30 * P.D ≤ S.card := by
      simpa [lemma52Parameters] using (Finset.mem_filter.1 hθ).2.1
    exact lemma52_fixed_parameter_mass_le
      hα0 hαh P hp S hreg θ hθ hb
  have hCore :
      orderingEventMass S Core ≤
        (lemma52Parameters S.card P.D).card *
          ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
            (S.card : ℝ) ^ 3) := by
    unfold orderingEventMass
    exact Section5External.witness_union_bound
      (indexedOrderings S)
      (lemma52Parameters S.card P.D)
      Core
      (fun θ σ => Lemma52Witness σ θ.1 θ.2)
      ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
        (S.card : ℝ) ^ 3)
      hcover
      (by simpa [orderingEventMass] using hparam)
  have hcount :
      (lemma52Parameters S.card P.D).card ≤
        S.card * (20 * P.D) ^ P.D := by
    unfold lemma52Parameters
    exact Section5External.base_and_window_tuple_count
  have hCore100 :
      orderingEventMass S Core ≤ (1 / 100 : ℝ) := by
    calc
      orderingEventMass S Core
        ≤ (lemma52Parameters S.card P.D).card *
            ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
              (S.card : ℝ) ^ 3) := hCore
      _ ≤ (S.card * (20 * P.D) ^ P.D : ℕ) *
            ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
              (S.card : ℝ) ^ 3) := by
            gcongr
            exact_mod_cast hcount
      _ = (P.D + 1 : ℝ) * (40 * P.D : ℝ) ^ P.D /
            (S.card : ℝ) ^ 2 := by
            field_simp
            ring_nf
      _ ≤ (1 / 100 : ℝ) := by
            have hnC := hreg.2.1
            have h40 := P.hundred_ge_40
            have h100 := P.second_ge_100
            have hC2 := P.Cα_second
            have hD7 : 7 ≤ P.D := by
              rw [P.D_eq]
              exact section5D_ge_seven hα0 hαh
            have hDplus :
                (P.D + 1 : ℝ) ≤ (5 * P.D : ℝ) ^ (2 * P.D) := by
              exact External.D_plus_one_le_fiveD_pow P.D hD7
            have hnpos : 0 < (S.card : ℝ) := by positivity
            apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
            have hCbig :
                100 * (P.D + 1 : ℝ) *
                    (40 * P.D : ℝ) ^ P.D ≤ P.Cα ^ 2 := by
              nlinarith [mul_le_mul hDplus h40
                (by positivity) (by positivity)]
            nlinarith
  have h0 := lemma5_4 hα0 hαh P hp S hreg
  have h1 := lemma5_1 hα0 hαh P hp S hreg
  have htotal :=
    uniformMass_le_two_exceptions
      (indexedOrderings S)
      (BadEvent2 P.D) (BadEvent0 P.D) (BadEvent1 P.D)
      (1 / 100 : ℝ)
      (by simpa [orderingEventMass, Core] using hCore100)
  nlinarith

end

end GrahamRearrangement
