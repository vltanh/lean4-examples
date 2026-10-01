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

def lemma52ChoiceSet {n : ℕ} (b : Fin n) (D : ℕ) :
    Finset (Fin n) :=
  (forwardWindow b (20 * D)).erase b

theorem mem_lemma52ChoiceSet {n D : ℕ} {b x : Fin n} :
    x ∈ lemma52ChoiceSet b D ↔
      paperPos b < paperPos x ∧
        paperPos x ≤ paperPos b + 20 * D := by
  simp [lemma52ChoiceSet,forwardWindow,paperPos]
  omega

theorem card_lemma52ChoiceSet_le {n D : ℕ} (b : Fin n) :
    (lemma52ChoiceSet b D).card ≤ 20 * D := by
  have hb : b ∈ forwardWindow b (20 * D) := by
    simp [forwardWindow]
  unfold lemma52ChoiceSet
  rw [Finset.card_erase_of_mem hb]
  have hw := card_forwardWindow_le b (20 * D)
  omega

def lemma52Parameters (n D : ℕ) :
    Finset (Fin n × (Fin D → Fin n)) := by
  classical
  exact Finset.univ.biUnion fun b =>
    if hfit : paperPos b + 30 * D ≤ n then
      (Finset.univ.pi fun _ : Fin D => lemma52ChoiceSet b D).image
        (fun v => (b,v))
    else ∅

theorem mem_lemma52Parameters {n D : ℕ}
    {b : Fin n} {v : Fin D → Fin n} :
    (b,v) ∈ lemma52Parameters n D ↔
      paperPos b + 30 * D ≤ n ∧
      ∀ i, paperPos b < paperPos (v i) ∧
        paperPos (v i) ≤ paperPos b + 20 * D := by
  classical
  by_cases hfit : paperPos b + 30 * D ≤ n
  · simp [lemma52Parameters,hfit,mem_lemma52ChoiceSet]
  · simp [lemma52Parameters,hfit]

theorem lemma52Parameters_card_le (n D : ℕ) :
    (lemma52Parameters n D).card ≤ n * (20 * D) ^ D := by
  classical
  unfold lemma52Parameters
  calc
    _ ≤ ∑ b : Fin n,
        (if hfit : paperPos b + 30 * D ≤ n then
          ((Finset.univ.pi fun _ : Fin D =>
            lemma52ChoiceSet b D).image (fun v => (b,v))).card
        else 0) := by
          apply card_biUnion_le_sum
    _ ≤ ∑ _b : Fin n, (20 * D) ^ D := by
          gcongr with b
          split
          · calc
              ((Finset.univ.pi fun _ : Fin D =>
                  lemma52ChoiceSet b D).image (fun v => (b,v))).card
                ≤ (Finset.univ.pi fun _ : Fin D =>
                    lemma52ChoiceSet b D).card :=
                  Finset.card_image_le
              _ ≤ (20 * D) ^ Fintype.card (Fin D) :=
                  card_pi_le_pow
                    (fun _ : Fin D => lemma52ChoiceSet b D)
                    (20 * D) (fun _ => card_lemma52ChoiceSet_le b)
              _ = (20 * D) ^ D := by simp
          · simp
    _ = n * (20 * D) ^ D := by simp

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
  · apply mem_lemma52Parameters.mpr
    refine ⟨hb₀fit, ?_⟩
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
      · exact le_of_lt (chainConstant_pos P.D)
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

def lemma52PrefixTuples {n k : ℕ} (b₀ : Fin n) :
    Finset (Fin k → Fin n) :=
  Finset.univ.filter fun a =>
    StrictMono a ∧ ∀ i, paperPos (a i) < paperPos b₀

def lemma52PrefixIntervals {n k : ℕ}
    (b₀ : Fin n) (a : Fin k → Fin n) :
    Fin k → Finset (Fin n) :=
  fun i => indexHalfOpen (a (reverseIndex k i)) b₀

def lemma52PrefixSizes {n k : ℕ}
    (b₀ : Fin n) (a : Fin k → Fin n) :
    Fin k → ℕ :=
  fun i => (lemma52PrefixIntervals b₀ a i).card

theorem lemma52PrefixSizes_valid {n k : ℕ}
    (b₀ : Fin n) (Tcard : ℕ) (hroom : b₀.val < Tcard)
    {a : Fin k → Fin n} (ha : a ∈ lemma52PrefixTuples b₀) :
    IsChainSizeTuple Tcard (lemma52PrefixSizes b₀ a) := by
  have hdata := (Finset.mem_filter.mp ha).2
  constructor
  · intro i j hij
    have hrev : (reverseIndex k j).val < (reverseIndex k i).val := by
      rw [reverseIndex_apply_val,reverseIndex_apply_val]
      omega
    have haa :
        (a (reverseIndex k j)).val <
          (a (reverseIndex k i)).val := by
      exact_mod_cast hdata.1 (Fin.mk_lt_mk.mpr hrev)
    have hai := hdata.2 (reverseIndex k i)
    have haj := hdata.2 (reverseIndex k j)
    simp [lemma52PrefixSizes,lemma52PrefixIntervals,
      card_indexHalfOpen,
      show (a (reverseIndex k i)).val ≤ b₀.val by
        simp [paperPos] at hai; omega,
      show (a (reverseIndex k j)).val ≤ b₀.val by
        simp [paperPos] at haj; omega]
    omega
  · intro i
    have hai := hdata.2 (reverseIndex k i)
    have hale : (a (reverseIndex k i)).val ≤ b₀.val := by
      simp [paperPos] at hai
      omega
    rw [show lemma52PrefixSizes b₀ a i =
        b₀.val - (a (reverseIndex k i)).val by
      exact card_indexHalfOpen _ _ hale]
    constructor
    · simp [paperPos] at hai
      omega
    · omega

theorem lemma52PrefixIntervals_nested {n k : ℕ}
    (b₀ : Fin n) {a : Fin k → Fin n}
    (ha : a ∈ lemma52PrefixTuples b₀) :
    ∀ i j, i ≤ j →
      lemma52PrefixIntervals b₀ a i ⊆
        lemma52PrefixIntervals b₀ a j := by
  intro i j hij x hx
  have hdata := (Finset.mem_filter.mp ha).2
  have hrev : reverseIndex k j ≤ reverseIndex k i := by
    apply Fin.mk_le_mk.mpr
    rw [reverseIndex_apply_val,reverseIndex_apply_val]
    omega
  have haa := hdata.1.monotone hrev
  simp only [lemma52PrefixIntervals,indexHalfOpen,
    Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
  exact ⟨le_trans (by exact_mod_cast haa) hx.1,hx.2⟩

theorem lemma52PrefixSizes_injective {n k : ℕ}
    (b₀ : Fin n) :
    Set.InjOn (lemma52PrefixSizes b₀)
      (lemma52PrefixTuples b₀ : Set (Fin k → Fin n)) := by
  intro a ha a' ha' h
  funext i
  let r := reverseIndex k i
  have hai := (Finset.mem_filter.mp ha).2.2 i
  have hai' := (Finset.mem_filter.mp ha').2.2 i
  have hle : (a i).val ≤ b₀.val := by
    simp [paperPos] at hai
    omega
  have hle' : (a' i).val ≤ b₀.val := by
    simp [paperPos] at hai'
    omega
  have hr := congrFun h r
  have hri :
      lemma52PrefixSizes b₀ a r = b₀.val - (a i).val := by
    simpa [lemma52PrefixSizes,lemma52PrefixIntervals,r,
      reverseIndex_involutive] using
      card_indexHalfOpen (a i) b₀ hle
  have hri' :
      lemma52PrefixSizes b₀ a' r = b₀.val - (a' i).val := by
    simpa [lemma52PrefixSizes,lemma52PrefixIntervals,r,
      reverseIndex_involutive] using
      card_indexHalfOpen (a' i) b₀ hle'
  rw [hri,hri'] at hr
  exact Fin.ext (by omega)

theorem lemma52_prefix_chain_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) (b₀ : Fin S.card)
    (hFright : ∀ x ∈ F, b₀.val ≤ x.val)
    (hroom : b₀.val < (S \ indexImageSet τ F).card)
    (target : Fin k → ZMod p)
    (C : ℝ)
    (hchain :
      ∀ m, IsChainSizeTuple (S \ indexImageSet τ F).card m →
        ∀ z, chainMass (S \ indexImageSet τ F) m z ≤
          chainUpperBound p (S \ indexImageSet τ F).card C m) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∃ a : Fin k → Fin S.card,
          StrictMono a ∧
          (∀ i, paperPos (a i) < paperPos b₀) ∧
          ∀ i, indexSetSum σ (indexHalfOpen (a i) b₀) = target i) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C := by
  classical
  let A := lemma52PrefixTuples (k := k) b₀
  let I := fun a : Fin k → Fin S.card =>
    lemma52PrefixIntervals b₀ a
  let m := fun a : Fin k → Fin S.card =>
    lemma52PrefixSizes b₀ a
  let z := fun _a : Fin k → Fin S.card =>
    fun i => target (reverseIndex k i)
  have hdisj : ∀ a ∈ A, ∀ i, Disjoint F (I a i) := by
    intro a ha i
    rw [Finset.disjoint_left]
    intro x hxF hxI
    have hxright := hFright x hxF
    simp only [I,lemma52PrefixIntervals,indexHalfOpen,
      Finset.mem_filter,Finset.mem_univ,true_and] at hxI
    omega
  have hnested : ∀ a ∈ A, ∀ i j, i ≤ j → I a i ⊆ I a j := by
    intro a ha
    exact lemma52PrefixIntervals_nested b₀ ha
  have hvalid : ∀ a ∈ A,
      IsChainSizeTuple (S \ indexImageSet τ F).card (m a) := by
    intro a ha
    exact lemma52PrefixSizes_valid b₀ _ hroom ha
  have hinj : Set.InjOn m A := by
    exact lemma52PrefixSizes_injective b₀
  have hchain' :
      ∀ a ∈ A,
        chainMass (S \ indexImageSet τ F) (m a) (z a) ≤
          chainUpperBound p (S \ indexImageSet τ F).card C (m a) := by
    intro a ha
    exact hchain (m a) (hvalid a ha) (z a)
  have hgeneric :=
    Section5External.conditional_chain_witness_union_bound
      S τ hτ F A I m z C
      hdisj hnested (fun _ _ _ => rfl) hvalid hinj hchain'
  apply le_trans ?_ hgeneric
  unfold orderingConditionalMass uniformConditionalMass
  apply uniformMass_mono
  intro σ h
  rcases h with ⟨a,hmono,hbefore,hsum⟩
  refine ⟨a,?_,?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hmono,hbefore⟩
  · intro i
    have hi := hsum (reverseIndex k i)
    simpa [I,z,lemma52PrefixIntervals,reverseIndex_involutive] using hi

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
      exact (mem_lemma52Parameters.mp hθ).1
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
        S.card * (20 * P.D) ^ P.D :=
    lemma52Parameters_card_le S.card P.D
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
