import Lean4Examples.GrahamRearrangement.Rearrangement.Parameters

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section5External

/-!
# External finite-permutation facts used in Section 5

All axioms here are generic facts about uniformly random bijections, conditioning,
finite fibers, and matchings.  None is a numbered result of Pham--Sauermann.
-/

noncomputable section

theorem indexedOrderings_nonempty {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (indexedOrderings S).Nonempty := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  let σ : Fin S.card → ZMod p := fun i => (e i).1
  refine ⟨σ, ?_⟩
  simp only [indexedOrderings, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
    · rintro ⟨i, rfl⟩
      exact (e i).2

def applyValuePerm {n p : ℕ}
    (π : Equiv.Perm (ZMod p))
    (σ : Fin n → ZMod p) : Fin n → ZMod p :=
  π ∘ σ

theorem applyValuePerm_isIndexedOrdering
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {σ : Fin S.card → ZMod p}
    (hσ : IsIndexedOrdering S σ) :
    IsIndexedOrdering S (applyValuePerm π σ) := by
  constructor
  · exact π.injective.comp hσ.1
  · intro x
    constructor
    · intro hx
      rw [← hπS] at hx
      rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
      rcases (hσ.2 y).1 hy with ⟨i,hi⟩
      exact ⟨i,by simpa [applyValuePerm,hi]⟩
    · rintro ⟨i,rfl⟩
      rw [← hπS]
      exact Finset.mem_image.mpr
        ⟨σ i,(hσ.2 _).2 ⟨i,rfl⟩,rfl⟩

theorem indexImageSet_applyValuePerm
    {n p : ℕ} (π : Equiv.Perm (ZMod p))
    (σ : Fin n → ZMod p) (I : Finset (Fin n)) :
    indexImageSet (applyValuePerm π σ) I =
      (indexImageSet σ I).image π := by
  ext x
  simp [indexImageSet,applyValuePerm]

theorem fixedIndexSet_image_uniform {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S (fun σ => E (indexImageSet σ I)) =
      uniformMass (S.powersetCard I.card) E := by
  classical
  let Ω := indexedOrderings S
  let V := S.powersetCard I.card
  have hΩ : Ω.Nonempty := indexedOrderings_nonempty S
  have hV : V.Nonempty := powersetCard_nonempty S
    (by
      calc I.card ≤ Fintype.card (Fin S.card) := Finset.card_le_univ _
           _ = S.card := by simp)
  have hmap : ∀ σ ∈ Ω, indexImageSet σ I ∈ V := by
    intro σ hσmem
    have hσ : IsIndexedOrdering S σ := by
      simpa [Ω,indexedOrderings] using
        (Finset.mem_filter.mp hσmem).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
      exact (hσ.2 _).2 ⟨i,rfl⟩
    · unfold indexImageSet
      exact Finset.card_image_iff.mpr hσ.1
  have heq :
      ∀ R ∈ V, ∀ R' ∈ V,
        (Ω.filter fun σ => indexImageSet σ I = R).card =
          (Ω.filter fun σ => indexImageSet σ I = R').card := by
    intro R hR R' hR'
    obtain ⟨π,hπR,hπS,hπout⟩ :=
      exists_perm_maps_finset S R R'
        (Finset.mem_powersetCard.mp hR).1
        (Finset.mem_powersetCard.mp hR').1
        (by rw [(Finset.mem_powersetCard.mp hR).2,
                (Finset.mem_powersetCard.mp hR').2])
    apply Finset.card_bij
      (fun σ _ => applyValuePerm π σ)
    · intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hσmem,himg⟩
      have hσord : IsIndexedOrdering S σ := by
        simpa [Ω,indexedOrderings] using
          (Finset.mem_filter.mp hσmem).2
      apply Finset.mem_filter.mpr
      constructor
      · simpa [Ω,indexedOrderings] using
          applyValuePerm_isIndexedOrdering S π hπS hσord
      · rw [indexImageSet_applyValuePerm,himg,hπR]
    · intro σ hσ τ hτ he
      funext i
      apply π.injective
      exact congrFun he i
    · intro τ hτ
      rcases Finset.mem_filter.mp hτ with ⟨hτmem,himg⟩
      have hτord : IsIndexedOrdering S τ := by
        simpa [Ω,indexedOrderings] using
          (Finset.mem_filter.mp hτmem).2
      let σ := applyValuePerm π.symm τ
      refine ⟨σ,?_,?_⟩
      · have hπsymS : S.image π.symm = S := by
          apply Finset.image_injective π.injective
          simpa using congrArg (Finset.image π) hπS
        apply Finset.mem_filter.mpr
        constructor
        · simpa [Ω,indexedOrderings,σ] using
            applyValuePerm_isIndexedOrdering S π.symm hπsymS hτord
        · rw [indexImageSet_applyValuePerm,himg]
          apply Finset.image_injective π.injective
          simpa using congrArg (Finset.image π.symm) hπR
      · funext i
        simp [σ,applyValuePerm]
  unfold orderingEventMass
  exact uniformMass_statistic_of_pairwise_equal_fibers
    Ω V (fun σ => indexImageSet σ I) hmap hV hΩ heq E

/-- The image of a fixed r-set of indices under a uniform bijection is a
uniform r-subset of S. -/
theorem fixedIndexSet_sumMass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (z : ZMod p) :
    orderingEventMass S (fun σ => indexSetSum σ I = z) =
      sliceMass S I.card z := by
  rw [← fixedIndexSet_image_uniform S I
      (fun R => subsetSum R = z)]
  apply uniformMass_congr
  intro σ hσmem
  have hσ : IsIndexedOrdering S σ := by
    simpa [indexedOrderings] using
      (Finset.mem_filter.mp hσmem).2
  rw [indexSetSum_eq_subsetSum_image hσ.1 I]

/-- Composition by a fixed permutation of positions preserves the uniform law. -/
theorem ordering_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ => E (applyPositionPerm σ π)) := by
  unfold orderingEventMass
  apply uniformMass_bij
    (indexedOrderings S) (indexedOrderings S)
    (fun σ => applyPositionPerm σ π)
  · intro σ hσ
    have hs : IsIndexedOrdering S σ := by
      simpa [indexedOrderings] using
        (Finset.mem_filter.mp hσ).2
    simpa [indexedOrderings] using
      applyPositionPerm_isIndexedOrdering hs π
  · intro σ hσ τ hτ he
    funext i
    have hi := congrFun he (π.symm i)
    simpa [applyPositionPerm,Function.comp_def] using hi
  · intro τ hτ
    refine ⟨applyPositionPerm τ π.symm,?_,?_⟩
    · have ht : IsIndexedOrdering S τ := by
        simpa [indexedOrderings] using
          (Finset.mem_filter.mp hτ).2
      simpa [indexedOrderings] using
        applyPositionPerm_isIndexedOrdering ht π.symm
    · funext i
      simp [applyPositionPerm,Function.comp_def]
  · intro σ hσ
    rfl

/-- Conditional version of the preceding invariance. -/
theorem ordering_conditional_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (given event : (Fin S.card → ZMod p) → Prop)
    [DecidablePred given] [DecidablePred event] :
    orderingConditionalMass S given event =
      orderingConditionalMass S
        (fun σ => given (applyPositionPerm σ π))
        (fun σ => event (applyPositionPerm σ π)) := by
  unfold orderingConditionalMass uniformConditionalMass
  apply uniformMass_bij
    ((indexedOrderings S).filter given)
    ((indexedOrderings S).filter
      fun σ => given (applyPositionPerm σ π))
    (fun σ => applyPositionPerm σ π.symm)
  · intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨hσord,hgiven⟩
    apply Finset.mem_filter.mpr
    constructor
    · have hs : IsIndexedOrdering S σ := by
        simpa [indexedOrderings] using
          (Finset.mem_filter.mp hσord).2
      simpa [indexedOrderings] using
        applyPositionPerm_isIndexedOrdering hs π.symm
    · simpa [applyPositionPerm,Function.comp_def] using hgiven
  · intro σ hσ τ hτ he
    funext i
    have := congrFun he (π i)
    simpa [applyPositionPerm,Function.comp_def] using this
  · intro τ hτ
    refine ⟨applyPositionPerm τ π,?_,?_⟩
    · rcases Finset.mem_filter.mp hτ with ⟨hτord,hgiven⟩
      apply Finset.mem_filter.mpr
      constructor
      · have ht : IsIndexedOrdering S τ := by
          simpa [indexedOrderings] using
            (Finset.mem_filter.mp hτord).2
        simpa [indexedOrderings] using
          applyPositionPerm_isIndexedOrdering ht π
      · exact hgiven
    · funext i
      simp [applyPositionPerm,Function.comp_def]
  · intro σ hσ
    simp [applyPositionPerm,Function.comp_def]

/-- Distinct index subsets in a window have equal image sums with probability at
most the reciprocal number of choices left for one exposed coordinate. -/
theorem sliceMass_one_le_inv_card {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (hT : T.Nonempty) (z : ZMod p) :
    sliceMass T 1 z ≤ 1 / (T.card : ℝ) := by
  unfold sliceMass uniformMass
  have hden : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hnum :
      ((T.powersetCard 1).filter fun R => subsetSum R = z).card ≤ 1 := by
    by_cases hz : z ∈ T
    · have hsub :
        (T.powersetCard 1).filter (fun R => subsetSum R = z) ⊆ {{z}} := by
        intro R hR
        rcases Finset.mem_filter.mp hR with ⟨hpow,hsum⟩
        rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hpow).2
          with ⟨x,hRx⟩
        have hxT : x ∈ T := (Finset.mem_powersetCard.mp hpow).1
          (by simp [hRx])
        have : x = z := by
          simpa [subsetSum,hRx] using hsum
        subst x
        simp [hRx]
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · have hemp :
        (T.powersetCard 1).filter (fun R => subsetSum R = z) = ∅ := by
        ext R
        constructor
        · intro hR
          rcases Finset.mem_filter.mp hR with ⟨hpow,hsum⟩
          rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hpow).2
            with ⟨x,hRx⟩
          have hxT := (Finset.mem_powersetCard.mp hpow).1 (by simp [hRx])
          have hxz : x = z := by simpa [subsetSum,hRx] using hsum
          exact False.elim (hz (hxz ▸ hxT))
        · simp
      simp [hemp]
  have hpowerset : (T.powersetCard 1).card = T.card := by
    rw [Finset.card_powersetCard]
    simp
  rw [hpowerset]
  exact (div_le_div_iff_of_pos_right hden).2 (by exact_mod_cast hnum)

theorem indexSetSum_eq_of_agreesOn
    {n p : ℕ} {F : Finset (Fin n)}
    {σ τ : Fin n → ZMod p}
    (hagr : AgreesOn F σ τ)
    {J : Finset (Fin n)} (hJF : J ⊆ F) :
    indexSetSum σ J = indexSetSum τ J := by
  unfold indexSetSum
  apply Finset.sum_congr rfl
  intro i hi
  exact hagr i (hJF hi)

theorem distinct_index_subset_sums_mass_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (W J J' : Finset (Fin S.card))
    (hJ : J ⊆ W) (hJ' : J' ⊆ W) (hne : J ≠ J')
    (hW : W.card ≤ S.card) :
    orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
      1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by
  classical
  have hsymm :
      (J \ J').Nonempty ∨ (J' \ J).Nonempty := by
    by_contra h
    push_neg at h
    have hsub1 : J ⊆ J' := by
      intro i hi
      by_contra hnot
      exact h.1 i (Finset.mem_sdiff.mpr ⟨hi,hnot⟩)
    have hsub2 : J' ⊆ J := by
      intro i hi
      by_contra hnot
      exact h.2 i (Finset.mem_sdiff.mpr ⟨hi,hnot⟩)
    exact hne (Finset.Subset.antisymm hsub1 hsub2)
  rcases hsymm with hleft | hright
  · let i := (J \ J').min' hleft
    have hiJ : i ∈ J := (Finset.mem_sdiff.mp ((J \ J').min'_mem hleft)).1
    have hiJ' : i ∉ J' := (Finset.mem_sdiff.mp ((J \ J').min'_mem hleft)).2
    have hiW : i ∈ W := hJ hiJ
    let F := W.erase i
    have hFcard : F.card = W.card - 1 := by
      exact Finset.card_erase_of_mem hiW
    have hfiber :
        ∀ τ, IsIndexedOrdering S τ →
          orderingConditionalMass S
            (fun σ => AgreesOn F σ τ)
            (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
          1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by
      intro τ hτ
      let T := S \ indexImageSet τ F
      have hTcard : T.card = S.card - F.card := by
        rw [Finset.card_sdiff (exposedImage_subset S hτ F),
          exposed_image_card S hτ F]
      have hTcard' : T.card = S.card - W.card + 1 := by
        rw [hTcard,hFcard]
        omega
      have hdisj : Disjoint F {i} := by
        simp [F,hiW]
      let z : ZMod p :=
        indexSetSum τ J' - indexSetSum τ (J.erase i)
      have hevent :
          ∀ σ, AgreesOn F σ τ →
            (indexSetSum σ J = indexSetSum σ J' ↔
              indexSetSum σ {i} = z) := by
        intro σ hagr
        have hJer : J.erase i ⊆ F := by
          intro x hx
          have hxJ := Finset.mem_of_mem_erase hx
          have hxW := hJ hxJ
          have hxi : x ≠ i := Finset.ne_of_mem_erase hx
          exact Finset.mem_erase.mpr ⟨hxi,hxW⟩
        have hJ'F : J' ⊆ F := by
          intro x hx
          have hxW := hJ' hx
          exact Finset.mem_erase.mpr
            ⟨by intro h; subst x; exact hiJ' hx,hxW⟩
        have hsumJ :
            indexSetSum σ J =
              σ i + indexSetSum τ (J.erase i) := by
          rw [show J = insert i (J.erase i) by
            ext x; simp [hiJ]]
          simp [indexSetSum,hiJ,
            indexSetSum_eq_of_agreesOn hagr hJer]
        have hsumJ' :
            indexSetSum σ J' = indexSetSum τ J' :=
          indexSetSum_eq_of_agreesOn hagr hJ'F
        simp [hsumJ,hsumJ',z,indexSetSum]
        abel
      calc
        orderingConditionalMass S
            (fun σ => AgreesOn F σ τ)
            (fun σ => indexSetSum σ J = indexSetSum σ J')
          = orderingConditionalMass S
              (fun σ => AgreesOn F σ τ)
              (fun σ => indexSetSum σ {i} = z) := by
                unfold orderingConditionalMass uniformConditionalMass
                apply uniformMass_congr
                intro σ hσ
                exact hevent σ (Finset.mem_filter.mp hσ).2
        _ = sliceMass T 1 z := by
              simpa [T] using
                conditional_fixedIndexSet_sumMass S τ hτ F {i} hdisj z
        _ ≤ 1 / (T.card : ℝ) := by
              have hTne : T.Nonempty := by
                have hden : 1 ≤ T.card := by
                  rw [hTcard']
                  omega
                exact Finset.card_pos.mp hden
              exact sliceMass_one_le_inv_card T hTne z
        _ = 1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by rw [hTcard']
    exact event_le_of_agreesOn_fibers S F
      (fun σ => indexSetSum σ J = indexSetSum σ J')
      _ hfiber
  · let i := (J' \ J).min' hright
    have hiJ' : i ∈ J' :=
      (Finset.mem_sdiff.mp ((J' \ J).min'_mem hright)).1
    have hiJ : i ∉ J :=
      (Finset.mem_sdiff.mp ((J' \ J).min'_mem hright)).2
    have hiW : i ∈ W := hJ' hiJ'
    let F := W.erase i
    have hFcard : F.card = W.card - 1 := by
      exact Finset.card_erase_of_mem hiW
    have hfiber :
        ∀ τ, IsIndexedOrdering S τ →
          orderingConditionalMass S
            (fun σ => AgreesOn F σ τ)
            (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
          1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by
      intro τ hτ
      let T := S \ indexImageSet τ F
      have hTcard : T.card = S.card - F.card := by
        rw [Finset.card_sdiff (exposedImage_subset S hτ F),
          exposed_image_card S hτ F]
      have hTcard' : T.card = S.card - W.card + 1 := by
        rw [hTcard,hFcard]
        omega
      have hdisj : Disjoint F {i} := by
        simp [F,hiW]
      let z : ZMod p :=
        indexSetSum τ J - indexSetSum τ (J'.erase i)
      have hevent :
          ∀ σ, AgreesOn F σ τ →
            (indexSetSum σ J = indexSetSum σ J' ↔
              indexSetSum σ {i} = z) := by
        intro σ hagr
        have hJ'ER : J'.erase i ⊆ F := by
          intro x hx
          have hxJ := Finset.mem_of_mem_erase hx
          have hxW := hJ' hxJ
          have hxi : x ≠ i := Finset.ne_of_mem_erase hx
          exact Finset.mem_erase.mpr ⟨hxi,hxW⟩
        have hJF : J ⊆ F := by
          intro x hx
          have hxW := hJ hx
          exact Finset.mem_erase.mpr
            ⟨by intro h; subst x; exact hiJ hx,hxW⟩
        have hsumJ :
            indexSetSum σ J = indexSetSum τ J :=
          indexSetSum_eq_of_agreesOn hagr hJF
        have hsumJ' :
            indexSetSum σ J' =
              σ i + indexSetSum τ (J'.erase i) := by
          rw [show J' = insert i (J'.erase i) by
            ext x; simp [hiJ']]
          simp [indexSetSum,hiJ',
            indexSetSum_eq_of_agreesOn hagr hJ'ER]
        simp [hsumJ,hsumJ',z,indexSetSum]
        abel
      calc
        orderingConditionalMass S
            (fun σ => AgreesOn F σ τ)
            (fun σ => indexSetSum σ J = indexSetSum σ J')
          = orderingConditionalMass S
              (fun σ => AgreesOn F σ τ)
              (fun σ => indexSetSum σ {i} = z) := by
                unfold orderingConditionalMass uniformConditionalMass
                apply uniformMass_congr
                intro σ hσ
                exact hevent σ (Finset.mem_filter.mp hσ).2
        _ = sliceMass T 1 z := by
              simpa [T] using
                conditional_fixedIndexSet_sumMass S τ hτ F {i} hdisj z
        _ ≤ 1 / (T.card : ℝ) := by
              have hTne : T.Nonempty := by
                have hden : 1 ≤ T.card := by
                  rw [hTcard']
                  omega
                exact Finset.card_pos.mp hden
              exact sliceMass_one_le_inv_card T hTne z
        _ = 1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by rw [hTcard']
    exact event_le_of_agreesOn_fibers S F
      (fun σ => indexSetSum σ J = indexSetSum σ J')
      _ hfiber

theorem exposedImage_subset {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    indexImageSet τ F ⊆ S := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
  exact (hτ.2 _).2 ⟨i,rfl⟩

theorem unexposed_indexImage_subset_remaining
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ σ : Fin S.card → ZMod p)
    (hτ : IsIndexedOrdering S τ)
    (hσ : IsIndexedOrdering S σ)
    (F J : Finset (Fin S.card))
    (hagr : AgreesOn F σ τ) (hdisj : Disjoint F J) :
    indexImageSet σ J ⊆ S \ indexImageSet τ F := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j,hj,rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · exact (hσ.2 _).2 ⟨j,rfl⟩
  · intro himg
    rcases Finset.mem_image.mp himg with ⟨i,hiF,heq⟩
    have hσi : σ i = τ i := hagr i hiF
    have hsij : i = j := hσ.1 (hσi.trans heq)
    subst i
    exact Finset.disjoint_left.mp hdisj hiF hj

theorem valuePerm_preserves_agreement
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ σ : Fin S.card → ZMod p)
    (F : Finset (Fin S.card))
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∈ indexImageSet τ F, π x = x)
    (hagr : AgreesOn F σ τ) :
    AgreesOn F (applyValuePerm π σ) τ := by
  intro i hi
  unfold applyValuePerm
  change π (σ i) = τ i
  rw [hagr i hi]
  exact hfix (τ i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem conditional_fixedIndexSet_image_uniform
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F J : Finset (Fin S.card)) (hdisj : Disjoint F J)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => E (indexImageSet σ J)) =
    uniformMass
      ((S \ indexImageSet τ F).powersetCard J.card) E := by
  classical
  let Ω := (indexedOrderings S).filter fun σ => AgreesOn F σ τ
  let T := S \ indexImageSet τ F
  let V := T.powersetCard J.card
  have hΩ : Ω.Nonempty := by
    refine ⟨τ,?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · simpa [indexedOrderings] using hτ
    · intro i hi
      rfl
  have hJcard : J.card ≤ T.card := by
    have hFI : F.card + J.card ≤ S.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact le_trans (Finset.card_le_univ (F ∪ J)) (by simp)
    have hEcard := exposed_image_card S hτ F
    unfold T
    rw [Finset.card_sdiff (exposedImage_subset S hτ F),hEcard]
    omega
  have hV : V.Nonempty := powersetCard_nonempty T hJcard
  have hmap : ∀ σ ∈ Ω, indexImageSet σ J ∈ V := by
    intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨hσmem,hagr⟩
    have hσord : IsIndexedOrdering S σ := by
      simpa [indexedOrderings] using
        (Finset.mem_filter.mp hσmem).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact unexposed_indexImage_subset_remaining
        S τ σ hτ hσord F J hagr hdisj
    · unfold indexImageSet
      exact Finset.card_image_iff.mpr hσord.1
  have heq :
      ∀ R ∈ V, ∀ R' ∈ V,
        (Ω.filter fun σ => indexImageSet σ J = R).card =
          (Ω.filter fun σ => indexImageSet σ J = R').card := by
    intro R hR R' hR'
    obtain ⟨π,hπR,hπT,hπout⟩ :=
      exists_perm_maps_finset T R R'
        (Finset.mem_powersetCard.mp hR).1
        (Finset.mem_powersetCard.mp hR').1
        (by rw [(Finset.mem_powersetCard.mp hR).2,
                (Finset.mem_powersetCard.mp hR').2])
    have hfixE : ∀ x ∈ indexImageSet τ F, π x = x := by
      intro x hx
      exact hπout x (by
        intro hxT
        exact (Finset.mem_sdiff.mp hxT).2 hx)
    have hπS : S.image π = S := by
      ext x
      by_cases hxE : x ∈ indexImageSet τ F
      · have hfix := hfixE x hxE
        simp [hfix,(exposedImage_subset S hτ F hxE)]
      · have hxT : x ∈ T ↔ x ∈ S := by
          simp [T,hxE]
        rw [← hπT]
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
          exact Finset.mem_image.mpr ⟨y,hxT.mp hy,rfl⟩
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
          by_cases hyE : y ∈ indexImageSet τ F
          · have hyfix := hfixE y hyE
            subst x
            exact False.elim (hxE hyE)
          · exact Finset.mem_image.mpr
              ⟨y,(by simpa [T,hyE] using hy),rfl⟩
    apply Finset.card_bij
      (fun σ _ => applyValuePerm π σ)
    · intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hσΩ,himg⟩
      rcases Finset.mem_filter.mp hσΩ with ⟨hσmem,hagr⟩
      have hσord : IsIndexedOrdering S σ := by
        simpa [indexedOrderings] using
          (Finset.mem_filter.mp hσmem).2
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · simpa [indexedOrderings] using
            applyValuePerm_isIndexedOrdering S π hπS hσord
        · exact valuePerm_preserves_agreement S τ σ F π hfixE hagr
      · rw [indexImageSet_applyValuePerm,himg,hπR]
    · intro σ hσ ρ hρ he
      funext i
      apply π.injective
      exact congrFun he i
    · intro ρ hρ
      let σ := applyValuePerm π.symm ρ
      refine ⟨σ,?_,?_⟩
      · rcases Finset.mem_filter.mp hρ with ⟨hρΩ,himg⟩
        rcases Finset.mem_filter.mp hρΩ with ⟨hρmem,hagr⟩
        have hρord : IsIndexedOrdering S ρ := by
          simpa [indexedOrderings] using
            (Finset.mem_filter.mp hρmem).2
        have hπsymS : S.image π.symm = S := by
          apply Finset.image_injective π.injective
          simpa using congrArg (Finset.image π) hπS
        have hfixEsym :
            ∀ x ∈ indexImageSet τ F, π.symm x = x := by
          intro x hx
          exact perm_symm_fixes_of_fixes π (hfixE x hx)
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          constructor
          · simpa [indexedOrderings,σ] using
              applyValuePerm_isIndexedOrdering S π.symm hπsymS hρord
          · exact valuePerm_preserves_agreement
              S τ ρ F π.symm hfixEsym hagr
        · rw [indexImageSet_applyValuePerm,himg]
          apply Finset.image_injective π.injective
          simpa using congrArg (Finset.image π.symm) hπR
      · funext i
        simp [σ,applyValuePerm]
  unfold orderingConditionalMass uniformConditionalMass
  exact uniformMass_statistic_of_pairwise_equal_fibers
    Ω V (fun σ => indexImageSet σ J) hmap hV hΩ heq E

theorem conditional_fixedIndexSet_sumMass
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F J : Finset (Fin S.card)) (hdisj : Disjoint F J)
    (z : ZMod p) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => indexSetSum σ J = z) =
    sliceMass (S \ indexImageSet τ F) J.card z := by
  rw [← conditional_fixedIndexSet_image_uniform
      S τ hτ F J hdisj (fun R => subsetSum R = z)]
  apply uniformMass_congr
  intro σ hσ
  rcases Finset.mem_filter.mp hσ with ⟨hσmem,hagr⟩
  have hσord : IsIndexedOrdering S σ := by
    simpa [indexedOrderings] using
      (Finset.mem_filter.mp hσmem).2
  rw [indexSetSum_eq_subsetSum_image hσord.1 J]

/-- Conditional union bound for a finite family of disjoint unexposed index sets. -/
theorem conditional_index_family_sumMass_le_zmod
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (A : Finset (Fin S.card))
    (I : Fin S.card → Finset (Fin S.card))
    (z : Fin S.card → ZMod p)
    (hdisj : ∀ a ∈ A, Disjoint F (I a)) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∃ a ∈ A, indexSetSum σ (I a) = z a) ≤
      ∑ a ∈ A,
        sliceMass (S \ indexImageSet τ F) (I a).card (z a) := by
  unfold orderingConditionalMass uniformConditionalMass
  calc
    uniformMass ((indexedOrderings S).filter
        (fun σ => AgreesOn F σ τ))
        (fun σ => ∃ a ∈ A, indexSetSum σ (I a) = z a)
      ≤ ∑ a ∈ A,
          uniformMass ((indexedOrderings S).filter
            (fun σ => AgreesOn F σ τ))
            (fun σ => indexSetSum σ (I a) = z a) :=
          uniformMass_exists_le_sum _ A _
    _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          simpa [orderingConditionalMass,uniformConditionalMass] using
            conditional_fixedIndexSet_sumMass
              S τ hτ F (I a) (hdisj a ha) (z a)

theorem partition_member_unique
    {α : Type*} [DecidableEq α] {k : ℕ}
    (T : Finset α) (Δ : Fin (k + 1) → Finset α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j))
    (hcover : ∀ x, x ∈ T ↔ ∃ i, x ∈ Δ i)
    {x : α} (hxT : x ∈ T)
    {i j : Fin (k + 1)} (hxi : x ∈ Δ i) (hxj : x ∈ Δ j) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj i j hij) hxi hxj

/-- Two nested chains with the same cardinality vector are carried to one
another by a permutation of the ground set, obtained by matching the disjoint
increment layers. -/
theorem exists_value_perm_maps_chain
    {p k : ℕ} [NeZero p] (hk : 0 < k)
    (T : Finset (ZMod p)) (m : Fin k → ℕ)
    {R R' : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily T m) (hR' : R' ∈ chainFamily T m) :
    ∃ π : Equiv.Perm (ZMod p),
      T.image π = T ∧
      (∀ x ∉ T, π x = x) ∧
      ∀ i, (R i).image π = R' i := by
  classical
  let Δ := chainIncrements T R
  let Γ := chainIncrements T R'
  have hΔmem := chainIncrements_mem hk T m hR
  have hΓmem := chainIncrements_mem hk T m hR'
  have hΔdata := (Finset.mem_filter.mp hΔmem).2.1
  have hΓdata := (Finset.mem_filter.mp hΓmem).2.1
  have hΔdisj := (Finset.mem_filter.mp hΔmem).2.2.1
  have hΓdisj := (Finset.mem_filter.mp hΓmem).2.2.1
  have hΔcover := (Finset.mem_filter.mp hΔmem).2.2.2
  have hΓcover := (Finset.mem_filter.mp hΓmem).2.2.2
  let idxΔ : {x // x ∈ T} → Fin (k + 1) :=
    fun x => Classical.choose ((hΔcover x.1).1 x.2)
  let idxΓ : {x // x ∈ T} → Fin (k + 1) :=
    fun x => Classical.choose ((hΓcover x.1).1 x.2)
  have hidxΔ : ∀ x : {x // x ∈ T}, x.1 ∈ Δ (idxΔ x) :=
    fun x => Classical.choose_spec ((hΔcover x.1).1 x.2)
  have hidxΓ : ∀ x : {x // x ∈ T}, x.1 ∈ Γ (idxΓ x) :=
    fun x => Classical.choose_spec ((hΓcover x.1).1 x.2)
  have huniqΔ :
      ∀ x : {x // x ∈ T}, ∀ i, x.1 ∈ Δ i → idxΔ x = i := by
    intro x i hxi
    exact partition_member_unique T Δ hΔdisj hΔcover x.2
      (hidxΔ x) hxi
  have huniqΓ :
      ∀ x : {x // x ∈ T}, ∀ i, x.1 ∈ Γ i → idxΓ x = i := by
    intro x i hxi
    exact partition_member_unique T Γ hΓdisj hΓcover x.2
      (hidxΓ x) hxi
  let e : ∀ i : Fin (k + 1),
      {x // x ∈ Δ i} ≃ {x // x ∈ Γ i} :=
    fun i => Fintype.equivOfCardEq (by
      simp only [Fintype.card_coe]
      rw [(hΔdata i).2,(hΓdata i).2])
  let fT : {x // x ∈ T} → {x // x ∈ T} := fun x =>
    let i := idxΔ x
    let y := e i ⟨x.1,hidxΔ x⟩
    ⟨y.1,(hΓdata i).1 y.2⟩
  let gT : {x // x ∈ T} → {x // x ∈ T} := fun y =>
    let i := idxΓ y
    let x := (e i).symm ⟨y.1,hidxΓ y⟩
    ⟨x.1,(hΔdata i).1 x.2⟩
  have hleft : Function.LeftInverse gT fT := by
    intro x
    apply Subtype.ext
    let i := idxΔ x
    have hfmem : (fT x).1 ∈ Γ i := by
      dsimp [fT,i]
      exact (e i ⟨x.1,hidxΔ x⟩).2
    have hidx : idxΓ (fT x) = i := huniqΓ (fT x) i hfmem
    dsimp [gT]
    rw [hidx]
    dsimp [fT,i]
    simp
  have hright : Function.RightInverse gT fT := by
    intro y
    apply Subtype.ext
    let i := idxΓ y
    have hgmem : (gT y).1 ∈ Δ i := by
      dsimp [gT,i]
      exact ((e i).symm ⟨y.1,hidxΓ y⟩).2
    have hidx : idxΔ (gT y) = i := huniqΔ (gT y) i hgmem
    dsimp [fT]
    rw [hidx]
    dsimp [gT,i]
    simp
  let eT : {x // x ∈ T} ≃ {x // x ∈ T} :=
    { toFun := fT, invFun := gT, left_inv := hleft, right_inv := hright }
  let π : Equiv.Perm (ZMod p) :=
    { toFun := fun x =>
        if hx : x ∈ T then (eT ⟨x,hx⟩).1 else x
      invFun := fun y =>
        if hy : y ∈ T then (eT.symm ⟨y,hy⟩).1 else y
      left_inv := by
        intro x
        by_cases hx : x ∈ T
        · have hy : (eT ⟨x,hx⟩).1 ∈ T := (eT ⟨x,hx⟩).2
          simp [hx,hy,eT]
        · simp [hx]
      right_inv := by
        intro y
        by_cases hy : y ∈ T
        · have hx : (eT.symm ⟨y,hy⟩).1 ∈ T :=
            (eT.symm ⟨y,hy⟩).2
          simp [hy,hx,eT]
        · simp [hy] }
  have hπT : T.image π = T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      simp [π,hx,(eT ⟨x,hx⟩).2]
    · intro hy
      let x := (eT.symm ⟨y,hy⟩).1
      have hx : x ∈ T := (eT.symm ⟨y,hy⟩).2
      refine Finset.mem_image.mpr ⟨x,hx,?_⟩
      simp [π,x,hx,hy,eT]
  have hπout : ∀ x ∉ T, π x = x := by
    intro x hx
    simp [π,hx]
  have hΔΓ : ∀ j : Fin (k + 1), (Δ j).image π = Γ j := by
    intro j
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxT := (hΔdata j).1 hx
      have hidx : idxΔ ⟨x,hxT⟩ = j :=
        huniqΔ ⟨x,hxT⟩ j hx
      simp [π,hxT,eT,fT,hidx]
    · intro hy
      have hyT := (hΓdata j).1 hy
      let xsub := (e j).symm ⟨y,hy⟩
      have hx : xsub.1 ∈ Δ j := xsub.2
      have hxT := (hΔdata j).1 hx
      refine Finset.mem_image.mpr ⟨xsub.1,hx,?_⟩
      have hidx : idxΔ ⟨xsub.1,hxT⟩ = j :=
        huniqΔ ⟨xsub.1,hxT⟩ j hx
      simp [π,hxT,eT,fT,hidx,xsub]
  refine ⟨π,hπT,hπout,?_⟩
  intro i
  rw [← chain_prefix_union_eq hk T hR i,
      ← chain_prefix_union_eq hk T hR' i]
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x,hx,rfl⟩
    simp at hx
    rcases hx with ⟨j,hji,hxj⟩
    have himg : π x ∈ Γ ⟨j,by omega⟩ := by
      rw [← hΔΓ ⟨j,by omega⟩]
      exact Finset.mem_image.mpr ⟨x,hxj,rfl⟩
    simp
    exact ⟨j,hji,himg⟩
  · intro hy
    simp at hy
    rcases hy with ⟨j,hji,hyj⟩
    rw [← hΔΓ ⟨j,by omega⟩] at hyj
    rcases Finset.mem_image.mp hyj with ⟨x,hx,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨x,?_,rfl⟩
    simp
    exact ⟨j,hji,hx⟩

/-- After fixing the values on F, the images of fixed nested unexposed index
sets are uniformly distributed over nested chains of the prescribed sizes in
the remaining ground set. -/
theorem conditional_nested_images_chainMass {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (I : Fin k → Finset (Fin S.card))
    (hdisj : ∀ i, Disjoint F (I i))
    (hnested : ∀ i j, i ≤ j → I i ⊆ I j)
    (m : Fin k → ℕ) (hcard : ∀ i, (I i).card = m i)
    (z : Fin k → ZMod p) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∀ i, indexSetSum σ (I i) = z i) =
      chainMass (S \ indexImageSet τ F) m z := by
  classical
  by_cases hk : 0 < k
  · let T := S \ indexImageSet τ F
    let Ω := (indexedOrderings S).filter fun σ => AgreesOn F σ τ
    let V := chainFamily T m
    let stat : (Fin S.card → ZMod p) → Fin k → Finset (ZMod p) :=
      fun σ i => indexImageSet σ (I i)
    have hΩ : Ω.Nonempty := by
      refine ⟨τ,?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [indexedOrderings] using hτ, fun i hi => rfl⟩
    have hmap : ∀ σ ∈ Ω, stat σ ∈ V := by
      intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hσmem,hagr⟩
      have hσord : IsIndexedOrdering S σ := by
        simpa [indexedOrderings] using (Finset.mem_filter.mp hσmem).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro i
        constructor
        · exact unexposed_indexImage_subset_remaining
            S τ σ hτ hσord F (I i) hagr (hdisj i)
        · unfold stat indexImageSet
          rw [Finset.card_image_iff.mpr hσord.1,hcard i]
      · intro i j hij
        unfold stat indexImageSet
        exact Finset.image_mono (hnested i j hij)
    have hV : V.Nonempty := by
      have hTcard :
          ∀ i, m i ≤ T.card := by
        intro i
        have hsub := unexposed_indexImage_subset_remaining
          S τ τ hτ hτ F (I i) (fun _ _ => rfl) (hdisj i)
        have hc := Finset.card_le_card hsub
        rw [show (indexImageSet τ (I i)).card = (I i).card by
          unfold indexImageSet
          exact Finset.card_image_iff.mpr hτ.1,hcard i] at hc
        exact hc
      exact ⟨stat τ, hmap τ (by
        apply Finset.mem_filter.mpr
        exact ⟨by simpa [indexedOrderings] using hτ,fun _ _ => rfl⟩)⟩
    have heq :
        ∀ R ∈ V, ∀ R' ∈ V,
          (Ω.filter fun σ => stat σ = R).card =
            (Ω.filter fun σ => stat σ = R').card := by
      intro R hR R' hR'
      obtain ⟨π,hπT,hπout,hπchain⟩ :=
        exists_value_perm_maps_chain hk T m hR hR'
      have hfixE :
          ∀ x ∈ indexImageSet τ F, π x = x := by
        intro x hx
        exact hπout x (by
          intro hxT
          exact (Finset.mem_sdiff.mp hxT).2 hx)
      have hπS : S.image π = S := by
        ext x
        by_cases hxE : x ∈ indexImageSet τ F
        · have hfix := hfixE x hxE
          simp [hfix,(exposedImage_subset S hτ F hxE)]
        · have hxT : x ∈ T ↔ x ∈ S := by simp [T,hxE]
          rw [← hπT]
          constructor
          · rintro ⟨y,hy,rfl⟩
            exact Finset.mem_image.mpr ⟨y,hxT.mp hy,rfl⟩
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
            exact Finset.mem_image.mpr
              ⟨y,(by
                apply Finset.mem_sdiff.mpr
                refine ⟨hy,?_⟩
                intro hyE
                have hyfix := hfixE y hyE
                have : π y = y := hyfix
                subst x
                exact hxE hyE),rfl⟩
      apply Finset.card_bij (fun σ _ => applyValuePerm π σ)
      · intro σ hσ
        rcases Finset.mem_filter.mp hσ with ⟨hσΩ,hstat⟩
        rcases Finset.mem_filter.mp hσΩ with ⟨hσmem,hagr⟩
        have hσord : IsIndexedOrdering S σ := by
          simpa [indexedOrderings] using (Finset.mem_filter.mp hσmem).2
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          exact ⟨by simpa [indexedOrderings] using
              applyValuePerm_isIndexedOrdering S π hπS hσord,
            valuePerm_preserves_agreement S τ σ F π hfixE hagr⟩
        · funext i
          unfold stat
          rw [indexImageSet_applyValuePerm,hstat]
          exact hπchain i
      · intro σ hσ ρ hρ he
        funext i
        apply π.injective
        exact congrFun he i
      · intro ρ hρ
        let σ := applyValuePerm π.symm ρ
        refine ⟨σ,?_,?_⟩
        · rcases Finset.mem_filter.mp hρ with ⟨hρΩ,hstat⟩
          rcases Finset.mem_filter.mp hρΩ with ⟨hρmem,hagr⟩
          have hρord : IsIndexedOrdering S ρ := by
            simpa [indexedOrderings] using (Finset.mem_filter.mp hρmem).2
          have hπsymS : S.image π.symm = S := by
            apply Finset.image_injective π.injective
            simpa using congrArg (Finset.image π) hπS
          have hfixEsym :
              ∀ x ∈ indexImageSet τ F, π.symm x = x := by
            intro x hx
            exact perm_symm_fixes_of_fixes π (hfixE x hx)
          apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_filter.mpr
            exact ⟨by simpa [indexedOrderings,σ] using
                applyValuePerm_isIndexedOrdering S π.symm hπsymS hρord,
              valuePerm_preserves_agreement S τ ρ F π.symm hfixEsym hagr⟩
          · funext i
            unfold stat
            rw [indexImageSet_applyValuePerm,hstat]
            apply Finset.image_injective π.injective
            simpa using congrArg (Finset.image π.symm) (hπchain i)
        · funext i
          simp [σ,applyValuePerm]
    have huniform :
        uniformMass Ω
          (fun σ => ∀ i, subsetSum (stat σ i) = z i) =
        uniformMass V
          (fun R => ∀ i, subsetSum (R i) = z i) :=
      uniformMass_statistic_of_pairwise_equal_fibers
        Ω V stat hmap hV hΩ heq
        (fun R => ∀ i, subsetSum (R i) = z i)
    unfold orderingConditionalMass chainMass uniformConditionalMass
    rw [← huniform]
    apply uniformMass_congr
    intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨hσmem,hagr⟩
    have hσord : IsIndexedOrdering S σ := by
      simpa [indexedOrderings] using (Finset.mem_filter.mp hσmem).2
    constructor <;> intro h i
    · rw [indexSetSum_eq_subsetSum_image hσord.1]
      exact h i
    · rw [indexSetSum_eq_subsetSum_image hσord.1] at h
      exact h i
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simp [orderingConditionalMass,chainMass,chainFamily]

/-- Conditioning on a window gives the obvious complement cardinality. -/
theorem exposed_image_card {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    (indexImageSet τ F).card = F.card := by
  unfold indexImageSet
  exact Finset.card_image_iff.mpr hτ.1

def agreementKey {n p : ℕ}
    (F : Finset (Fin n)) (σ : Fin n → ZMod p) :
    Fin n → Option (ZMod p) :=
  fun i => if i ∈ F then some (σ i) else none

theorem agreementKey_eq_iff {n p : ℕ}
    (F : Finset (Fin n)) (σ τ : Fin n → ZMod p) :
    agreementKey F σ = agreementKey F τ ↔
      AgreesOn F σ τ := by
  constructor
  · intro h i hi
    have hval := congrFun h i
    simpa [agreementKey,hi] using hval
  · intro h
    funext i
    by_cases hi : i ∈ F
    · simp [agreementKey,hi,h i hi]
    · simp [agreementKey,hi]

/-- A uniform bound on every exposed-value fiber is also an unconditional bound. -/
theorem event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E]
    (q : ℝ)
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) E ≤ q) :
    orderingEventMass S E ≤ q := by
  let key := agreementKey F
  have hq0 : 0 ≤ q := by
    obtain ⟨τ,hτmem⟩ := indexedOrderings_nonempty S
    have hτ : IsIndexedOrdering S τ := by
      simpa [indexedOrderings] using
        (Finset.mem_filter.mp hτmem).2
    exact le_trans (uniformMass_nonneg _ _) (hfiber τ hτ)
  have h :=
    uniformConditionalMass_le_of_fibers
      (indexedOrderings S) key (fun _ => True) E q hq0
      (by
        intro κ hκ
        by_cases hnon :
            ((indexedOrderings S).filter fun σ => key σ = κ).Nonempty
        · obtain ⟨τ,hτfib⟩ := hnon
          rcases Finset.mem_filter.mp hτfib with ⟨hτmem,hτkey⟩
          have hτ : IsIndexedOrdering S τ := by
            simpa [indexedOrderings] using
              (Finset.mem_filter.mp hτmem).2
          have heq :
              (fun σ => key σ = κ) =
                (fun σ => AgreesOn F σ τ) := by
            funext σ
            apply propext
            rw [← agreementKey_eq_iff]
            exact ⟨fun h => h.trans hτkey.symm,
              fun h => h.trans hτkey⟩
          rw [heq]
          simpa [orderingConditionalMass] using hfiber τ hτ
        · have hemp :
              (indexedOrderings S).filter (fun σ => key σ = κ) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hnon
          unfold uniformConditionalMass
          simp [hemp])
  simpa [orderingEventMass,uniformConditionalMass,key] using h

/-- Fiber multiplication specialized to exposing a set of positions in a
uniform random ordering. -/
theorem joint_event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (A B : (Fin S.card → ZMod p) → Prop)
    [DecidablePred A] [DecidablePred B]
    (a b : ℝ)
    (hA : orderingEventMass S A ≤ a)
    (hdetermined :
      ∀ σ τ, AgreesOn F σ τ → (A σ ↔ A τ))
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ → A τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) B ≤ b) :
    orderingEventMass S (fun σ => A σ ∧ B σ) ≤ a * b := by
  have ha0 : 0 ≤ a :=
    le_trans (uniformMass_nonneg _ _) hA
  unfold orderingEventMass
  rw [uniformMass_chain_rule]
  have hcond :
      uniformConditionalMass (indexedOrderings S) A B ≤ b := by
    by_cases hAspace : ((indexedOrderings S).filter A).Nonempty
    · obtain ⟨τ₀,hτ₀A⟩ := hAspace
      rcases Finset.mem_filter.mp hτ₀A with ⟨hτ₀mem,hAτ₀⟩
      have hτ₀ : IsIndexedOrdering S τ₀ := by
        simpa [indexedOrderings] using
          (Finset.mem_filter.mp hτ₀mem).2
      have hb0 : 0 ≤ b :=
        le_trans (uniformMass_nonneg _ _) (hfiber τ₀ hτ₀ hAτ₀)
      let key := agreementKey F
      let spaceA := (indexedOrderings S).filter A
      have htotal :=
        uniformConditionalMass_le_of_fibers
          spaceA key (fun _ => True) B b hb0
          (by
            intro κ hκ
            by_cases hnon :
                (spaceA.filter fun σ => key σ = κ).Nonempty
            · obtain ⟨τ,hτfib⟩ := hnon
              rcases Finset.mem_filter.mp hτfib with ⟨hτA,hτkey⟩
              rcases Finset.mem_filter.mp hτA with ⟨hτmem,hAτ⟩
              have hτ : IsIndexedOrdering S τ := by
                simpa [indexedOrderings] using
                  (Finset.mem_filter.mp hτmem).2
              have heq :
                  spaceA.filter (fun σ => key σ = κ) =
                    (indexedOrderings S).filter
                      (fun σ => AgreesOn F σ τ) := by
                ext σ
                constructor
                · intro hσ
                  rcases Finset.mem_filter.mp hσ with ⟨hσA,hσkey⟩
                  rcases Finset.mem_filter.mp hσA with ⟨hσmem,hAσ⟩
                  apply Finset.mem_filter.mpr
                  refine ⟨hσmem,?_⟩
                  rw [← agreementKey_eq_iff]
                  exact hσkey.trans hτkey.symm
                · intro hσ
                  rcases Finset.mem_filter.mp hσ with ⟨hσmem,hagr⟩
                  have hAσ := (hdetermined σ τ hagr).2 hAτ
                  apply Finset.mem_filter.mpr
                  constructor
                  · exact Finset.mem_filter.mpr ⟨hσmem,hAσ⟩
                  · rw [← agreementKey_eq_iff] at hagr
                    exact hagr.trans hτkey
              unfold uniformConditionalMass
              rw [heq]
              simpa [orderingConditionalMass] using
                hfiber τ hτ hAτ
            · have hemp :
                  spaceA.filter (fun σ => key σ = κ) = ∅ :=
                Finset.not_nonempty_iff_eq_empty.mp hnon
              unfold uniformConditionalMass
              simp [hemp])
      simpa [uniformConditionalMass,spaceA,key] using htotal
    · have hemp :
          (indexedOrderings S).filter A = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hAspace
      unfold uniformConditionalMass
      simp [hemp]
  exact mul_le_mul hA hcond (uniformMass_nonneg _ _) ha0

/-- Union bound over a finite set of possible parameter records. -/
theorem finite_parameter_union_bound
    {Ω Θ : Type*} [DecidableEq Ω] [DecidableEq Θ]
    (space : Finset Ω) (params : Finset Θ)
    (E : Θ → Ω → Prop) [∀ θ, DecidablePred (E θ)] :
    uniformMass space (fun ω => ∃ θ ∈ params, E θ ω) ≤
      ∑ θ ∈ params, uniformMass space (E θ) :=
  uniformMass_exists_le_sum space params E

/-- Union bound in witness form: if every occurrence of E supplies a parameter
θ and the θ-event has mass at most q, then E has mass at most |params| q. -/
theorem witness_union_bound
    {Ω Θ : Type*} [DecidableEq Ω] [DecidableEq Θ]
    (space : Finset Ω) (params : Finset Θ)
    (E : Ω → Prop) (A : Θ → Ω → Prop)
    [DecidablePred E] [∀ θ, DecidablePred (A θ)]
    (q : ℝ)
    (hcover : ∀ ω ∈ space, E ω → ∃ θ ∈ params, A θ ω)
    (hbound : ∀ θ ∈ params, uniformMass space (A θ) ≤ q) :
    uniformMass space E ≤ (params.card : ℝ) * q := by
  have hmono :
      uniformMass space E ≤
        uniformMass space (fun ω => ∃ θ ∈ params, A θ ω) := by
    apply uniformMass_mono_on
    intro ω hω hE
    exact hcover ω hω hE
  calc
    uniformMass space E
      ≤ uniformMass space (fun ω => ∃ θ ∈ params, A θ ω) := hmono
    _ ≤ ∑ θ ∈ params, uniformMass space (A θ) :=
      finite_parameter_union_bound space params A
    _ ≤ ∑ _θ ∈ params, q := by
      gcongr with θ hθ
      exact hbound θ hθ
    _ = (params.card : ℝ) * q := by simp [mul_comm]

window yield a least point b₀ and D further distinct points in the following 20D
window. -/
theorem dense_window_extract {n D : ℕ}
    (B : Finset (Fin n)) (hD : 0 < D)
    (h : ∃ z : Fin n,
      D < (B ∩ symmetricWindow z (10 * D)).card) :
    ∃ b₀ ∈ B, ∃ b : Fin D → Fin n,
      Function.Injective b ∧
      (∀ i, b i ∈ B) ∧
      (∀ i, paperPos b₀ < paperPos (b i) ∧
        paperPos (b i) ≤ paperPos b₀ + 20 * D) := by
  classical
  obtain ⟨z,hz⟩ := h
  let T := B ∩ symmetricWindow z (10 * D)
  have hT : T.Nonempty := by
    exact Finset.card_pos.mp (lt_trans hD hz)
  let b₀ := T.min' hT
  have hb₀T : b₀ ∈ T := T.min'_mem hT
  have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀T).1
  let U := T.erase b₀
  have hUcard : D ≤ U.card := by
    rw [Finset.card_erase_of_mem hb₀T]
    omega
  obtain ⟨b,hbinj,hbU⟩ := exists_injective_fin_enum U D hUcard
  refine ⟨b₀,hb₀B,b,hbinj,?_,?_⟩
  · intro i
    exact (Finset.mem_inter.mp
      (Finset.mem_of_mem_erase (hbU i))).1
  · intro i
    have hbiT : b i ∈ T :=
      Finset.mem_of_mem_erase (hbU i)
    have hbine : b i ≠ b₀ := Finset.ne_of_mem_erase (hbU i)
    have hmin : b₀ ≤ b i := T.min'_le _ hbiT
    have hlt : b₀ < b i := lt_of_le_of_ne hmin (Ne.symm hbine)
    have hb0W := (Finset.mem_inter.mp hb₀T).2
    have hbiW := (Finset.mem_inter.mp hbiT).2
    simp only [symmetricWindow, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb0W hbiW
    constructor
    · simpa [paperPos] using hlt
    · simp [Nat.dist_eq,paperPos] at hb0W hbiW ⊢
      omega

theorem disjoint_swaps_commute_general {α : Type*} [DecidableEq α]
    (a b c d : α)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) := by
  by_cases hab : a = b
  · subst b; simp
  by_cases hcd : c = d
  · subst d; simp
  ext x
  by_cases hxa : x = a
  · subst x; simp [hab,hcd,hac,had,hbc,hbd]
  by_cases hxb : x = b
  · subst x; simp [hab,hcd,hac,had,hbc,hbd]
  by_cases hxc : x = c
  · subst x; simp [hab,hcd,hac,had,hbc,hbd]
  by_cases hxd : x = d
  · subst x; simp [hab,hcd,hac,had,hbc,hbd]
  simp [Equiv.swap_apply_of_ne_of_ne,hxa,hxb,hxc,hxd]

theorem disjoint_swaps_commute {α : Type*} [DecidableEq α]
    (a b c d : α)
    (_hab : a ≠ b) (_hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) :=
  disjoint_swaps_commute_general a b c d hac had hbc hbd

theorem disjoint_swaps_fix_outside_support
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (_hP : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (i : α)
    (hi : ∀ q ∈ P, i ≠ q.1 ∧ i ≠ q.2) :
    swapsPermList P.toList i = i := by
  induction P.toList with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      have hq : q ∈ P := by simpa using P.mem_toList q
      have hqi := hi q hq
      have hrest : ∀ r ∈ qs, i ≠ r.1 ∧ i ≠ r.2 := by
        intro r hr
        exact hi r (by
          have : r ∈ P.toList := by simp [hr]
          simpa using this)
      simp [swapsPermList,Equiv.swap_apply_of_ne_of_ne hqi.1 hqi.2,
        ih hrest]

theorem nodup_lists_perm_of_toFinset_eq {α : Type*} [DecidableEq α]
    {l r : List α} (hl : l.Nodup) (hr : r.Nodup)
    (hset : l.toFinset = r.toFinset) :
    l.Perm r := by
  apply List.perm_ext_iff_of_nodup hl hr |>.2
  intro x
  simpa [hset]

theorem swapsPermList_eq_of_perm_pairwise
    {α : Type*} [DecidableEq α]
    {l r : List (α × α)}
    (hp : l.Perm r)
    (hpair : l.toFinset.toSet.Pairwise fun q s =>
      q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2) :
    swapsPermList l = swapsPermList r := by
  induction hp with
  | nil => rfl
  | @cons a l r hp ih =>
      have hsub :
          l.toFinset.toSet.Pairwise fun q s =>
            q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2 :=
        hpair.mono (by intro q hq; simp at hq ⊢; exact Or.inr hq)
      simp [swapsPermList,ih hsub]
  | @swap a b l =>
      by_cases hab : a = b
      · subst b; rfl
      have ha : a ∈ (a :: b :: l).toFinset := by simp
      have hb : b ∈ (a :: b :: l).toFinset := by simp
      have hd := hpair ha hb hab
      have hcomm := disjoint_swaps_commute_general
        a.1 a.2 b.1 b.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      simp only [swapsPermList]
      rw [hcomm]
  | @trans l r s h₁ h₂ ih₁ ih₂ =>
      have hset : r.toFinset = l.toFinset := by
        ext x
        simpa using h₁.mem_iff.symm
      have hpairR :
          r.toFinset.toSet.Pairwise fun q t =>
            q.1 ≠ t.1 ∧ q.1 ≠ t.2 ∧ q.2 ≠ t.1 ∧ q.2 ≠ t.2 := by
        simpa [hset] using hpair
      exact (ih₁ hpair).trans (ih₂ hpairR)

theorem disjoint_swaps_order_independent
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (l : List (α × α)) (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = swapsPermList P.toList := by
  have hp := nodup_lists_perm_of_toFinset_eq hln P.nodup_toList
    (by simpa [hl])
  apply swapsPermList_eq_of_perm_pairwise hp
  simpa [hl] using hP

theorem swapsPermList_pair_action
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P : Finset (α × α))
    (hPpair : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hord : ∀ q ∈ P, q.1 < q.2)
    {q : α × α} (hq : q ∈ P) :
    swapsPermList P.toList q.1 = q.2 ∧
      swapsPermList P.toList q.2 = q.1 := by
  let l := q :: (P.erase q).toList
  have hln : l.Nodup := by simp [l]
  have hset : l.toFinset = P := by simp [l,hq]
  have horder :=
    disjoint_swaps_order_independent P hPpair l hset hln
  have hrest1 :
      swapsPermList (P.erase q).toList q.1 = q.1 := by
    apply disjoint_swaps_fix_outside_support (P.erase q)
    · exact hPpair.mono (by intro a ha; exact Finset.mem_of_mem_erase ha)
    · intro r hr
      have hrP := Finset.mem_of_mem_erase hr
      have hrne : r ≠ q := Finset.ne_of_mem_erase hr
      have hd := hPpair hrP hq hrne
      exact ⟨hd.1,hd.2.1⟩
  have hrest2 :
      swapsPermList (P.erase q).toList q.2 = q.2 := by
    apply disjoint_swaps_fix_outside_support (P.erase q)
    · exact hPpair.mono (by intro a ha; exact Finset.mem_of_mem_erase ha)
    · intro r hr
      have hrP := Finset.mem_of_mem_erase hr
      have hrne : r ≠ q := Finset.ne_of_mem_erase hr
      have hd := hPpair hrP hq hrne
      exact ⟨hd.2.2.1,hd.2.2.2⟩
  have hqne : q.1 ≠ q.2 := ne_of_lt (hord q hq)
  constructor
  · rw [← horder]
    simp [l,swapsPermList,hqne,hrest2]
  · rw [← horder]
    simp [l,swapsPermList,hqne,hrest1]

theorem disjoint_swaps_reconstruct
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P Q : Finset (α × α))
    (hPpair : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hQpair : Q.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hPord : ∀ q ∈ P, q.1 < q.2)
    (hQord : ∀ q ∈ Q, q.1 < q.2)
    (hperm : swapsPermList P.toList = swapsPermList Q.toList) :
    P = Q := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hactP := swapsPermList_pair_action P hPpair hPord hq
    have hmoveQ : swapsPermList Q.toList q.1 = q.2 := by
      rw [← hperm]
      exact hactP.1
    by_contra hqQ
    have hqne : q.1 ≠ q.2 := ne_of_lt (hPord q hq)
    have hsupport : ∃ r ∈ Q, q.1 = r.1 ∨ q.1 = r.2 := by
      by_contra hnone
      push_neg at hnone
      have hfix :=
        disjoint_swaps_fix_outside_support Q hQpair q.1
          (by intro r hr; exact ⟨(hnone r hr).1,(hnone r hr).2⟩)
      rw [hfix] at hmoveQ
      exact hqne hmoveQ
    rcases hsupport with ⟨r,hr,hr1 | hr2⟩
    · have hactQ := swapsPermList_pair_action Q hQpair hQord hr
      have hsnd : r.2 = q.2 := by
        rw [hr1] at hactQ
        rw [hactQ.1] at hmoveQ
        exact hmoveQ.symm
      have heq : r = q := Prod.ext hr1.symm hsnd
      exact hqQ (heq ▸ hr)
    · have hactQ := swapsPermList_pair_action Q hQpair hQord hr
      have hfst : r.1 = q.2 := by
        rw [hr2] at hactQ
        rw [hactQ.2] at hmoveQ
        exact hmoveQ
      have hrord := hQord r hr
      have hqord := hPord q hq
      rw [hr2,hfst] at hrord
      exact (not_lt_of_ge (le_of_lt hqord)) hrord
  · intro q hq
    have hsym := hperm.symm
    have hactQ := swapsPermList_pair_action Q hQpair hQord hq
    have hmoveP : swapsPermList P.toList q.1 = q.2 := by
      rw [← hsym]
      exact hactQ.1
    by_contra hqP
    have hqne : q.1 ≠ q.2 := ne_of_lt (hQord q hq)
    have hsupport : ∃ r ∈ P, q.1 = r.1 ∨ q.1 = r.2 := by
      by_contra hnone
      push_neg at hnone
      have hfix :=
        disjoint_swaps_fix_outside_support P hPpair q.1
          (by intro r hr; exact ⟨(hnone r hr).1,(hnone r hr).2⟩)
      rw [hfix] at hmoveP
      exact hqne hmoveP
    rcases hsupport with ⟨r,hr,hr1 | hr2⟩
    · have hactP := swapsPermList_pair_action P hPpair hPord hr
      have hsnd : r.2 = q.2 := by
        rw [hr1] at hactP
        rw [hactP.1] at hmoveP
        exact hmoveP.symm
      have heq : r = q := Prod.ext hr1.symm hsnd
      exact hqP (heq ▸ hr)
    · have hactP := swapsPermList_pair_action P hPpair hPord hr
      have hfst : r.1 = q.2 := by
        rw [hr2] at hactP
        rw [hactP.2] at hmoveP
        exact hmoveP
      have hrord := hPord r hr
      have hqord := hQord q hq
      rw [hr2,hfst] at hrord
      exact (not_lt_of_ge (le_of_lt hqord)) hrord

theorem swapsPermList_append {n : ℕ}
    (l r : List (Fin n × Fin n)) :
    swapsPermList (l ++ r) =
      (swapsPermList l).trans (swapsPermList r) := by
  induction l with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      simp [swapsPermList,ih,Equiv.trans_assoc]

theorem swap_image_eq_self_of_not_crosses {n : ℕ}
    (q : Fin n × Fin n) (I : Finset (Fin n))
    (hnot : ¬ SwapCrosses q I) :
    I.image (Equiv.swap q.1 q.2) = I := by
  by_cases heq : q.1 = q.2
  · rcases q with ⟨a,b⟩
    simp only at heq
    subst b
    simp
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    by_cases hy1 : y = q.1
    · subst y
      have hq2I : q.2 ∈ I := by
        by_contra hq2
        exact hnot (Or.inl ⟨hy,hq2⟩)
      simpa [Equiv.swap_apply_left heq] using hq2I
    · by_cases hy2 : y = q.2
      · subst y
        have hq1I : q.1 ∈ I := by
          by_contra hq1
          exact hnot (Or.inr ⟨hq1,hy⟩)
        simpa [Equiv.swap_apply_right heq] using hq1I
      · simpa [Equiv.swap_apply_of_ne_of_ne hy1 hy2] using hy
  · intro hx
    by_cases hx1 : x = q.1
    · subst x
      have hq2I : q.2 ∈ I := by
        by_contra hq2
        exact hnot (Or.inl ⟨hx,hq2⟩)
      exact Finset.mem_image.mpr
        ⟨q.2,hq2I,by simp [Equiv.swap_apply_right heq]⟩
    · by_cases hx2 : x = q.2
      · subst x
        have hq1I : q.1 ∈ I := by
          by_contra hq1
          exact hnot (Or.inr ⟨hq1,hx⟩)
        exact Finset.mem_image.mpr
          ⟨q.1,hq1I,by simp [Equiv.swap_apply_left heq]⟩
      · exact Finset.mem_image.mpr
          ⟨x,hx,by simp [Equiv.swap_apply_of_ne_of_ne hx1 hx2]⟩

theorem swapsPermList_image_eq_self
    {n : ℕ} (l : List (Fin n × Fin n))
    (I : Finset (Fin n))
    (hnot : ∀ q ∈ l, ¬ SwapCrosses q I) :
    I.image (swapsPermList l) = I := by
  induction l with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      have hqnot := hnot q (by simp)
      have hnot' : ∀ r ∈ qs, ¬ SwapCrosses r I := by
        intro r hr; exact hnot r (by simp [hr])
      rw [show swapsPermList (q::qs) =
          (Equiv.swap q.1 q.2).trans (swapsPermList qs) by rfl]
      rw [Finset.image_image]
      rw [swap_image_eq_self_of_not_crosses q I hqnot]
      exact ih hnot'

/-- Delete swaps crossing none of the constrained index sets.  The deleted
swaps preserve every constrained set, and pairwise-disjoint transpositions
commute, so all constrained images are unchanged. -/
theorem trim_irrelevant_disjoint_swaps
    {n k : ℕ} (P : Finset (Fin n × Fin n))
    (hP : P.toSet.Pairwise swapPairsDisjoint)
    (I : Fin k → Finset (Fin n)) :
    ∃ P' ⊆ P,
      P'.toSet.Pairwise swapPairsDisjoint ∧
      (∀ q ∈ P', ∃ i, ((q.1 ∈ I i) ↔ q.2 ∉ I i)) ∧
      ∀ i, (I i).image (collectionPerm P') =
        (I i).image (collectionPerm P) := by
  classical
  let crosses : Fin n × Fin n → Prop :=
    fun q => ∃ i, SwapCrosses q (I i)
  let P' := P.filter crosses
  let R := P.filter fun q => ¬ crosses q
  have hP'sub : P' ⊆ P := Finset.filter_subset _ _
  have hRsub : R ⊆ P := Finset.filter_subset _ _
  have hP'disj : P'.toSet.Pairwise swapPairsDisjoint :=
    hP.mono (by intro q hq; exact hP'sub hq)
  have hdisjSets : Disjoint R P' := by
    rw [Finset.disjoint_left]
    intro q hqR hqP
    exact (Finset.mem_filter.mp hqR).2
      (Finset.mem_filter.mp hqP).2
  have hunion : R ∪ P' = P := by
    ext q
    by_cases hq : crosses q <;> simp [R,P',hq]
  refine ⟨P',hP'sub,hP'disj,?_,?_⟩
  · intro q hq
    rcases (Finset.mem_filter.mp hq).2 with ⟨i,hi⟩
    refine ⟨i,?_⟩
    rcases hi with h | h
    · exact ⟨fun _ => h.2, fun hnot => h.1⟩
    · exact ⟨fun hmem => False.elim (h.1 hmem), fun _ => h.2⟩
  · intro i
    have hRfix :
        (I i).image (collectionPerm R) = I i := by
      unfold collectionPerm
      apply swapsPermList_image_eq_self R.toList (I i)
      intro q hq
      have hnotCrosses := (Finset.mem_filter.mp
        (show q ∈ R from by simpa using hq)).2
      intro hi
      exact hnotCrosses ⟨i,hi⟩
    have hlistSet :
        (R.toList ++ P'.toList).toFinset = P := by
      simp [hunion]
    have hlistNodup :
        (R.toList ++ P'.toList).Nodup := by
      apply List.Nodup.append R.nodup_toList P'.nodup_toList
      intro q hqR hqP
      exact Finset.disjoint_left.mp hdisjSets
        (by simpa using hqR) (by simpa using hqP)
    have horder :
        swapsPermList (R.toList ++ P'.toList) = collectionPerm P := by
      unfold collectionPerm
      exact disjoint_swaps_order_independent P hP
        (R.toList ++ P'.toList) hlistSet hlistNodup
    rw [← horder,swapsPermList_append,Finset.image_image,hRfix]
    rfl

/-- Sort a finite injective tuple by a permutation of its coordinates. -/
theorem exists_sorting_perm
    {α : Type*} [LinearOrder α] [DecidableEq α] {k : ℕ}
    (x : Fin k → α) (hinj : Function.Injective x) :
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ) := by
  classical
  let X : Finset α := Finset.univ.image x
  have hcard : X.card = k := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [X]
  let ex : Fin k ≃ {a // a ∈ X} :=
    Equiv.ofBijective (fun i => ⟨x i,by
      apply Finset.mem_image.mpr
      exact ⟨i,Finset.mem_univ _,rfl⟩⟩)
      ⟨fun i j h => hinj (Subtype.ext_iff.mp h),
       fun y => by
        rcases Finset.mem_image.mp y.2 with ⟨i,hi,rfl⟩
        exact ⟨i,rfl⟩⟩
  let ord : Fin k ≃o {a // a ∈ X} := X.orderIsoOfFin hcard
  let ρ : Equiv.Perm (Fin k) := ord.toEquiv.trans ex.symm
  refine ⟨ρ,?_⟩
  intro i j hij
  have hord : ord i < ord j := ord.lt_iff_lt.mpr hij
  have hi : x (ρ i) = (ord i).1 := by
    have := ex.apply_symm_apply (ord i)
    exact congrArg Subtype.val this
  have hj : x (ρ j) = (ord j).1 := by
    have := ex.apply_symm_apply (ord j)
    exact congrArg Subtype.val this
  simpa [Function.comp_def,hi,hj] using hord

/-- Generic bookkeeping for summing all increasing prefix-chain constraints after
conditioning on an exposed set. The substantive chain estimate is supplied by
hchain; this axiom only identifies/sums the finite fibers. -/
axiom conditional_prefix_chain_union_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) (cut : Fin S.card)
    (target : Fin k → ZMod p)
    (C : ℝ)
    (hchain :
      ∀ (m : Fin k → ℕ), IsChainSizeTuple
          (S \ indexImageSet τ F).card m →
        ∀ z : Fin k → ZMod p,
          chainMass (S \ indexImageSet τ F) m z ≤
            chainUpperBound p (S \ indexImageSet τ F).card C m) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∃ a : Fin k → Fin S.card,
          StrictMono a ∧
          (∀ i, paperPos (a i) < paperPos cut) ∧
          (∀ i,
            indexSetSum σ (indexHalfOpen (a i) cut) = target i)) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C

/-- If a remaining ground set has size between n/2 and n, the Lemma 4.3 base
is bounded by twice the ambient n^{-α} bound used in Section 5. -/
theorem half_ground_lemma43Base_le
    {n s p : ℕ} {α C : ℝ}
    (hn : 2 ≤ n) (hhalf : n / 2 ≤ s) (hsn : s ≤ n)
    (hCnonneg : 0 ≤ C)
    (hp : (n : ℝ) / p ≤ (n : ℝ) ^ (-α))
    (hC :
      4 * C * Real.sqrt (Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-α)) :
    lemma43Base p s C ≤ 2 * (n : ℝ) ^ (-α) := by
  unfold lemma43Base
  have hnR : 0 < (n : ℝ) := by positivity
  have hsR : 0 < (s : ℝ) := by
    have : 1 ≤ s := by omega
    exact_mod_cast this
  have hsp : (s : ℝ) / p ≤ (n : ℝ) / p := by
    gcongr
  have hlog :
      Real.sqrt (Real.log (s : ℝ)) ≤
        Real.sqrt (Real.log (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact Real.strictMonoOn_log.monotoneOn
      (by positivity) (by exact_mod_cast hsn)
  have hroot :
      Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (s : ℝ) := by
    have hhalfR : (n : ℝ) / 2 ≤ s := by exact_mod_cast hhalf
    have hsqrt :=
      Real.sqrt_le_sqrt (show (n : ℝ) ≤ 4 * s by nlinarith)
    have hs0 := Real.sqrt_nonneg (s : ℝ)
    nlinarith
  have hterm :
      2 * C * Real.sqrt (Real.log (s : ℝ)) /
          Real.sqrt (s : ℝ) ≤
        4 * C * Real.sqrt (Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ) := by
    have hsnlog : 0 ≤ Real.sqrt (Real.log (n : ℝ)) :=
      Real.sqrt_nonneg _
    have hslog : 0 ≤ Real.sqrt (Real.log (s : ℝ)) :=
      Real.sqrt_nonneg _
    have hsroot : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hsR
    have hnroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    apply (div_le_div_iff₀ hsroot hnroot).2
    nlinarith [hlog,hroot,hCnonneg]
  nlinarith [hsp,hp,hterm,hC]

/-- The exponent comparison αD≥3 used in the D-fold chain bounds. -/
theorem two_neg_alpha_pow_le_cube
    {n D : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα0 : 0 < α)
    (hαD : 3 ≤ α * D) :
    (2 * (n : ℝ) ^ (-α)) ^ D ≤
      (2 : ℝ) ^ D / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [mul_pow]
  have hrpow :
      ((n : ℝ) ^ (-α)) ^ D =
        (n : ℝ) ^ (-(α * D)) := by
    rw [← Real.rpow_natCast]
    congr 1
    ring
  rw [hrpow]
  have hexp : -(α * D) ≤ (-3 : ℝ) := by nlinarith
  have hmono :=
    External.rpow_exponent_mono_of_one_le hnR hexp
  have hneg3 :
      (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rfl
  rw [hneg3] at hmono
  nlinarith

/-- Reindex an injective finite family of valid chain-size tuples into the full
sum occurring in Lemma 4.3. -/
theorem chainUpperBound_sum_le_lemma43
    {Θ : Type*} [DecidableEq Θ]
    {p n k : ℕ} (C : ℝ)
    (X : Finset Θ) (m : Θ → Fin k → ℕ)
    (hvalid : ∀ θ ∈ X, IsChainSizeTuple n (m θ))
    (hinj : Set.InjOn m X) :
    (∑ θ ∈ X, chainUpperBound p n C (m θ)) ≤
      lemma43LHS p n k C := by
  unfold lemma43LHS lemma43Summand
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset
  intro μ hμ
  rcases Finset.mem_image.mp hμ with ⟨θ,hθ,rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvalid θ hθ⟩

/-- The right-tail size tuple associated with a strictly increasing tail tuple is
a valid chain-size tuple in the remaining ground set. -/
theorem tailSizes_valid
    {n D s : ℕ}
    (b b' : Fin n)
    (hb2 : 2 ≤ paperPos b)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (x : Fin D → Fin n)
    (hx : x ∈ tailTuples b' D)
    (hs : s = n - (5 * D + 1)) :
    IsChainSizeTuple s (tailSizes b' x) := by
  rcases Finset.mem_filter.mp hx with ⟨_,hmono,habove⟩
  constructor
  · intro i j hij
    unfold tailSizes
    have hxi := hmono hij
    simp only [Fin.mk_lt_mk] at hxi ⊢
    omega
  · intro i
    have habove := habove i
    have hgapv : b'.val - b.val = 5 * D := by
      simpa [paperPos] using hgap
    have hbval : 1 ≤ b.val := by
      simpa [paperPos] using hb2
    unfold tailSizes
    constructor
    · simp [paperPos] at habove
      omega
    · rw [hs]
      simp [paperPos] at habove
      have hxlt := (x i).isLt
      omega

/-- After exposing [b,b'], a fixed right-tail tuple has exactly the nested-chain
law on the remaining values. The bound supplied as hchain is therefore inherited
by the corresponding interval-sum event. -/
axiom fixed_tail_tuple_conditional_chainBound
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (b b' : Fin S.card)
    (u x : Fin D → Fin S.card)
    (πi : Fin D → Equiv.Perm (Fin S.card))
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (C : ℝ)
    (hm : IsChainSizeTuple
      (S \ indexImageSet τ F).card (tailSizes b' x))
    (hchain :
      ∀ z : Fin D → ZMod p,
        chainMass (S \ indexImageSet τ F)
            (tailSizes b' x) z ≤
          chainUpperBound p (S \ indexImageSet τ F).card
            C (tailSizes b' x)) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm σ (πi i))
            (u i) (x i) = 0) ≤
      chainUpperBound p (S \ indexImageSet τ F).card
        C (tailSizes b' x)

/-- Generic two-level witness union bound: for each outer parameter there are
at most M inner choices, each inner event has weight w(theta), and the outer
weights sum to at most B. -/
theorem bounded_choice_witness_union
    {Ω Θ Ξ : Type*} [DecidableEq Ω] [DecidableEq Θ] [DecidableEq Ξ]
    (space : Finset Ω) (outer : Finset Θ)
    (inner : Θ → Finset Ξ)
    (E : Ω → Prop) (A : Θ → Ξ → Ω → Prop)
    [DecidablePred E] [∀ θ ξ, DecidablePred (A θ ξ)]
    (M : ℕ) (w : Θ → ℝ) (B : ℝ)
    (hcover :
      ∀ ω ∈ space, E ω →
        ∃ θ ∈ outer, ∃ ξ ∈ inner θ, A θ ξ ω)
    (hcount : ∀ θ ∈ outer, (inner θ).card ≤ M)
    (hpoint :
      ∀ θ ∈ outer, ∀ ξ ∈ inner θ,
        uniformMass space (A θ ξ) ≤ w θ)
    (hsum : (∑ θ ∈ outer, w θ) ≤ B)
    (hw : ∀ θ ∈ outer, 0 ≤ w θ) :
    uniformMass space E ≤ (M : ℝ) * B := by
  have hmono :
      uniformMass space E ≤
        uniformMass space
          (fun ω => ∃ θ ∈ outer, ∃ ξ ∈ inner θ, A θ ξ ω) := by
    apply uniformMass_mono_on
    intro ω hω hE
    exact hcover ω hω hE
  have houter :=
    uniformMass_exists_le_sum space outer
      (fun θ ω => ∃ ξ ∈ inner θ, A θ ξ ω)
  have hinner :
      ∀ θ ∈ outer,
        uniformMass space (fun ω => ∃ ξ ∈ inner θ, A θ ξ ω) ≤
          (inner θ).card * w θ := by
    intro θ hθ
    calc
      _ ≤ ∑ ξ ∈ inner θ, uniformMass space (A θ ξ) :=
        uniformMass_exists_le_sum space (inner θ) (A θ)
      _ ≤ ∑ _ξ ∈ inner θ, w θ := by
          gcongr with ξ hξ
          exact hpoint θ hθ ξ hξ
      _ = (inner θ).card * w θ := by simp
  calc
    uniformMass space E
      ≤ uniformMass space
          (fun ω => ∃ θ ∈ outer, ∃ ξ ∈ inner θ, A θ ξ ω) := hmono
    _ ≤ ∑ θ ∈ outer,
          uniformMass space (fun ω => ∃ ξ ∈ inner θ, A θ ξ ω) := houter
    _ ≤ ∑ θ ∈ outer, (inner θ).card * w θ := by
          gcongr with θ hθ
          exact hinner θ hθ
    _ ≤ ∑ θ ∈ outer, (M : ℝ) * w θ := by
          gcongr with θ hθ
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hcount θ hθ) (hw θ hθ)
    _ = (M : ℝ) * ∑ θ ∈ outer, w θ := by
          rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * B := by
          gcongr
          positivity

/-- Generic count of disjoint oriented short-swap collections when all first
endpoints lie in Q. Each q∈Q has at most 5D possible partners, plus the option
that no pair starts at q. -/
def shortPartners {n D : ℕ} (q : Fin n) : Finset (Fin n) :=
  (forwardWindow q (5 * D)).erase q

theorem card_shortPartners_le {n D : ℕ} (q : Fin n) :
    (shortPartners (D := D) q).card ≤ 5 * D := by
  unfold shortPartners
  have hq : q ∈ forwardWindow q (5 * D) := by
    simp [forwardWindow]
  rw [Finset.card_erase_of_mem hq]
  have h := card_forwardWindow_le q (5 * D)
  omega

def collectionPartner {n : ℕ}
    (P : Finset (Fin n × Fin n)) (q : Fin n) : Option (Fin n) := by
  classical
  by_cases h : ∃ y, (q,y) ∈ P
  · exact some (Classical.choose h)
  · exact none

theorem collectionPartner_eq_some_iff
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (q y : Fin n) :
    collectionPartner P q = some y ↔ (q,y) ∈ P := by
  classical
  unfold collectionPartner
  by_cases h : ∃ z, (q,z) ∈ P
  · let z := Classical.choose h
    have hz : (q,z) ∈ P := Classical.choose_spec h
    simp [h]
    constructor
    · intro hy
      injection hy with hyz
      subst y
      exact hz
    · intro hy
      by_contra hne
      have hpairs := hP.1 hz hy (by
        intro heq
        injection heq with _ heq2
        exact hne heq2.symm)
      exact hpairs.1 rfl
  · simp [h]

theorem collectionPartner_mem_allowed
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {Q : Finset (Fin n)}
    (hsupp : ∀ r ∈ P, r.1 ∈ Q)
    (q : {x // x ∈ Q}) :
    collectionPartner P q.1 ∈
      insert none ((shortPartners (D := D) q.1).image some) := by
  classical
  cases h : collectionPartner P q.1 with
  | none => simp
  | some y =>
      have hqy : (q.1,y) ∈ P :=
        (collectionPartner_eq_some_iff hP q.1 y).1 h
      have hadm := hP.2 (q.1,y) hqy
      have hmem : y ∈ shortPartners (D := D) q.1 := by
        apply Finset.mem_erase.mpr
        constructor
        · intro hy
          subst y
          simpa [paperPos] using (ne_of_lt hadm.1)
        · simp [forwardWindow,paperPos]
          omega
      simp [h, hmem]

def supportedCollectionCode {n D : ℕ}
    (Q : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) :
    {q // q ∈ Q} → Option (Fin n) :=
  fun q => collectionPartner P q.1

theorem supportedCollectionCode_injective {n D : ℕ}
    (Q : Finset (Fin n)) :
    Set.InjOn (supportedCollectionCode (D := D) Q)
      (supportedAdmissibleCollections D Q :
        Set (Finset (Fin n × Fin n))) := by
  intro P hP Q' hQ' hcode
  have hPadm :=
    (Finset.mem_filter.mp (show P ∈ supportedAdmissibleCollections D Q from hP)).2.1
  have hPsupp :=
    (Finset.mem_filter.mp (show P ∈ supportedAdmissibleCollections D Q from hP)).2.2
  have hQadm :=
    (Finset.mem_filter.mp (show Q' ∈ supportedAdmissibleCollections D Q from hQ')).2.1
  have hQsupp :=
    (Finset.mem_filter.mp (show Q' ∈ supportedAdmissibleCollections D Q from hQ')).2.2
  ext r
  constructor
  · intro hr
    have hrQ : r.1 ∈ Q := hPsupp r hr
    let q : {x // x ∈ Q} := ⟨r.1,hrQ⟩
    have hp :
        collectionPartner P r.1 = some r.2 :=
      (collectionPartner_eq_some_iff hPadm r.1 r.2).2 hr
    have hfun := congrFun hcode q
    have hqpartner : collectionPartner Q' r.1 = some r.2 := by
      simpa [supportedCollectionCode,q,hp] using hfun.symm
    exact (collectionPartner_eq_some_iff hQadm r.1 r.2).1 hqpartner
  · intro hr
    have hrQ : r.1 ∈ Q := hQsupp r hr
    let q : {x // x ∈ Q} := ⟨r.1,hrQ⟩
    have hp :
        collectionPartner Q' r.1 = some r.2 :=
      (collectionPartner_eq_some_iff hQadm r.1 r.2).2 hr
    have hfun := congrFun hcode q
    have hppartner : collectionPartner P r.1 = some r.2 := by
      simpa [supportedCollectionCode,q,hp] using hfun
    exact (collectionPartner_eq_some_iff hPadm r.1 r.2).1 hppartner

def supportedCollectionCodes {n D : ℕ} (Q : Finset (Fin n)) :
    Finset ({q // q ∈ Q} → Option (Fin n)) :=
  Finset.univ.pi fun q =>
    insert none ((shortPartners (D := D) q.1).image some)

theorem supportedAdmissibleCollections_card_le {n D : ℕ}
    (Q : Finset (Fin n)) :
    (supportedAdmissibleCollections D Q).card ≤
      (5 * D + 1) ^ Q.card := by
  classical
  let f := supportedCollectionCode (D := D) Q
  have hmap :
      ∀ P ∈ supportedAdmissibleCollections D Q,
        f P ∈ supportedCollectionCodes (D := D) Q := by
    intro P hP
    have hPadm := (Finset.mem_filter.mp hP).2.1
    have hPsupp := (Finset.mem_filter.mp hP).2.2
    simp [supportedCollectionCodes]
    intro q
    exact collectionPartner_mem_allowed hPadm hPsupp q
  have hinj := supportedCollectionCode_injective (D := D) Q
  calc
    (supportedAdmissibleCollections D Q).card
      = ((supportedAdmissibleCollections D Q).image f).card := by
          symm
          exact Finset.card_image_of_injOn hinj
    _ ≤ (supportedCollectionCodes (D := D) Q).card := by
          apply Finset.card_le_card
          intro code hcode
          rcases Finset.mem_image.mp hcode with ⟨P,hP,rfl⟩
          exact hmap P hP
    _ = ∏ q : {x // x ∈ Q},
        (insert none ((shortPartners (D := D) q.1).image some)).card := by
          simp [supportedCollectionCodes,Finset.card_pi]
    _ ≤ ∏ _q : {x // x ∈ Q}, (5 * D + 1) := by
          gcongr with q
          calc
            (insert none ((shortPartners (D := D) q.1).image some)).card
              ≤ (shortPartners (D := D) q.1).card + 1 := by
                  exact Finset.card_insert_le _ _
            _ ≤ 5 * D + 1 := Nat.add_le_add_right
                  (card_shortPartners_le (D := D) q.1) 1
    _ = (5 * D + 1) ^ Q.card := by simp

/-- Reversal conjugation preserves admissibility of a collection of local
disjoint swaps and preserves the same distance bound. -/
def reverseSwapPair {n : ℕ} (q : Fin n × Fin n) :
    Fin n × Fin n :=
  (reverseIndex n q.2, reverseIndex n q.1)

theorem reverseSwapPair_involutive {n : ℕ} :
    Function.Involutive (reverseSwapPair (n := n)) := by
  intro q
  rcases q with ⟨a,b⟩
  simp [reverseSwapPair,reverseIndex_involutive]

theorem reverseSwapPair_injective {n : ℕ} :
    Function.Injective (reverseSwapPair (n := n)) :=
  (reverseSwapPair_involutive (n := n)).injective

def reverseSwapCollection {n : ℕ}
    (P : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) :=
  P.image reverseSwapPair

theorem reverseSwapCollection_admissible {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P) :
    IsAdmissibleCollection D (reverseSwapCollection P) := by
  constructor
  · intro q hq r hr hqr
    rcases Finset.mem_image.mp hq with ⟨q₀,hq₀,rfl⟩
    rcases Finset.mem_image.mp hr with ⟨r₀,hr₀,rfl⟩
    have hq0r0 : q₀ ≠ r₀ := by
      intro h
      subst r₀
      exact hqr rfl
    have hd := hP.1 hq₀ r₀ hq0r0
    unfold reverseSwapPair swapPairsDisjoint
    simp only
    repeat' apply And.intro
    · intro h; exact hd.2.2.2 (reverseIndex_injective h)
    · intro h; exact hd.2.2.1 (reverseIndex_injective h)
    · intro h; exact hd.2.1 (reverseIndex_injective h)
    · intro h; exact hd.1 (reverseIndex_injective h)
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨r,hr,rfl⟩
    have hadm := hP.2 r hr
    unfold reverseSwapPair
    constructor
    · rw [paperPos_reverseIndex,paperPos_reverseIndex]
      omega
    · rw [paperPos_reverseIndex,paperPos_reverseIndex]
      omega

theorem reverseConjugate_trans {n : ℕ}
    (π ρ : Equiv.Perm (Fin n)) :
    reverseConjugate (π.trans ρ) =
      (reverseConjugate π).trans (reverseConjugate ρ) := by
  ext i
  simp [reverseConjugate_apply,reverseIndex_involutive]

theorem reverseConjugate_swap {n : ℕ}
    (a b : Fin n) :
    reverseConjugate (Equiv.swap a b) =
      Equiv.swap (reverseIndex n a) (reverseIndex n b) := by
  ext i
  by_cases hia : reverseIndex n i = a
  · have hi : i = reverseIndex n a := by
      apply reverseIndex_injective
      simpa using hia
    subst i
    simp [reverseConjugate_apply,hia,reverseIndex_involutive]
  by_cases hib : reverseIndex n i = b
  · have hi : i = reverseIndex n b := by
      apply reverseIndex_injective
      simpa using hib
    subst i
    simp [reverseConjugate_apply,hib,reverseIndex_involutive]
  have hiA : i ≠ reverseIndex n a := by
    intro h
    subst i
    simp at hia
  have hiB : i ≠ reverseIndex n b := by
    intro h
    subst i
    simp at hib
  simp [reverseConjugate_apply,Equiv.swap_apply_of_ne_of_ne,
    hia,hib,hiA,hiB,reverseIndex_involutive]

theorem swapsPermList_reverse {n : ℕ}
    (l : List (Fin n × Fin n)) :
    swapsPermList (l.map reverseSwapPair) =
      reverseConjugate (swapsPermList l) := by
  induction l with
  | nil =>
      ext i
      simp [swapsPermList,reverseConjugate_apply,
        reverseIndex_involutive]
  | cons q qs ih =>
      rcases q with ⟨a,b⟩
      simp only [List.map_cons,swapsPermList]
      rw [reverseConjugate_trans,← ih,
        reverseConjugate_swap]
      simp [reverseSwapPair]
      rw [Equiv.swap_comm]

theorem reverseConjugate_admissible {n D : ℕ}
    (π : Equiv.Perm (Fin n))
    (hπ : IsAdmissiblePermutation D π) :
    IsAdmissiblePermutation D (reverseConjugate π) := by
  rcases hπ with ⟨P,hPadm,hPπ⟩
  let P' := reverseSwapCollection P
  have hP'adm := reverseSwapCollection_admissible hPadm
  refine ⟨P',hP'adm,?_⟩
  have hlist :
      (P.toList.map reverseSwapPair).toFinset = P' := by
    ext q
    simp [P',reverseSwapCollection]
  have hnodup :
      (P.toList.map reverseSwapPair).Nodup :=
    P.nodup_toList.map reverseSwapPair_injective
  rw [← collectionPerm_order_independent hP'adm
      (P.toList.map reverseSwapPair) hlist hnodup]
  rw [swapsPermList_reverse,hPπ]

/-- Reversal conjugation transports the fixed-outside condition from [b,b'] to
the reversed interval [rev b', rev b]. -/
theorem reverseConjugate_fixedOutside {n : ℕ}
    (b b' : Fin n) (π : Equiv.Perm (Fin n))
    (hfix : FixedOutside b b' π) :
    FixedOutside (reverseIndex n b') (reverseIndex n b)
      (reverseConjugate π) := by
  intro i hi
  have hrev :
      paperPos (reverseIndex n i) < paperPos b ∨
        paperPos b' < paperPos (reverseIndex n i) := by
    rcases hi with hi | hi
    · right
      rw [paperPos_reverseIndex, paperPos_reverseIndex] at hi
      omega
    · left
      rw [paperPos_reverseIndex, paperPos_reverseIndex] at hi
      omega
  rw [reverseConjugate_apply,hfix (reverseIndex n i) hrev,
    reverseIndex_involutive]

end

end GrahamRearrangement.Section5External
