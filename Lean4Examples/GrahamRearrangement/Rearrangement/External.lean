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
axiom distinct_index_subset_sums_mass_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (W J J' : Finset (Fin S.card))
    (hJ : J ⊆ W) (hJ' : J' ⊆ W) (hne : J ≠ J')
    (hW : W.card ≤ S.card) :
    orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
      1 / ((S.card - W.card + 1 : ℕ) : ℝ)

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

/-- Conditioning a uniform bijection on its values on F leaves a uniform bijection
between the unexposed positions and S minus the exposed image. Nested image sets
therefore have exactly the chain law on the remaining ground set. -/
axiom conditional_nested_images_chainMass {p k : ℕ} [NeZero p]
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
      chainMass (S \ indexImageSet τ F) m z

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

/-- Generic trimming principle for disjoint transpositions: swaps crossing none
of a finite family of index sets can be deleted without changing the image of
any of those sets. -/
axiom trim_irrelevant_disjoint_swaps
    {n k : ℕ} (P : Finset (Fin n × Fin n))
    (hP : P.toSet.Pairwise swapPairsDisjoint)
    (I : Fin k → Finset (Fin n)) :
    ∃ P' ⊆ P,
      P'.toSet.Pairwise swapPairsDisjoint ∧
      (∀ q ∈ P', ∃ i, ((q.1 ∈ I i) ↔ q.2 ∉ I i)) ∧
      ∀ i, (I i).image (collectionPerm P') =
        (I i).image (collectionPerm P)

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
axiom supportedAdmissibleCollections_card_le {n D : ℕ}
    (Q : Finset (Fin n)) :
    (supportedAdmissibleCollections D Q).card ≤
      (5 * D + 1) ^ Q.card

/-- Reversal conjugation preserves admissibility of a collection of local
disjoint swaps and preserves the same distance bound. -/
axiom reverseConjugate_admissible {n D : ℕ}
    (π : Equiv.Perm (Fin n))
    (hπ : IsAdmissiblePermutation D π) :
    IsAdmissiblePermutation D (reverseConjugate π)

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
