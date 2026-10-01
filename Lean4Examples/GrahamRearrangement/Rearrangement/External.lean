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

/-- Specialized finite form of the preceding sampling fact for ZMod orderings. -/
axiom conditional_index_family_sumMass_le_zmod
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
        sliceMass (S \ indexImageSet τ F) (I a).card (z a)

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

/-- A uniform bound on an event in every fiber obtained by exposing F is also
an unconditional bound. -/
axiom event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E]
    (q : ℝ)
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) E ≤ q) :
    orderingEventMass S E ≤ q

/-- Fiber multiplication specialized to exposing a set of positions in a
uniform random ordering. -/
axiom joint_event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
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
    orderingEventMass S (fun σ => A σ ∧ B σ) ≤ a * b

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
axiom dense_window_extract {n D : ℕ}
    (B : Finset (Fin n)) (hD : 0 < D)
    (h : ∃ z : Fin n,
      D < (B ∩ symmetricWindow z (10 * D)).card) :
    ∃ b₀ ∈ B, ∃ b : Fin D → Fin n,
      Function.Injective b ∧
      (∀ i, b i ∈ B) ∧
      (∀ i, paperPos b₀ < paperPos (b i) ∧
        paperPos (b i) ≤ paperPos b₀ + 20 * D)

/-- A finite tuple of distinct elements in a linear order can be relabelled in
strictly increasing order without changing the underlying set of witnesses. -/
axiom relabel_strictly_increasing
    {α : Type*} [LinearOrder α] [Fintype α] [DecidableEq α]
    {D : ℕ} (x : Fin D → α) (hinj : Function.Injective x) :
    ∃ y : Fin D → α, StrictMono y ∧
      Set.range y = Set.range x

/-- Generic permutation fact: transpositions with disjoint supports commute. -/
theorem disjoint_swaps_commute {α : Type*} [DecidableEq α]
    (a b c d : α)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) := by
  ext x
  by_cases hxa : x = a
  · subst x; simp [hab,hac,had,hbc,hbd]
  by_cases hxb : x = b
  · subst x; simp [hab,hac,had,hbc,hbd]
  by_cases hxc : x = c
  · subst x; simp [hab,hcd,hac,had,hbc,hbd]
  by_cases hxd : x = d
  · subst x; simp [hab,hcd,hac,had,hbc,hbd]
  simp [Equiv.swap_apply_of_ne_of_ne,hxa,hxb,hxc,hxd]

theorem nodup_toFinset_eq_perm {α : Type*} [DecidableEq α]
    {l r : List α} (hl : l.Nodup) (hr : r.Nodup)
    (hset : l.toFinset = r.toFinset) :
    l.Perm r := by
  induction l generalizing r with
  | nil =>
      have : r = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have : x ∈ r.toFinset := by simpa using hx
        simpa [hset] using this
      simp [this]
  | cons a l ih =>
      have hal : a ∉ l := (List.nodup_cons.mp hl).1
      have hln : l.Nodup := (List.nodup_cons.mp hl).2
      have har : a ∈ r := by
        have : a ∈ r.toFinset := by
          rw [← hset]
          simp
        simpa using this
      let r' := r.erase a
      have hr' : r'.Nodup := hr.erase _
      have hset' : l.toFinset = r'.toFinset := by
        ext x
        by_cases hxa : x = a
        · subst x; simp [hal,r',hr]
        · have hcons :
              x ∈ (a :: l).toFinset ↔ x ∈ l.toFinset := by simp [hxa]
          have herase :
              x ∈ r'.toFinset ↔ x ∈ r.toFinset := by
            simp [r',hxa]
          rw [← hcons, hset, herase]
      have hp := ih hln hr' hset'
      have hconsperm : a :: r' ~ r := by
        exact List.Perm.cons_erase a har
      exact (List.Perm.cons a hp).trans hconsperm

theorem swapsPermList_perm_of_disjoint
    {α : Type*} [DecidableEq α]
    {l r : List (α × α)}
    (hperm : l.Perm r)
    (hpair :
      ∀ q ∈ l, ∀ s ∈ l, q ≠ s →
        q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2)
    (hord : ∀ q ∈ l, q.1 ≠ q.2) :
    swapsPermList l = swapsPermList r := by
  induction hperm with
  | nil => rfl
  | @cons a l r hperm ih =>
      have hpair' :
          ∀ q ∈ l, ∀ s ∈ l, q ≠ s →
            q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2 := by
        intro q hq s hs hne
        exact hpair q (by simp [hq]) s (by simp [hs]) hne
      have hord' : ∀ q ∈ l, q.1 ≠ q.2 := by
        intro q hq
        exact hord q (by simp [hq])
      simp [swapsPermList,ih hpair' hord']
  | @swap a b l =>
      have hab : a ≠ b := by
        intro h; subst b
        have hd := hpair a (by simp) a (by simp) (by simp)
        exact hd.1 rfl
      have haord := hord a (by simp)
      have hbord := hord b (by simp)
      have hd := hpair a (by simp) b (by simp) hab
      have hcomm :=
        disjoint_swaps_commute
          a.1 a.2 b.1 b.2 haord hbord
          hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      simp [swapsPermList]
      rw [hcomm]
  | @trans l r s h₁ h₂ ih₁ ih₂ =>
      have hset₁ : r.toFinset = l.toFinset := by
        exact Finset.ext fun x => by
          simpa using h₁.mem_iff.symm
      have hpairR :
          ∀ q ∈ r, ∀ t ∈ r, q ≠ t →
            q.1 ≠ t.1 ∧ q.1 ≠ t.2 ∧ q.2 ≠ t.1 ∧ q.2 ≠ t.2 := by
        intro q hq t ht hne
        apply hpair q
        · exact h₁.symm.mem_iff.mp hq
        · exact h₁.symm.mem_iff.mp ht
        · exact hne
      have hordR : ∀ q ∈ r, q.1 ≠ q.2 := by
        intro q hq
        exact hord q (h₁.symm.mem_iff.mp hq)
      exact (ih₁ hpair hord).trans (ih₂ hpairR hordR)

/-- The product of support-disjoint transpositions is independent of the
enumeration. -/
theorem disjoint_swaps_order_independent {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (l : List (α × α)) (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = swapsPermList P.toList := by
  have hperm :=
    nodup_toFinset_eq_perm hln P.nodup_toList hl
  apply swapsPermList_perm_of_disjoint hperm
  · intro q hq r hr hne
    exact hP (by simpa [← hl] using hq)
      (by simpa [← hl] using hr) hne
  · intro q hq
    by_contra heq
    have hself :
        q.1 ≠ q.1 ∧ q.1 ≠ q.2 ∧ q.2 ≠ q.1 ∧ q.2 ≠ q.2 := by
      have qmem : q ∈ P := by simpa [← hl] using hq
      have : False := by
        exact hP qmem qmem (by
          intro h; exact (not_false_eq_true.mpr trivial) (congrArg id h))
      contradiction
    exact hself.2.1 heq

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
  have hln : l.Nodup := by
    simp [l]
  have hset : l.toFinset = P := by
    simp [l,hq]
  have horder :=
    disjoint_swaps_order_independent P hPpair l hset hln
  have hrest1 :
      swapsPermList (P.erase q).toList q.1 = q.1 := by
    apply disjoint_swaps_fix_outside_support (P.erase q)
    · exact hPpair.mono (by intro a ha; exact Finset.mem_of_mem_erase ha)
    · intro r hr
      have hrP := Finset.mem_of_mem_erase hr
      have hrne := Finset.ne_of_mem_erase hr
      have hd := hPpair hq hrP hrne.symm
      exact ⟨hd.1,hd.2.1⟩
  have hrest2 :
      swapsPermList (P.erase q).toList q.2 = q.2 := by
    apply disjoint_swaps_fix_outside_support (P.erase q)
    · exact hPpair.mono (by intro a ha; exact Finset.mem_of_mem_erase ha)
    · intro r hr
      have hrP := Finset.mem_of_mem_erase hr
      have hrne := Finset.ne_of_mem_erase hr
      have hd := hPpair hq hrP hrne.symm
      exact ⟨hd.2.2.1,hd.2.2.2⟩
  have hqne : q.1 ≠ q.2 := ne_of_lt (hord q hq)
  constructor
  · rw [← horder]
    simp [l,swapsPermList,hqne,hrest2]
  · rw [← horder]
    simp [l,swapsPermList,hqne,hrest1]

/-- A finite collection of disjoint, oriented nontrivial transpositions is
recovered from the resulting permutation. -/
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
    have hmoveQ :
        swapsPermList Q.toList q.1 = q.2 := by
      rw [← hperm]
      exact hactP.1
    have hqne : q.1 ≠ q.2 := ne_of_lt (hPord q hq)
    by_contra hqQ
    have hsupport :
        ∃ r ∈ Q, q.1 = r.1 ∨ q.1 = r.2 := by
      by_contra hnone
      push_neg at hnone
      have hfix :=
        disjoint_swaps_fix_outside_support Q hQpair q.1
          (by
            intro r hr
            exact ⟨hnone r hr |>.1, hnone r hr |>.2⟩)
      rw [hfix] at hmoveQ
      exact hqne hmoveQ
    rcases hsupport with ⟨r,hr,hr1 | hr2⟩
    · have hactQ := swapsPermList_pair_action Q hQpair hQord hr
      rw [hr1] at hactQ
      have : r.2 = q.2 := by
        rw [← hmoveQ]
        exact hactQ.1.symm
      have : r = q := by
        apply Prod.ext
        · exact hr1.symm
        · exact this
      exact hqQ (this ▸ hr)
    · have hactQ := swapsPermList_pair_action Q hQpair hQord hr
      have hEq : r.1 = q.2 := by
        rw [hr2] at hactQ
        rw [hactQ.2] at hmoveQ
        exact hmoveQ
      have hrord := hQord r hr
      have hqord := hPord q hq
      rw [hr2,hEq] at hrord
      exact (not_lt_of_ge (le_of_lt hqord)) hrord
  · intro q hq
    have hsym : swapsPermList Q.toList = swapsPermList P.toList :=
      hperm.symm
    exact Finset.mem_of_subset
      (by
        intro r hr
        have hactQ := swapsPermList_pair_action Q hQpair hQord hr
        have hmoveP : swapsPermList P.toList r.1 = r.2 := by
          rw [← hsym]
          exact hactQ.1
        have hrne : r.1 ≠ r.2 := ne_of_lt (hQord r hr)
        by_contra hrP
        have hsupport :
            ∃ s ∈ P, r.1 = s.1 ∨ r.1 = s.2 := by
          by_contra hnone
          push_neg at hnone
          have hfix :=
            disjoint_swaps_fix_outside_support P hPpair r.1
              (by intro s hs; exact ⟨(hnone s hs).1,(hnone s hs).2⟩)
          rw [hfix] at hmoveP
          exact hrne hmoveP
        rcases hsupport with ⟨s,hs,hs1 | hs2⟩
        · have hactP := swapsPermList_pair_action P hPpair hPord hs
          rw [hs1] at hactP
          have hsnd : s.2 = r.2 := by
            rw [← hmoveP]
            exact hactP.1.symm
          have : s = r := Prod.ext hs1.symm hsnd
          exact hrP (this ▸ hs)
        · have hactP := swapsPermList_pair_action P hPpair hPord hs
          have hfst : s.1 = r.2 := by
            rw [hs2] at hactP
            rw [hactP.2] at hmoveP
            exact hmoveP
          have hsord := hPord s hs
          have hrord := hQord r hr
          rw [hs2,hfst] at hsord
          exact (not_lt_of_ge (le_of_lt hrord)) hsord)
      hq

/-- A product of support-disjoint swaps fixes every point outside all swap
supports. -/
theorem disjoint_swaps_fix_outside_support
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (i : α)
    (hi : ∀ q ∈ P, i ≠ q.1 ∧ i ≠ q.2) :
    swapsPermList P.toList i = i := by
  induction P.toList with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      have hqP : q ∈ P := by
        simpa using P.mem_toList q
      have hqi := hi q hqP
      have hqs : ∀ r ∈ qs, i ≠ r.1 ∧ i ≠ r.2 := by
        intro r hr
        exact hi r (by
          have : r ∈ P.toList := by simp [hr]
          simpa using this)
      simp [swapsPermList,Equiv.swap_apply_of_ne_of_ne hqi.1 hqi.2,
        ih hqs]

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
axiom exists_sorting_perm
    {α : Type*} [LinearOrder α] {k : ℕ}
    (x : Fin k → α) (hinj : Function.Injective x) :
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ)

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

/-- Right-tail analogue of conditional_prefix_chain_union_bound. -/
axiom conditional_suffix_chain_union_bound
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
        ∃ x : Fin k → Fin S.card,
          StrictMono x ∧
          (∀ i, paperPos cut < paperPos (x i)) ∧
          (∀ i,
            indexSetSum σ (indexHalfOpen cut (x i)) = target i)) ≤
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
axiom reverseConjugate_fixedOutside {n : ℕ}
    (b b' : Fin n) (π : Equiv.Perm (Fin n))
    (hfix : FixedOutside b b' π) :
    FixedOutside (reverseIndex n b') (reverseIndex n b)
      (reverseConjugate π)

/-- Fixed-position reversal is a permutation and therefore preserves a uniform
random ordering. -/
axiom reversal_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin S.card → ZMod p) → Prop)
    [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ =>
        E (fun i => σ ⟨S.card - 1 - i.val, by omega⟩))

/-- An admissible local permutation fixing the prefix sends a subset of the
5D-window into the 10D-window. -/
axiom admissible_local_image_subset
    {n D : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (J : Finset (Fin n))
    (hJ : J ⊆ forwardWindow b (5 * D)) :
    J.image π ⊆ forwardWindow b (10 * D)

/-- Generic two-colour pigeonhole extraction: from at least 2D distinct
objects, each of which has colour A or B, one can select D distinct objects of
one colour. -/
theorem two_colour_extract {α : Type*} [DecidableEq α]
    (D : ℕ) (Y : Finset α)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (hcard : 2 * D ≤ Y.card)
    (hcover : ∀ y ∈ Y, A y ∨ B y) :
    (∃ f : Fin D → α, Function.Injective f ∧
      ∀ i, f i ∈ Y ∧ A (f i)) ∨
    (∃ f : Fin D → α, Function.Injective f ∧
      ∀ i, f i ∈ Y ∧ B (f i)) := by
  classical
  let YA := Y.filter A
  by_cases hA : D ≤ YA.card
  · obtain ⟨f,hfinj,hf⟩ := exists_injective_fin_enum YA D hA
    exact Or.inl ⟨f,hfinj,fun i => by
      have hi := hf i
      exact ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩⟩
  · have hAc : YA.card < D := Nat.lt_of_not_ge hA
    let YB := Y.filter fun y => ¬ A y
    have hpartition : YA.card + YB.card = Y.card := by
      unfold YA YB
      exact Finset.card_filter_add_card_filter_neg_eq Y A
    have hBcard : D ≤ YB.card := by omega
    obtain ⟨f,hfinj,hf⟩ := exists_injective_fin_enum YB D hBcard
    exact Or.inr ⟨f,hfinj,fun i => by
      have hi := hf i
      have hiY := (Finset.mem_filter.mp hi).1
      have hnotA := (Finset.mem_filter.mp hi).2
      rcases hcover (f i) hiY with hAi | hBi
      · exact False.elim (hnotA hAi)
      · exact ⟨hiY,hBi⟩⟩

/-- Generic finite choice principle used in the greedy repair: a finite candidate
set of cardinality 5D with three forbidden subsets of sizes at most 2D,D,D
has a remaining element when D>0. -/
theorem exists_after_three_forbidden {α : Type*} [DecidableEq α]
    (D : ℕ) (hD : 0 < D)
    (C F₁ F₂ F₃ : Finset α)
    (hC : C.card = 5 * D)
    (h₁ : (C ∩ F₁).card ≤ 2 * D)
    (h₂ : (C ∩ F₂).card ≤ D)
    (h₃ : (C ∩ F₃).card ≤ D) :
    ∃ x ∈ C, x ∉ F₁ ∧ x ∉ F₂ ∧ x ∉ F₃ := by
  by_contra hnone
  push_neg at hnone
  have hsub :
      C ⊆ (C ∩ F₁) ∪ (C ∩ F₂) ∪ (C ∩ F₃) := by
    intro x hx
    rcases hnone x hx with h1 | h2 | h3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hx,h1⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨hx,h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx,h3⟩)
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (C ∩ F₁) (C ∩ F₂)
  have hu2 := Finset.card_union_le ((C ∩ F₁) ∪ (C ∩ F₂)) (C ∩ F₃)
  rw [hC] at hc
  omega

end

end GrahamRearrangement.Section5External
