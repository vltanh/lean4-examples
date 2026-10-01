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

theorem constraintSet_mem_above_window {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) (z : Fin n)
    (hz : paperPos b' < paperPos z) :
    z ∈ constraintSet u x πi i ↔
      z ∈ indexInterval (u i) (x i) := by
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨w, hw, hπw⟩
    have hzfix : πi i z = z :=
      hfix i z (Or.inr hz)
    have hwz : w = z := by
      apply (πi i).injective
      rw [hπw, hzfix]
    simpa [hwz] using hw
  · intro h
    refine Finset.mem_image.2 ⟨z, h, ?_⟩
    exact hfix i z (Or.inr hz)

theorem constraintSet_not_mem_below_window {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) (z : Fin n)
    (hz : paperPos z < paperPos b) :
    z ∉ constraintSet u x πi i := by
  intro h
  rcases Finset.mem_image.1 h with ⟨w, hw, hπw⟩
  have hzfix : πi i z = z :=
    hfix i z (Or.inl hz)
  have hwz : w = z := by
    apply (πi i).injective
    rw [hπw, hzfix]
  subst w
  have hw' := (Finset.mem_filter.1 hw).2.1
  have hui := (hu i).1
  simp [paperPos] at hw' hui hz
  omega

theorem interesting_crossing_forces_tail_start
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
    (q : Fin n × Fin n) (i : Fin D)
    (hlen :
      paperPos q.1 < paperPos q.2 ∧
        paperPos q.2 - paperPos q.1 ≤ 5 * D)
    (hcross : SwapCrosses q (constraintSet u x πi i))
    (hnotlocal : q.1 ∉ symmetricWindow b (5 * D)) :
    q.1 ∈ backwardWindow (x i) (5 * D) := by
  have hq1right : paperPos b' < paperPos q.1 := by
    by_contra hnot
    have hq1le : paperPos q.1 ≤ paperPos b' := le_of_not_gt hnot
    by_cases hq1lt : paperPos q.1 < paperPos b
    · have hq2lt : paperPos q.2 < paperPos b := by
        have hdist : 5 * D < paperPos b - paperPos q.1 := by
          simp [symmetricWindow, Nat.dist_eq, paperPos] at hnotlocal
          omega
        omega
      have hq1out :=
        constraintSet_not_mem_below_window
          b b' u x hu πi hfix i q.1 hq1lt
      have hq2out :=
        constraintSet_not_mem_below_window
          b b' u x hu πi hfix i q.2 hq2lt
      rcases hcross with h | h <;> tauto
    · have hq1ge : paperPos b ≤ paperPos q.1 := le_of_not_gt hq1lt
      have hdist :
          Nat.dist q.1.val b.val ≤ 5 * D := by
        simp [Nat.dist_eq, paperPos] at *
        omega
      exact hnotlocal (by
        simp [symmetricWindow, hdist])
  have hq2right : paperPos b' < paperPos q.2 :=
    lt_trans hq1right hlen.1
  have hm1 :=
    constraintSet_mem_above_window b b' u x hu πi hfix i q.1 hq1right
  have hm2 :=
    constraintSet_mem_above_window b b' u x hu πi hfix i q.2 hq2right
  have hq1x : paperPos q.1 ≤ paperPos (x i) := by
    rcases hcross with hcross | hcross
    · have hmem := (hm1.mp hcross.1)
      have hmem' := (Finset.mem_filter.1 hmem).2
      simpa [paperPos] using hmem'.2
    · have hq2mem := hm2.mp hcross.2
      have hq2mem' := (Finset.mem_filter.1 hq2mem).2
      have hq1lt := hlen.1
      simpa [paperPos] using
        le_trans (le_of_lt hq1lt) (by
          simpa [paperPos] using hq2mem'.2)
  have hxq2 : paperPos (x i) < paperPos q.2 := by
    by_contra hnot
    have hq2x : paperPos q.2 ≤ paperPos (x i) := le_of_not_gt hnot
    have hq2mem : q.2 ∈ indexInterval (u i) (x i) := by
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have hui := (hu i).1
        omega
      · simpa [paperPos] using hq2x
    have hq1mem : q.1 ∈ indexInterval (u i) (x i) := by
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have hui := (hu i).1
        omega
      · simpa [paperPos] using hq1x
    have hboth :
        q.1 ∈ constraintSet u x πi i ∧
          q.2 ∈ constraintSet u x πi i :=
      ⟨hm1.mpr hq1mem, hm2.mpr hq2mem⟩
    rcases hcross with h | h
    · exact h.2 hboth.2
    · exact h.1 hboth.1
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · simpa [paperPos] using hq1x
  · simp [paperPos] at hlen hxq2 ⊢
    omega

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
      exact interesting_crossing_forces_tail_start
        hD b b' hgap u x πi hu hfix q i hlen hi hlocal
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ i, htail⟩)

def chosenInterestingCollection {n k : ℕ} (D : ℕ)
    (I : Fin k → Finset (Fin n))
    (π : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  by_cases h : IsInterestingPermutation D I π
  · exact Classical.choose h
  · exact ∅

theorem chosenInterestingCollection_spec {n k : ℕ}
    (D : ℕ) (I : Fin k → Finset (Fin n))
    {π : Equiv.Perm (Fin n)}
    (hπ : π ∈ interestingPermutations D I) :
    IsAdmissibleCollection D
        (chosenInterestingCollection D I π) ∧
      collectionPerm (chosenInterestingCollection D I π) = π ∧
      ∀ q ∈ chosenInterestingCollection D I π,
        ∃ i, SwapCrosses q (I i) := by
  classical
  have h : IsInterestingPermutation D I π :=
    (Finset.mem_filter.1 hπ).2
  simp [chosenInterestingCollection, h]
  exact Classical.choose_spec h

theorem chosenInterestingCollection_injective {n k : ℕ}
    (D : ℕ) (I : Fin k → Finset (Fin n)) :
    Set.InjOn (chosenInterestingCollection D I)
      (interestingPermutations D I : Set (Equiv.Perm (Fin n))) := by
  intro π hπ ρ hρ hEq
  have hπspec :=
    (chosenInterestingCollection_spec D I
      (show π ∈ interestingPermutations D I from hπ)).2.1
  have hρspec :=
    (chosenInterestingCollection_spec D I
      (show ρ ∈ interestingPermutations D I from hρ)).2.1
  rw [← hπspec, ← hρspec, hEq]

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
  classical
  let I : Fin D → Finset (Fin n) :=
    fun i => constraintSet u x πi i
  let Q := interestingLeftSupport b x
  let f := chosenInterestingCollection D I
  have hfinj :
      Set.InjOn f
        (interestingPermutations D I : Set (Equiv.Perm (Fin n))) :=
    chosenInterestingCollection_injective D I
  have hsupport :
      ∀ π ∈ interestingPermutations D I,
        f π ∈ supportedAdmissibleCollections D Q := by
    intro π hπ
    have hspec := chosenInterestingCollection_spec D I hπ
    obtain ⟨P', hP'adm, hP'π, hP'supp⟩ :=
      interesting_left_support
        (by omega) b b' hgap u x hu πi hfix hπ
    have hEq : f π = P' := by
      apply admissibleCollection_reconstruct
        hspec.1 hP'adm
      rw [hspec.2.1, hP'π]
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, hspec.1, ?_⟩
    intro q hq
    rw [hEq] at hq
    exact hP'supp q hq
  have hcardImage :
      (interestingPermutations D I).card =
        ((interestingPermutations D I).image f).card := by
    symm
    exact Finset.card_image_of_injOn hfinj
  have hsub :
      (interestingPermutations D I).image f ⊆
        supportedAdmissibleCollections D Q := by
    intro P hP
    rcases Finset.mem_image.1 hP with ⟨π, hπ, rfl⟩
    exact hsupport π hπ
  have hQ : Q.card ≤ 7 * D ^ 2 :=
    card_interestingLeftSupport_le hD7 b x
  have hcount :=
    Section5External.supportedAdmissibleCollections_card_le
      (D := D) Q
  have hbase : 5 * D + 1 ≤ D ^ 2 := by
    nlinarith
  calc
    (interestingPermutations D I).card
      = ((interestingPermutations D I).image f).card := hcardImage
    _ ≤ (supportedAdmissibleCollections D Q).card :=
      Finset.card_le_card hsub
    _ ≤ (5 * D + 1) ^ Q.card := hcount
    _ ≤ (D ^ 2) ^ Q.card := by
      gcongr
    _ ≤ (D ^ 2) ^ (7 * D ^ 2) := by
      gcongr
    _ = D ^ (14 * D ^ 2) := by
      rw [← pow_mul]
      congr 1
      ring

def lemma55HeadSet {n D : ℕ}
    (u : Fin D → Fin n) (b' : Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (i : Fin D) : Finset (Fin n) :=
  (indexInterval (u i) b').image (πi i)

def lemma55TailSet {n D : ℕ}
    (b' : Fin n) (x : Fin D → Fin n)
    (i : Fin D) : Finset (Fin n) :=
  indexOpenClosed b' (x i)

theorem lemma55HeadSet_subset_window {n D : ℕ}
    (b b' : Fin n)
    (u : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    lemma55HeadSet u b' πi i ⊆ indexInterval b b' := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨w,hw,rfl⟩
  have hwData := (Finset.mem_filter.mp hw).2
  have hwb : b.val ≤ w.val := by
    have hui := (hu i).1
    simp [paperPos] at hui
    exact le_trans hui hwData.1
  have hwb' : w.val ≤ b'.val := hwData.2
  by_contra hout
  have hout' :
      paperPos (πi i w) < paperPos b ∨
        paperPos b' < paperPos (πi i w) := by
    simp [indexInterval,paperPos] at hout
    omega
  have hfixed := hfix i (πi i w) hout'
  have hEq : w = πi i w := by
    apply (πi i).injective
    simpa [hfixed]
  have hwmem : w ∈ indexInterval b b' := by
    simp [indexInterval,hwb,hwb']
  exact hout (by simpa [hEq] using hwmem)

theorem lemma55TailSet_fixed {n D : ℕ}
    (b b' : Fin n) (x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    (lemma55TailSet b' x i).image (πi i) =
      lemma55TailSet b' x i := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hzData := (Finset.mem_filter.mp hz).2
    have hfixz := hfix i z (Or.inr (by
      simp [paperPos] at hzData ⊢
      omega))
    simpa [hfixz] using hz
  · intro hy
    refine Finset.mem_image.mpr ⟨y,hy,?_⟩
    have hyData := (Finset.mem_filter.mp hy).2
    exact hfix i y (Or.inr (by
      simp [paperPos] at hyData ⊢
      omega))

theorem lemma55_constraint_split {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hx : x ∈ tailTuples b' D)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    constraintSet u x πi i =
      lemma55HeadSet u b' πi i ∪ lemma55TailSet b' x i := by
  have hxi := (Finset.mem_filter.mp hx).2.2 i
  have huib := (hu i).2
  have hux : (u i).val ≤ (x i).val := by
    simp [paperPos] at hxi huib
    omega
  have hsplit :
      indexInterval (u i) (x i) =
        indexInterval (u i) b' ∪ indexOpenClosed b' (x i) := by
    ext y
    simp [indexInterval,indexOpenClosed]
    constructor
    · intro h
      by_cases hy : y.val ≤ b'.val
      · exact Or.inl ⟨h.1,hy⟩
      · exact Or.inr ⟨by omega,h.2⟩
    · rintro (h | h)
      · exact ⟨h.1,le_trans h.2 (by
          simp [paperPos] at hxi; omega)⟩
      · exact ⟨le_trans (by
          simp [paperPos] at huib
          omega) (le_of_lt h.1),h.2⟩
  unfold constraintSet lemma55HeadSet lemma55TailSet
  rw [hsplit,Finset.image_union,lemma55TailSet_fixed b b' x πi hfix i]

theorem lemma55TailSet_nested {n D : ℕ}
    (b' : Fin n) {x : Fin D → Fin n}
    (hx : x ∈ tailTuples b' D) :
    ∀ i j, i ≤ j →
      lemma55TailSet b' x i ⊆ lemma55TailSet b' x j := by
  intro i j hij y hy
  have hmono := (Finset.mem_filter.mp hx).2.1.monotone hij
  simp only [lemma55TailSet,indexOpenClosed,Finset.mem_filter,
    Finset.mem_univ,true_and] at hy ⊢
  exact ⟨hy.1,le_trans hy.2 (by exact_mod_cast hmono)⟩

theorem lemma55TailSet_card {n D : ℕ}
    (b' : Fin n) {x : Fin D → Fin n}
    (hx : x ∈ tailTuples b' D) (i : Fin D) :
    (lemma55TailSet b' x i).card = tailSizes b' x i := by
  have hxi := (Finset.mem_filter.mp hx).2.2 i
  have hle : b'.val ≤ (x i).val := by
    simp [paperPos] at hxi
    omega
  simpa [lemma55TailSet,tailSizes] using
    card_indexOpenClosed b' (x i) hle

theorem lemma55HeadTail_disjoint {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    Disjoint (lemma55HeadSet u b' πi i)
      (lemma55TailSet b' x i) := by
  rw [Finset.disjoint_left]
  intro y hyH hyT
  have hyF := lemma55HeadSet_subset_window b b' u hu πi hfix i hyH
  simp [indexInterval,lemma55TailSet,indexOpenClosed] at hyF hyT
  omega

theorem lemma55_fixed_tail_conditional_bound
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (b b' : Fin S.card)
    (u x : Fin D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hx : x ∈ tailTuples b' D)
    (πi : Fin D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (C : ℝ)
    (hm : IsChainSizeTuple
      (S \ indexImageSet τ (indexInterval b b')).card
      (tailSizes b' x))
    (hchain :
      ∀ z : Fin D → ZMod p,
        chainMass (S \ indexImageSet τ (indexInterval b b'))
            (tailSizes b' x) z ≤
          chainUpperBound p
            (S \ indexImageSet τ (indexInterval b b')).card
            C (tailSizes b' x)) :
    orderingConditionalMass S
      (fun σ => AgreesOn (indexInterval b b') σ τ)
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm σ (πi i))
            (u i) (x i) = 0) ≤
      chainUpperBound p
        (S \ indexImageSet τ (indexInterval b b')).card
        C (tailSizes b' x) := by
  classical
  let F := indexInterval b b'
  let I : Fin D → Finset (Fin S.card) :=
    lemma55TailSet b' x
  let H : Fin D → Finset (Fin S.card) :=
    fun i => lemma55HeadSet u b' πi i
  let z : Fin D → ZMod p :=
    fun i => - indexSetSum τ (H i)
  have hdisj : ∀ i, Disjoint F (I i) := by
    intro i
    rw [Finset.disjoint_left]
    intro y hyF hyI
    simp [F,I,indexInterval,lemma55TailSet,indexOpenClosed] at hyF hyI
    omega
  have hnested : ∀ i j, i ≤ j → I i ⊆ I j :=
    lemma55TailSet_nested b' hx
  have hcard : ∀ i, (I i).card = tailSizes b' x i :=
    lemma55TailSet_card b' hx
  have hevent :
      orderingConditionalMass S
        (fun σ => AgreesOn F σ τ)
        (fun σ =>
          ∀ i,
            indexedIntervalSum
              (applyPositionPerm σ (πi i))
              (u i) (x i) = 0) =
      orderingConditionalMass S
        (fun σ => AgreesOn F σ τ)
        (fun σ => ∀ i, indexSetSum σ (I i) = z i) := by
    unfold orderingConditionalMass uniformConditionalMass
    apply uniformMass_congr
    intro σ hσ
    have hagr : AgreesOn F σ τ := (Finset.mem_filter.mp hσ).2
    constructor
    · intro hz i
      have hui := (hu i).2
      have hxi := (Finset.mem_filter.mp hx).2.2 i
      have hux : (u i).val ≤ (x i).val := by
        simp [paperPos] at hui hxi
        omega
      have hsum :
          indexedIntervalSum
              (applyPositionPerm σ (πi i)) (u i) (x i) =
            indexSetSum σ (constraintSet u x πi i) := by
        simpa [constraintSet,applyPositionPerm] using
          permuted_interval_sum_eq σ (Equiv.refl _) (πi i)
            (u i) (x i) hux
      have hsplit :=
        lemma55_constraint_split b b' u x hu hx πi hfix i
      have hheadSub :
          H i ⊆ F := by
        exact lemma55HeadSet_subset_window
          b b' u hu πi hfix i
      have hhead :
          indexSetSum σ (H i) = indexSetSum τ (H i) :=
        Section5External.indexSetSum_eq_of_agreesOn hagr hheadSub
      have hsep :=
        lemma55HeadTail_disjoint b b' u x hu πi hfix i
      have hzero := hz i
      rw [hsum,hsplit] at hzero
      unfold indexSetSum at hzero
      rw [Finset.sum_union hsep] at hzero
      fold indexSetSum σ (H i) at hzero
      fold indexSetSum σ (I i) at hzero
      rw [hhead] at hzero
      simp [z]
      abel_nf at hzero ⊢
      exact hzero
    · intro htail i
      have hui := (hu i).2
      have hxi := (Finset.mem_filter.mp hx).2.2 i
      have hux : (u i).val ≤ (x i).val := by
        simp [paperPos] at hui hxi
        omega
      have hsum :
          indexedIntervalSum
              (applyPositionPerm σ (πi i)) (u i) (x i) =
            indexSetSum σ (constraintSet u x πi i) := by
        simpa [constraintSet,applyPositionPerm] using
          permuted_interval_sum_eq σ (Equiv.refl _) (πi i)
            (u i) (x i) hux
      have hsplit :=
        lemma55_constraint_split b b' u x hu hx πi hfix i
      have hheadSub :
          H i ⊆ F :=
        lemma55HeadSet_subset_window b b' u hu πi hfix i
      have hhead :
          indexSetSum σ (H i) = indexSetSum τ (H i) :=
        Section5External.indexSetSum_eq_of_agreesOn hagr hheadSub
      have hsep :=
        lemma55HeadTail_disjoint b b' u x hu πi hfix i
      rw [hsum,hsplit]
      unfold indexSetSum
      rw [Finset.sum_union hsep]
      fold indexSetSum σ (H i)
      fold indexSetSum σ (I i)
      rw [hhead]
      have hi := htail i
      simp [z] at hi
      abel_nf at hi ⊢
      exact hi
  rw [hevent]
  have hlaw :=
    Section5External.conditional_nested_images_chainMass
      S τ hτ F I hdisj hnested
      (tailSizes b' x) hcard z
  rw [hlaw]
  exact hchain z

theorem lemma55_fixed_x_pi_mass_le
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b b' : Fin S.card)
    (hb2 : 2 ≤ paperPos b)
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
      b b' hb2 hgap x hx hTcard
  have hchain :
      ∀ z : Fin P.D → ZMod p,
        chainMass T (tailSizes b' x) z ≤
          chainUpperBound p T.card (chainConstant P.D)
            (tailSizes b' x) := by
    intro z
    exact chainConstant_spec P.D hD p hp T hT2
      (tailSizes b' x) htuple z
  simpa [T,F,hTcard] using
    lemma55_fixed_tail_conditional_bound
      S τ hτ b b' u x hu hx πi hfix
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
      hα0 hαh P hp S hreg b b' hb2 hgap
      u x hu hx πi hfix π
  let s := S.card - (5 * P.D + 1)
  have hsum :
      (∑ x ∈ X, weight x) ≤
        lemma43LHS p s P.D (chainConstant P.D) := by
    apply Section5External.chainUpperBound_sum_le_lemma43
      (chainConstant P.D) X (fun x => tailSizes b' x)
    · intro x hx
      exact Section5External.tailSizes_valid
        b b' hb2 hgap x hx rfl
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
    · exact le_of_lt (chainConstant_pos P.D)
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
