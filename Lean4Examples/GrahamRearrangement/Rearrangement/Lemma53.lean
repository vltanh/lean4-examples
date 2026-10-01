import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma56

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.3

The blocked-choice event is split into the right-extending event E₁ and the
left-extending event E₂, bounded by Lemmas 5.5 and 5.6 respectively.
-/

noncomputable section

theorem swap_fixedOutside
    {n : ℕ} (b b' y : Fin n)
    (hby : paperPos b < paperPos y)
    (hyb' : paperPos y ≤ paperPos b') :
    FixedOutside b b' (Equiv.swap b y) := by
  intro i hi
  have hib : i ≠ b := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  have hiy : i ≠ y := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  exact Equiv.swap_apply_of_ne_of_ne hib hiy

/-- Failure of B₀ says that the subset-sum map is injective on the local
5D-window even after applying any admissible permutation fixing the prefix.
This is the precise local-injectivity statement used in the proof of Lemma 5.3. -/
theorem local_subset_sum_injective_after_admissible
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {J J' : Finset (Fin n)}
    (hJ : J ⊆ forwardWindow b (5 * D))
    (hJ' : J' ⊆ forwardWindow b (5 * D))
    (hne : J ≠ J') :
    indexSetSum (applyPositionPerm σ π) J ≠
      indexSetSum (applyPositionPerm σ π) J' := by
  intro heq
  have hπJ :
      J.image π ⊆ forwardWindow b (10 * D) :=
    Section5External.admissible_local_image_subset
      b π hadm hfix J hJ
  have hπJ' :
      J'.image π ⊆ forwardWindow b (10 * D) :=
    Section5External.admissible_local_image_subset
      b π hadm hfix J' hJ'
  have h10_20 :
      forwardWindow b (10 * D) ⊆ forwardWindow b (20 * D) := by
    intro x hx
    simp only [forwardWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    omega
  have himageNe : J.image π ≠ J'.image π := by
    intro h
    apply hne
    apply Finset.ext
    intro x
    have hinj := π.injective
    simpa using congrArg (fun K => x ∈ K.image π) h
  have hsum :
      indexSetSum σ (J.image π) =
        indexSetSum σ (J'.image π) := by
    simpa [indexSetSum_applyPositionPerm_image] using heq
  exact h0 ⟨b, hb, hbfar,
    J.image π, J'.image π,
    fun x hx => h10_20 (hπJ hx),
    fun x hx => h10_20 (hπJ' hx),
    himageNe, hsum⟩

theorem local_nonzero_after_admissible
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {J : Finset (Fin n)}
    (hJne : J.Nonempty)
    (hJ : J ⊆ forwardWindow b (5 * D)) :
    indexSetSum (applyPositionPerm σ π) J ≠ 0 := by
  have hne : J ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hJne
  have hinj :=
    local_subset_sum_injective_after_admissible
      σ b hb hbfar h0 π hadm hfix
      hJ (by simp) hne
  simpa using hinj

def RightBlockedWitness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  ∃ s t : Fin n,
    paperPos b < paperPos s ∧ paperPos s ≤ paperPos y ∧
    paperPos b + 5 * D < paperPos t ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
      s t = 0

def LeftBlockedWitness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  ∃ s t : Fin n,
    paperPos s < paperPos b ∧
    paperPos b ≤ paperPos t ∧ paperPos t < paperPos y ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
      s t = 0

/-- This is the dichotomy in the first paragraph of the proof of Lemma 5.3:
a blocked interval cannot be wholly contained in the 5D-window, so it must
extend to the right or to the left. -/
theorem blocked_witness_has_side
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {y : Fin n} (hy : y ∈ blockedCandidates D σ b π) :
    RightBlockedWitness σ b π y ∨
      LeftBlockedWitness σ b π y := by
  have hblocked := (Finset.mem_filter.1 hy).2
  rcases hblocked with ⟨hby, hy5, s, t, hs2, hst, hzero, hcross⟩
  by_cases hright : paperPos b + 5 * D < paperPos t
  · left
    have hbs : paperPos b < paperPos s := by
      rcases hcross with hcross | hcross
      · exact hcross.1
      · by_contra h
        have hsb : paperPos s ≤ paperPos b := le_of_not_gt h
        have htb : paperPos t < paperPos y := hcross.2
        omega
    have hsy : paperPos s ≤ paperPos y := by
      rcases hcross with hcross | hcross
      · exact hcross.2
      · omega
    exact ⟨s, t, hbs, hsy, hright, hzero⟩
  · have ht5 : paperPos t ≤ paperPos b + 5 * D := le_of_not_gt hright
    by_cases hleft : paperPos s < paperPos b
    · right
      have hbt : paperPos b ≤ paperPos t := by
        rcases hcross with hcross | hcross
        · omega
        · exact hcross.1
      have hty : paperPos t < paperPos y := by
        rcases hcross with hcross | hcross
        · omega
        · exact hcross.2
      exact ⟨s, t, hleft, hbt, hty, hzero⟩
    · have hbs : paperPos b ≤ paperPos s := le_of_not_gt hleft
      have hty : paperPos t ≤ paperPos b + 5 * D := ht5
      let J := (indexInterval s t).image (Equiv.swap b y)
      have hJne : J.Nonempty := by
        refine ⟨Equiv.swap b y s, ?_⟩
        simp only [J, Finset.mem_image]
        exact ⟨s, by
          simp [indexInterval]
          exact ⟨le_rfl, by simpa [paperPos] using le_of_lt hst⟩, rfl⟩
      have hJsub : J ⊆ forwardWindow b (5 * D) := by
        intro x hx
        rcases Finset.mem_image.1 hx with ⟨u, hu, rfl⟩
        simp only [indexInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hu
        simp only [forwardWindow, Finset.mem_filter,
          Finset.mem_univ, true_and]
        by_cases hub : u = b
        · subst u
          simp [hby, hy5, paperPos]
        · by_cases huy : u = y
          · subst u
            simp [paperPos]
            omega
          · rw [Equiv.swap_apply_of_ne_of_ne hub huy]
            simp [paperPos] at hbs ht5 ⊢
            omega
      have hJzero :
          indexSetSum (applyPositionPerm σ π) J = 0 := by
        have hab : s.val ≤ t.val := by
          simpa [paperPos] using le_of_lt hst
        rw [← indexedIntervalSum_after_perm
          (applyPositionPerm σ π) (Equiv.swap b y) s t hab]
        exact hzero
      exact (local_nonzero_after_admissible
        σ b hb hbfar h0 π hadm hfix hJne hJsub) hJzero

/-- At the pigeonhole stage only the blocked choices y_i are known to be
distinct. Distinctness of the far endpoints is proved separately below, just
as in the paper. -/
theorem blocked_family_side_split
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (hblocked :
      2 * D ≤ (blockedCandidates D σ b π).card) :
    (∃ y : Fin D → Fin n,
      Function.Injective y ∧
      ∀ i, y i ∈ blockedCandidates D σ b π ∧
        RightBlockedWitness σ b π (y i)) ∨
    (∃ y : Fin D → Fin n,
      Function.Injective y ∧
      ∀ i, y i ∈ blockedCandidates D σ b π ∧
        LeftBlockedWitness σ b π (y i)) := by
  apply Section5External.two_colour_extract
    D (blockedCandidates D σ b π)
    (RightBlockedWitness σ b π)
    (LeftBlockedWitness σ b π)
    hblocked
  intro y hy
  exact blocked_witness_has_side
    σ b hb hbfar h0 π hadm hfix hy

/-- The distinctness argument for the right endpoints t_i in E₁, exactly as
on pp. 25--26 of the paper. -/
theorem right_witness_endpoints_injective
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (y s t : Fin D → Fin n)
    (hyinj : Function.Injective y)
    (hw : ∀ i,
      paperPos b < paperPos (y i) ∧
      paperPos (y i) ≤ paperPos b' ∧
      paperPos b < paperPos (s i) ∧
      paperPos (s i) ≤ paperPos (y i) ∧
      paperPos b' < paperPos (t i) ∧
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b (y i)))
        (s i) (t i) = 0) :
    Function.Injective t := by
  intro i j ht
  by_contra hij
  have hyne : y i ≠ y j := hyinj hij
  wlog hylt : paperPos (y i) < paperPos (y j)
      generalizing i j
  · have hygt : paperPos (y j) < paperPos (y i) := by
      have := lt_or_gt_of_ne
        (show paperPos (y i) ≠ paperPos (y j) by
          simpa [paperPos] using congrArg Fin.val hyne)
      exact this.resolve_left hylt
    exact (this j i ht.symm hij.symm hygt).symm
  let Ji := (indexInterval (s i) b').image (Equiv.swap b (y i))
  let Jj := (indexInterval (s j) b').image (Equiv.swap b (y j))
  have hJi : Ji ⊆ forwardWindow b (5 * D) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨u, hu, rfl⟩
    simp only [indexInterval, Finset.mem_filter,
      Finset.mem_univ, true_and] at hu
    simp only [forwardWindow, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hi := hw i
    by_cases hub : u = b
    · subst u
      simp [hi.1, hi.2.1, hgap, paperPos]
    · by_cases huy : u = y i
      · subst u
        simp [paperPos]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hub huy]
        simp [paperPos] at hi hgap ⊢
        omega
  have hJj : Jj ⊆ forwardWindow b (5 * D) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨u, hu, rfl⟩
    simp only [indexInterval, Finset.mem_filter,
      Finset.mem_univ, true_and] at hu
    simp only [forwardWindow, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hj := hw j
    by_cases hub : u = b
    · subst u
      simp [hj.1, hj.2.1, hgap, paperPos]
    · by_cases huy : u = y j
      · subst u
        simp [paperPos]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hub huy]
        simp [paperPos] at hj hgap ⊢
        omega
  have hJne : Ji ≠ Jj := by
    intro heq
    have hyjJi : y j ∈ Ji := by
      refine Finset.mem_image.2 ⟨y j, ?_, ?_⟩
      · simp [indexInterval]
        have hi := hw i
        have hj := hw j
        simp [paperPos] at hi hj hylt ⊢
        omega
      · have hneqb : y j ≠ b := by
          intro h
          subst h
          exact (not_lt_of_ge (paperPos_pos b)) (hw j).1
        have hneqyi : y j ≠ y i := Ne.symm hyne
        exact (Equiv.swap_apply_of_ne_of_ne hneqb hneqyi).symm
    have hyjJj : y j ∉ Jj := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨u, hu, hswap⟩
      have : u = b := by
        exact Equiv.swap_eq_iff.mp hswap |>.resolve_right (by
          intro h; subst h; simpa using (Equiv.swap_apply_right b (y j)))
      subst u
      have hj := hw j
      simp [indexInterval, paperPos] at hu hj
      omega
    exact hyjJj (by simpa [heq] using hyjJi)
  have hsumEq :
      indexSetSum (applyPositionPerm σ π) Ji =
        indexSetSum (applyPositionPerm σ π) Jj := by
    -- Split each zero interval at b'. The tails are identical because t_i=t_j,
    -- so the local contributions must agree.
    have hi := hw i
    have hj := hw j
    have hsplit_i :=
      swap_interval_split_right
        (applyPositionPerm σ π) b b' (y i) (s i) (t i)
        hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1
    have hsplit_j :=
      swap_interval_split_right
        (applyPositionPerm σ π) b b' (y j) (s j) (t j)
        hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2.1
    rw [hi.2.2.2.2.2] at hsplit_i
    rw [hj.2.2.2.2.2, ht] at hsplit_j
    linarith
  exact (local_subset_sum_injective_after_admissible
    σ b hb hbfar h0 π hadm hfix hJi hJj hJne) hsumEq

/-- The analogous distinctness argument for the left endpoints s_i in E₂. -/
theorem left_witness_endpoints_injective
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (y s t : Fin D → Fin n)
    (hyinj : Function.Injective y)
    (hw : ∀ i,
      paperPos b < paperPos (y i) ∧
      paperPos (y i) ≤ paperPos b' ∧
      paperPos (s i) < paperPos b ∧
      paperPos b ≤ paperPos (t i) ∧
      paperPos (t i) < paperPos (y i) ∧
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b (y i)))
        (s i) (t i) = 0) :
    Function.Injective s := by
  intro i j hs
  by_contra hij
  have hyne : y i ≠ y j := hyinj hij
  wlog hylt : paperPos (y i) < paperPos (y j)
      generalizing i j
  · have hygt : paperPos (y j) < paperPos (y i) := by
      have := lt_or_gt_of_ne
        (show paperPos (y i) ≠ paperPos (y j) by
          simpa [paperPos] using congrArg Fin.val hyne)
      exact this.resolve_left hylt
    exact (this j i hs.symm hij.symm hygt).symm
  let Ji := (indexInterval b (t i)).image (Equiv.swap b (y i))
  let Jj := (indexInterval b (t j)).image (Equiv.swap b (y j))
  have hJi : Ji ⊆ forwardWindow b (5 * D) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨u, hu, rfl⟩
    have hi := hw i
    simp only [indexInterval, Finset.mem_filter,
      Finset.mem_univ, true_and] at hu
    simp only [forwardWindow, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hub : u = b
    · subst u
      simp [hi.1, hi.2.1, paperPos]
    · by_cases huy : u = y i
      · subst u
        simp [paperPos]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hub huy]
        simp [paperPos] at hi ⊢
        omega
  have hJj : Jj ⊆ forwardWindow b (5 * D) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨u, hu, rfl⟩
    have hj := hw j
    simp only [indexInterval, Finset.mem_filter,
      Finset.mem_univ, true_and] at hu
    simp only [forwardWindow, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hub : u = b
    · subst u
      simp [hj.1, hj.2.1, paperPos]
    · by_cases huy : u = y j
      · subst u
        simp [paperPos]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hub huy]
        simp [paperPos] at hj ⊢
        omega
  have hJne : Ji ≠ Jj := by
    intro heq
    have hyjJi : y j ∈ Ji := by
      refine Finset.mem_image.2 ⟨y j, ?_, ?_⟩
      · simp [indexInterval]
        have hi := hw i
        have hj := hw j
        simp [paperPos] at hi hj hylt ⊢
        omega
      · have hneqb : y j ≠ b := by
          intro h
          subst h
          exact (not_lt_of_ge (paperPos_pos b)) (hw j).1
        have hneqyi : y j ≠ y i := Ne.symm hyne
        exact (Equiv.swap_apply_of_ne_of_ne hneqb hneqyi).symm
    have hyjJj : y j ∉ Jj := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨u, hu, hswap⟩
      have : u = b := by
        exact Equiv.swap_eq_iff.mp hswap |>.resolve_right (by
          intro h; subst h; simpa using (Equiv.swap_apply_right b (y j)))
      subst u
      simp [indexInterval] at hu
    exact hyjJj (by simpa [heq] using hyjJi)
  have hsumEq :
      indexSetSum (applyPositionPerm σ π) Ji =
        indexSetSum (applyPositionPerm σ π) Jj := by
    have hi := hw i
    have hj := hw j
    have hsplit_i :=
      swap_interval_split_left
        (applyPositionPerm σ π) b (y i) (s i) (t i)
        hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1
    have hsplit_j :=
      swap_interval_split_left
        (applyPositionPerm σ π) b (y j) (s j) (t j)
        hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2.1
    rw [hi.2.2.2.2.2] at hsplit_i
    rw [hj.2.2.2.2.2, hs] at hsplit_j
    linarith
  exact (local_subset_sum_injective_after_admissible
    σ b hb hbfar h0 π hadm hfix hJi hJj hJne) hsumEq

theorem badEvent3_core_side_reduction
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h3 : BadEvent3 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    RightRepairEvent D σ ∨ LeftRepairEvent D σ := by
  classical
  rcases h3 with ⟨b, hb, π, hπadm, hπfix, hblocked⟩
  have hbfar : paperPos b + 30 * D ≤ n := by
    by_contra h
    exact h1 ⟨b, hb, by omega⟩
  have hb2 : 2 ≤ paperPos b :=
    le_trans (by norm_num) (badRightEndpoint_ge_three hb)
  rcases blocked_family_side_split hD σ b hb hbfar h0 π hπadm hπfix hblocked with
    hright | hleft
  · rcases hright with ⟨y, hyinj, hyw⟩
    choose s t hs using fun i => (hyw i).2
    have hw : ∀ i,
        paperPos b < paperPos (y i) ∧
        paperPos (y i) ≤ paperPos b + 5 * D ∧
        paperPos b < paperPos (s i) ∧
        paperPos (s i) ≤ paperPos (y i) ∧
        paperPos b + 5 * D < paperPos (t i) ∧
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (Equiv.swap b (y i)))
          (s i) (t i) = 0 := by
      intro i
      have hyblock := (Finset.mem_filter.1 (hyw i).1).2
      rcases hs i with ⟨hbs, hsy, ht, hz⟩
      exact ⟨hyblock.1, hyblock.2, hbs, hsy, ht, hz⟩
    have hb'lt : b.val + 5 * D < n := by
      simp [paperPos] at hbfar
      omega
    let b' : Fin n := ⟨b.val + 5 * D, hb'lt⟩
    have hgap : paperPos b' - paperPos b = 5 * D := by
      simp [paperPos, b']
    have htinj :=
      right_witness_endpoints_injective
        σ b b' hgap hb hbfar h0 π hπadm hπfix
        y s t hyinj (by
          intro i
          simpa [b', paperPos] using hw i)
    obtain ⟨ρ, htmono⟩ :=
      Section5External.exists_sorting_perm t htinj
    let y' := y ∘ ρ
    let s' := s ∘ ρ
    let t' := t ∘ ρ
    refine Or.inl ⟨b, b', hb2, hbfar, hgap, y', s', ?_, ?_, ?_⟩
    · intro i
      have h := hw (ρ i)
      simpa [y', b', paperPos] using ⟨h.1, h.2.1⟩
    · intro i
      have h := hw (ρ i)
      simpa [s', b', paperPos] using ⟨h.2.2.1, h.2.2.2.1⟩
    · refine ⟨t', ?_, π, hπadm, ?_⟩
      · simp [tailTuples, t', htmono]
        intro i
        have h := hw (ρ i)
        simpa [b', paperPos] using h.2.2.2.2.1
      · intro i
        simpa [y', s', t'] using (hw (ρ i)).2.2.2.2.2
  · rcases hleft with ⟨y, hyinj, hyw⟩
    choose s t hs using fun i => (hyw i).2
    have hw : ∀ i,
        paperPos b < paperPos (y i) ∧
        paperPos (y i) ≤ paperPos b + 5 * D ∧
        paperPos (s i) < paperPos b ∧
        paperPos b ≤ paperPos (t i) ∧
        paperPos (t i) < paperPos (y i) ∧
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (Equiv.swap b (y i)))
          (s i) (t i) = 0 := by
      intro i
      have hyblock := (Finset.mem_filter.1 (hyw i).1).2
      rcases hs i with ⟨hsb, hbt, hty, hz⟩
      exact ⟨hyblock.1, hyblock.2, hsb, hbt, hty, hz⟩
    have hb'lt : b.val + 5 * D < n := by
      simp [paperPos] at hbfar
      omega
    let b' : Fin n := ⟨b.val + 5 * D, hb'lt⟩
    have hgap : paperPos b' - paperPos b = 5 * D := by
      simp [paperPos, b']
    have hsinj :=
      left_witness_endpoints_injective
        σ b b' hgap hb hbfar h0 π hπadm hπfix
        y s t hyinj (by
          intro i
          have h := hw i
          simpa [b', paperPos] using h)
    obtain ⟨ρ, hsmono⟩ :=
      Section5External.exists_sorting_perm s hsinj
    let y' := y ∘ ρ
    let s' := s ∘ ρ
    let t' := t ∘ ρ
    refine Or.inr ⟨b, b', hb2, hbfar, hgap, y', t', ?_, ?_, ?_⟩
    · intro i
      have h := hw (ρ i)
      simpa [y', b', paperPos] using ⟨h.1, h.2.1⟩
    · intro i
      have h := hw (ρ i)
      have htlt : paperPos (t (ρ i)) < paperPos b' := by
        exact lt_of_lt_of_le h.2.2.2.2.1 h.2.1
      exact ⟨h.2.2.2.1, by simpa [t'] using htlt⟩
    · refine ⟨s', ?_, π, hπadm, ?_⟩
      · simp [headTuples, s', hsmono]
        intro i
        simpa [s'] using (hw (ρ i)).2.2.1
      · intro i
        simpa [y', s', t'] using (hw (ρ i)).2.2.2.2.2

def rightRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma55Event σ θ.b θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

def leftRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma56Event σ θ.b θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

theorem rightRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (RightRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Θ := rightRepairParameters S.card P.D
  have hcover :
      ∀ σ ∈ indexedOrderings S,
        RightRepairEvent P.D σ →
          ∃ θ ∈ Θ, rightRepairAtom θ σ := by
    intro σ hσ h
    rcases h with
      ⟨b, b', hb2, hbfar, hgap, y, u, hy, hu, hev⟩
    let θ : RepairParams S.card P.D :=
      ⟨b, b', y, u⟩
    refine ⟨θ, ?_, ?_⟩
    · simp [Θ, rightRepairParameters, θ, hb2, hbfar, hgap, hy, hu]
    · exact hev
  have hpoint :
      ∀ θ ∈ Θ,
        orderingEventMass S (rightRepairAtom θ) ≤
          1 / (S.card : ℝ) ^ 2 := by
    intro θ hθ
    have hpθ := (Finset.mem_filter.1 hθ).2
    have hb'le : paperPos θ.b' ≤ S.card - 2 := by
      have hD := section5Parameters_D_pos hα0 hαh P
      omega
    have hfix :
        ∀ i, FixedOutside θ.b θ.b'
          (Equiv.swap θ.b (θ.y i)) := by
      intro i
      exact swap_fixedOutside θ.b θ.b' (θ.y i)
        (hpθ.2.2.2.1 i).1 (hpθ.2.2.2.1 i).2
    exact lemma5_5 hα0 hαh P hp S hreg
      θ.b θ.b' hpθ.1 hb'le hpθ.2.2.1
      θ.u hpθ.2.2.2.2 hfix
  have hmass :
      orderingEventMass S (RightRepairEvent P.D) ≤
        ((rightRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := by
    unfold orderingEventMass
    exact Section5External.witness_union_bound
      (indexedOrderings S) Θ
      (RightRepairEvent P.D) rightRepairAtom
      (1 / (S.card : ℝ) ^ 2)
      hcover (by simpa [orderingEventMass] using hpoint)
  have hcount :=
    Section5External.rightRepairParameters_card_le
      (n := S.card) (D := P.D)
  calc
    orderingEventMass S (RightRepairEvent P.D)
      ≤ ((rightRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := hmass
    _ ≤ (S.card * (5 * P.D) ^ (2 * P.D) : ℕ) *
          (1 / (S.card : ℝ) ^ 2) := by
          gcongr
          exact_mod_cast hcount
    _ = (5 * P.D : ℝ) ^ (2 * P.D) /
          (S.card : ℝ) := by
          have hnpos : 0 < (S.card : ℝ) := by positivity
          field_simp
          ring
    _ ≤ (1 / 100 : ℝ) := by
          have h100 := P.second_ge_100
          have hC := P.Cα_second
          have hn := hreg.2.1
          have hbound :
              100 * (5 * P.D : ℝ) ^ (2 * P.D) ≤
                (S.card : ℝ) := by
            exact le_trans h100 (le_trans hC hn)
          have hnpos : 0 < (S.card : ℝ) := by positivity
          apply (div_le_iff₀ hnpos).2
          nlinarith

theorem leftRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (LeftRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Θ := leftRepairParameters S.card P.D
  have hcover :
      ∀ σ ∈ indexedOrderings S,
        LeftRepairEvent P.D σ →
          ∃ θ ∈ Θ, leftRepairAtom θ σ := by
    intro σ hσ h
    rcases h with
      ⟨b, b', hb2, hbfar, hgap, y, u, hy, hu, hev⟩
    let θ : RepairParams S.card P.D :=
      ⟨b, b', y, u⟩
    refine ⟨θ, ?_, ?_⟩
    · simp [Θ, leftRepairParameters, θ, hb2, hbfar, hgap, hy, hu]
    · exact hev
  have hpoint :
      ∀ θ ∈ Θ,
        orderingEventMass S (leftRepairAtom θ) ≤
          1 / (S.card : ℝ) ^ 2 := by
    intro θ hθ
    have hpθ := (Finset.mem_filter.1 hθ).2
    have hb'le : paperPos θ.b' ≤ S.card - 2 := by
      have hD := section5Parameters_D_pos hα0 hαh P
      omega
    have hfix :
        ∀ i, FixedOutside θ.b θ.b'
          (Equiv.swap θ.b (θ.y i)) := by
      intro i
      exact swap_fixedOutside θ.b θ.b' (θ.y i)
        (hpθ.2.2.2.1 i).1 (hpθ.2.2.2.1 i).2
    exact lemma5_6 hα0 hαh P hp S hreg
      θ.b θ.b' hpθ.1 hb'le hpθ.2.2.1
      θ.u
      (fun i => ⟨(hpθ.2.2.2.2 i).1,
        le_of_lt (hpθ.2.2.2.2 i).2⟩)
      hfix
  have hmass :
      orderingEventMass S (LeftRepairEvent P.D) ≤
        ((leftRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := by
    unfold orderingEventMass
    exact Section5External.witness_union_bound
      (indexedOrderings S) Θ
      (LeftRepairEvent P.D) leftRepairAtom
      (1 / (S.card : ℝ) ^ 2)
      hcover (by simpa [orderingEventMass] using hpoint)
  have hcount :=
    Section5External.leftRepairParameters_card_le
      (n := S.card) (D := P.D)
  calc
    orderingEventMass S (LeftRepairEvent P.D)
      ≤ ((leftRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := hmass
    _ ≤ (S.card * (5 * P.D) ^ (2 * P.D) : ℕ) *
          (1 / (S.card : ℝ) ^ 2) := by
          gcongr
          exact_mod_cast hcount
    _ = (5 * P.D : ℝ) ^ (2 * P.D) /
          (S.card : ℝ) := by
          have hnpos : 0 < (S.card : ℝ) := by positivity
          field_simp
          ring
    _ ≤ (1 / 100 : ℝ) := by
          have h100 := P.second_ge_100
          have hC := P.Cα_second
          have hn := hreg.2.1
          have hbound :
              100 * (5 * P.D : ℝ) ^ (2 * P.D) ≤
                (S.card : ℝ) := by
            exact le_trans h100 (le_trans hC hn)
          have hnpos : 0 < (S.card : ℝ) := by positivity
          apply (div_le_iff₀ hnpos).2
          nlinarith

/-- Lemma 5.3. -/
theorem lemma5_3
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent3 P.D) ≤
      (1 / 25 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Core : (Fin S.card → ZMod p) → Prop :=
    fun σ =>
      BadEvent3 P.D σ ∧
        ¬ BadEvent0 P.D σ ∧ ¬ BadEvent1 P.D σ
  have hD := section5Parameters_D_pos hα0 hαh P
  have hsubset :
      ∀ σ, Core σ →
        RightRepairEvent P.D σ ∨ LeftRepairEvent P.D σ := by
    intro σ h
    exact badEvent3_core_side_reduction
      hD σ h.1 h.2.1 h.2.2
  have hcore :
      orderingEventMass S Core ≤ (2 / 100 : ℝ) := by
    calc
      orderingEventMass S Core
        ≤ orderingEventMass S
            (fun σ =>
              RightRepairEvent P.D σ ∨
                LeftRepairEvent P.D σ) := by
            apply uniformMass_mono
            intro σ h
            exact hsubset σ h
      _ ≤ orderingEventMass S (RightRepairEvent P.D) +
          orderingEventMass S (LeftRepairEvent P.D) := by
            exact uniformMass_or_le_add
              (indexedOrderings S)
              (RightRepairEvent P.D)
              (LeftRepairEvent P.D)
      _ ≤ 1 / 100 + 1 / 100 := by
            gcongr
            · exact rightRepairEvent_mass hα0 hαh P hp S hreg
            · exact leftRepairEvent_mass hα0 hαh P hp S hreg
      _ = 2 / 100 := by norm_num
  have h0 := lemma5_4 hα0 hαh P hp S hreg
  have h1 := lemma5_1 hα0 hαh P hp S hreg
  have htotal :=
    uniformMass_le_two_exceptions
      (indexedOrderings S)
      (BadEvent3 P.D) (BadEvent0 P.D) (BadEvent1 P.D)
      (2 / 100 : ℝ)
      (by simpa [orderingEventMass, Core] using hcore)
  nlinarith

end

end GrahamRearrangement
