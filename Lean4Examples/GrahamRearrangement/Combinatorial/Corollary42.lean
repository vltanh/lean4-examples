import Lean4Examples.GrahamRearrangement.Combinatorial.Corollary14

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Corollary 4.2
-/

noncomputable section

theorem chainGap_pos {k n : ℕ} (hk : 0 < k)
    (m : Fin k → ℕ) (hm : IsChainSizeTuple n m)
    (i : Fin (k + 1)) :
    0 < chainGap n m i := by
  rcases hm with ⟨hmono, hrange⟩
  unfold chainGap extendedSize
  by_cases hi0 : i.val = 0
  · subst hi0
    have hfirst := (hrange ⟨0, hk⟩).1
    simp [hk, hfirst]
  · have hile : i.val ≤ k := Nat.le_of_lt_succ i.isLt
    by_cases hik : i.val = k
    · subst hik
      have hkpred : k - 1 < k := by omega
      have hlast := (hrange ⟨k - 1, hkpred⟩).2
      simp [hi0, hk, hlast]
    · have hilk : i.val < k := lt_of_le_of_ne hile hik
      have him1 : i.val - 1 < k := lt_of_le_of_lt (Nat.sub_le _ _) hilk
      have hii : i.val < k := hilk
      have hlt :
          m ⟨i.val - 1, him1⟩ < m ⟨i.val, hii⟩ := by
        apply hmono
        simp only [Fin.mk_lt_mk]
        omega
      simp [hi0, hile, hik, hilk, hlt]

theorem chainFactor_nonneg {p n gap : ℕ} (C : ℝ)
    (hC : 0 ≤ C) :
    0 ≤ chainFactor p n C gap := by
  unfold chainFactor
  positivity

theorem chain_factor_from_cor14 {p k : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (ε Cε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hCε : 0 < Cε)
    (hCor :
      ∀ (T : Finset (ZMod p)), 2 ≤ T.card →
      ∀ (r : ℕ), 0 < r →
        (r : ℝ) ≤ (1 - ε) * T.card →
        ∀ q : ZMod p,
          sliceMass T r q ≤
            1 / (p : ℝ) +
              Cε * Real.sqrt (Real.log (T.card : ℝ)) /
                ((T.card : ℝ) * Real.sqrt (r : ℝ)))
    (T : Finset (ZMod p)) (hTS : T ⊆ S)
    (hTlower : ε * S.card ≤ (T.card : ℝ))
    (r : ℕ) (hr : 0 < r)
    (hrfrac : (r : ℝ) ≤ (1 - ε) * T.card)
    (q : ZMod p) :
    let Ck := Cε / ε
    sliceMass T r q ≤ chainFactor p S.card Ck r := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro Ck
  have hT2 : 2 ≤ T.card := by
    have hstrict : (r : ℝ) < T.card := by
      have : 0 < ε * T.card := by
        have hTpos : 0 < (T.card : ℝ) := by
          have hSpos : 0 < (S.card : ℝ) := by positivity
          nlinarith [hTlower]
        positivity
      nlinarith [hrfrac]
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    exact_mod_cast (show (2 : ℝ) ≤ T.card by nlinarith)
  have hbase := hCor T hT2 r hr hrfrac q
  have hcardTS : T.card ≤ S.card := Finset.card_le_card hTS
  have hlog :
      Real.sqrt (Real.log (T.card : ℝ)) ≤
        Real.sqrt (Real.log (S.card : ℝ)) := by
    apply Real.sqrt_le_sqrt
    apply Real.strictMonoOn_log.monotoneOn
    · have : (0 : ℝ) < T.card := by positivity
      exact le_of_lt this
    · exact_mod_cast hcardTS
  have hTpos : 0 < (T.card : ℝ) := by positivity
  have hSpos : 0 < (S.card : ℝ) := by positivity
  have hrroot : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
  have hcoeff :
      Cε * Real.sqrt (Real.log (T.card : ℝ)) /
          ((T.card : ℝ) * Real.sqrt (r : ℝ))
        ≤ (Cε / ε) * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (r : ℝ)) := by
    have hεS : ε * (S.card : ℝ) ≤ T.card := hTlower
    have hlognonneg : 0 ≤ Real.sqrt (Real.log (T.card : ℝ)) :=
      Real.sqrt_nonneg _
    have hCnonneg : 0 ≤ Cε := le_of_lt hCε
    apply (div_le_div_iff_of_pos_right hrroot).2
    apply (div_le_div_iff₀ hTpos hSpos).2
    have hεpos := hε0
    field_simp
    nlinarith
  unfold chainFactor
  nlinarith

def incrementPartitionFamily {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ) :
    Finset (Fin (k + 1) → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter fun Δ =>
    (∀ i, Δ i ⊆ S ∧ (Δ i).card = chainGap S.card m i) ∧
    (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
    (∀ x, x ∈ S ↔ ∃ i, x ∈ Δ i)

def chainIncrements {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p)) :
    Fin (k + 1) → Finset (ZMod p) :=
  fun i =>
    if h0 : i.val = 0 then R ⟨0, by omega⟩
    else if hk : i.val = k then S \ R ⟨k - 1, by omega⟩
    else
      R ⟨i.val, by omega⟩ \ R ⟨i.val - 1, by omega⟩

def incrementsToChain {p k : ℕ} [NeZero p]
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Fin k → Finset (ZMod p) :=
  fun i => ∪ j ∈ Finset.Iic i.val, Δ ⟨j, by omega⟩

theorem chainIncrements_mem {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ) {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    chainIncrements S R ∈ incrementPartitionFamily S m := by
  classical
  rcases Finset.mem_filter.mp hR with ⟨_, hdata, hnested⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro i
    unfold chainIncrements chainGap extendedSize
    split <;> split
    · subst i
      simpa using hdata ⟨0,hk⟩
    · rename_i h0 hlast
      have hi : i.val < k := by omega
      have hprev : R ⟨i.val - 1, by omega⟩ ⊆ R ⟨i.val,hi⟩ :=
        hnested _ _ (by simp; omega)
      constructor
      · exact Finset.sdiff_subset.trans (hdata ⟨i.val,hi⟩).1
      · rw [Finset.card_sdiff hprev,
          (hdata ⟨i.val,hi⟩).2,
          (hdata ⟨i.val-1,by omega⟩).2]
        simp [h0, hi]
    · subst i
      have hlastData := hdata ⟨k-1,by omega⟩
      exact ⟨by intro x hx; exact (Finset.mem_sdiff.mp hx).1,
        by rw [Finset.card_sdiff hlastData.1, hlastData.2]; simp [hk]⟩
  · intro i j hij
    unfold chainIncrements
    by_cases h : i.val < j.val
    · exact chain_increment_disjoint_of_lt S R hnested h
    · have : j.val < i.val := by omega
      exact (chain_increment_disjoint_of_lt S R hnested this).symm
  · intro x
    constructor
    · intro hx
      by_cases hxk : x ∈ R ⟨k-1,by omega⟩
      · let i : Fin k := Finset.min' (Finset.univ.filter fun i : Fin k => x ∈ R i)
          ⟨⟨k-1,by omega⟩, by simp [hxk]⟩
        exact ⟨⟨i.val,by omega⟩,
          x_mem_chain_increment_of_min S R i hx⟩
      · exact ⟨⟨k,by omega⟩, by simp [chainIncrements,hx,hxk]⟩
    · rintro ⟨i,hi⟩
      exact chain_increment_subset S R hdata i hi

theorem incrementsToChain_mem {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    incrementsToChain Δ ∈ chainFamily S m := by
  classical
  rcases Finset.mem_filter.mp hΔ with ⟨_, hdata, hdisj, hcover⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    constructor
    · intro x hx
      simp [incrementsToChain] at hx
      rcases hx with ⟨j,hji,hx⟩
      exact (hdata ⟨j,by omega⟩).1 hx
    · have hcardUnion :=
        Finset.card_biUnion_of_pairwise_disjoint
          (Finset.Iic i.val)
          (fun j => Δ ⟨j,by omega⟩)
          (by
            intro a ha b hb hab
            exact hdisj ⟨a,by omega⟩ ⟨b,by omega⟩
              (by simpa using hab))
      rw [hcardUnion]
      have htel :
          ∑ j ∈ Finset.Iic i.val,
            chainGap S.card m ⟨j,by omega⟩ =
            m i := chainGap_prefix_sum m (Finset.mem_filter.mp hΔ).2.1 i
      simpa [incrementsToChain, (hdata _).2] using htel
  · intro i j hij
    intro x hx
    simp [incrementsToChain] at hx ⊢
    rcases hx with ⟨r,hri,hx⟩
    exact ⟨r, le_trans hri hij, hx⟩

theorem chain_increment_bijection {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p)) (m : Fin k → ℕ) :
    (chainFamily S m).card = (incrementPartitionFamily S m).card := by
  classical
  apply Finset.card_bij
    (fun R _ => chainIncrements S R)
  · intro R hR
    exact chainIncrements_mem hk S m hR
  · intro R hR R' hR' hEq
    exact chain_eq_of_increments_eq S R R' hEq
  · intro Δ hΔ
    refine ⟨incrementsToChain Δ, incrementsToChain_mem hk S m hΔ, ?_⟩
    exact increments_chain_inverse S Δ hΔ

def chainGapTarget {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : Fin k → ZMod p)
    (i : Fin (k + 1)) : ZMod p :=
  if h0 : i.val = 0 then z ⟨0,by omega⟩
  else if hk : i.val = k then subsetSum S - z ⟨k-1,by omega⟩
  else z ⟨i.val,by omega⟩ - z ⟨i.val-1,by omega⟩

theorem chain_sum_event_iff_increment_targets {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p))
    (hR : R ∈ chainFamily S (fun i => (R i).card))
    (z : Fin k → ZMod p) :
    (∀ i, subsetSum (R i) = z i) ↔
      ∀ i : Fin (k + 1),
        subsetSum (chainIncrements S R i) = chainGapTarget S z i := by
  constructor
  · intro hz i
    unfold chainGapTarget chainIncrements
    split <;> split
    · subst i; simpa using hz ⟨0,hk⟩
    · rename_i h0 hlast
      have hi : i.val < k := by omega
      have hsub := chain_nested_from_mem hR
      rw [subsetSum_sdiff (hsub _ _ (by simp; omega))]
      simpa using sub_eq_sub_iff_add_eq_add.mpr
        (congrArg id (hz ⟨i.val,hi⟩))
    · subst i
      rw [subsetSum_sdiff (chain_last_subset_from_mem hR)]
      simp [hz]
  · intro hΔ i
    have hprefix :
        subsetSum (R i) =
          ∑ j : Fin (i.val + 1),
            subsetSum (chainIncrements S R
              ⟨j.val,by omega⟩) :=
      subsetSum_eq_sum_chain_increments S R hR i
    rw [hprefix]
    simp_rw [hΔ]
    exact chainGapTarget_prefix_telescopes S z i

def exposureOrder {k : ℕ} (j : Fin (k + 1)) :
    List (Fin (k + 1)) :=
  (List.ofFn fun i : Fin j.val => ⟨i.val,by omega⟩) ++
  (List.ofFn fun i : Fin (k - j.val) =>
    ⟨k - i.val,by omega⟩)

theorem exposureOrder_nodup {k : ℕ} (j : Fin (k + 1)) :
    (exposureOrder j).Nodup := by
  unfold exposureOrder
  apply List.Nodup.append
  · exact List.nodup_ofFn.mpr (by intro a b h; exact Fin.ext (Fin.mk.inj h))
  · exact List.nodup_ofFn.mpr (by intro a b h; apply Fin.ext; omega)
  · intro x hxL hxR
    simp at hxL hxR
    omega

theorem mem_exposureOrder_iff {k : ℕ} (j : Fin (k + 1))
    (i : Fin (k + 1)) :
    i ∈ exposureOrder j ↔ i ≠ j := by
  unfold exposureOrder
  simp
  omega

/-- Sequential exposure of all increments except j.  Conditional on previously
exposed increments, the next increment is a uniform subset of the remaining
ground set with its prescribed gap size. -/
theorem incrementPartition_product_bound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (j : Fin (k + 1))
    (b : Fin (k + 1) → ℝ)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p),
          (chainGap S.card m j : ℕ) ≤ U.card →
          chainGap S.card m i ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (target : Fin (k + 1) → ZMod p) :
    uniformMass (incrementPartitionFamily S m)
      (fun Δ => ∀ i, i ≠ j → subsetSum (Δ i) = target i) ≤
        ∏ i ∈ Finset.univ.erase j, b i := by
  classical
  let order := exposureOrder j
  have horder := exposureOrder_nodup j
  induction order using List.reverseRecOn with
  | nil =>
      simp [incrementPartitionFamily]
  | append_singleton order i ih =>
      have hi : i ≠ j := (mem_exposureOrder_iff j i).mp
        (by simp [exposureOrder, order])
      let Prev : (Fin (k + 1) → Finset (ZMod p)) → Prop :=
        fun Δ => ∀ r ∈ order, subsetSum (Δ r) = target r
      rw [uniformMass_chain_rule_on_partition
        (incrementPartitionFamily S m) Prev
        (fun Δ => subsetSum (Δ i) = target i)]
      apply mul_le_mul
      · exact ih
      · apply uniformExpectation_le_const
        · exact incrementPartitionFamily_nonempty S m hm
        · intro Δ hΔ
          let U := S \ ∪ r ∈ order.toFinset, Δ r
          have hUj :
              chainGap S.card m j ≤ U.card :=
            unexposed_gap_le_remaining S m hm j order hΔ horder
          have hUi :
              chainGap S.card m i ≤ U.card :=
            unexposed_gap_le_remaining S m hm i order hΔ horder
          have hcond :=
            increment_conditional_uniform S m hm order i hΔ horder
          rw [hcond]
          exact hstep i hi U hUj hUi (target i)
      · positivity
      · positivity

theorem chainMass_fixed_gap_product_bound {p k : ℕ} [NeZero p]
    (hk : 0 < k)
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (j : Fin (k + 1))
    (b : Fin (k + 1) → ℝ)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p),
          chainGap S.card m j ≤ U.card →
          chainGap S.card m i ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (z : Fin k → ZMod p) :
    chainMass S m z ≤
      ∏ i ∈ Finset.univ.erase j, b i := by
  classical
  unfold chainMass
  have hmass :
      uniformMass (chainFamily S m)
        (fun R => ∀ i, subsetSum (R i) = z i) =
      uniformMass (incrementPartitionFamily S m)
        (fun Δ => ∀ i, subsetSum (Δ i) = chainGapTarget S z i) := by
    exact uniformMass_bij
      (chainIncrements S)
      (chain_increment_bijection_equiv hk S m)
      (fun R hR => chain_sum_event_iff_increment_targets hk S R hR z)
  rw [hmass]
  apply le_trans
    (uniformMass_mono_on _ _ _
      (by intro Δ hΔ hall i hij; exact hall i))
  exact incrementPartition_product_bound S m hm j b hstep
    (chainGapTarget S z)

/-- Corollary 4.2. -/
theorem corollary42 : Corollary42Statement := by
  intro k hk
  let ε : ℝ := 1 / (k + 1 : ℝ)
  have hε0 : 0 < ε := by
    dsimp [ε]
    positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    have : (1 : ℝ) < k + 1 := by exact_mod_cast Nat.succ_lt_succ hk
    exact one_div_lt_one this
  rcases corollary14 ε hε0 hε1 with ⟨Cε, hCε, hCor⟩
  let Ck := Cε / ε
  have hCk : 0 < Ck := div_pos hCε hε0
  refine ⟨Ck, hCk, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hm z
  obtain ⟨j, hj⟩ :=
    Section4External.exists_large_chain_gap m hm
  have hgapRemain :
      (chainGap S.card m j : ℝ) ≥ ε * S.card := by
    dsimp [ε]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hj
  have hprod :
      chainMass S m z ≤
        ∏ i ∈ Finset.univ.erase j,
          chainFactor p S.card Ck (chainGap S.card m i) := by
    apply chainMass_fixed_gap_product_bound hk S m hm j
      (fun i => chainFactor p S.card Ck (chainGap S.card m i))
    intro i hij T hremain hgapfit q
    have hgap : 0 < chainGap S.card m i :=
      chainGap_pos hk m hm i
    have hTlower : ε * S.card ≤ (T.card : ℝ) := by
      exact_mod_cast le_trans (by exact_mod_cast hgapRemain) hremain
    have hfrac :
        (chainGap S.card m i : ℝ) ≤ (1 - ε) * T.card := by
      have hrem :
          ε * (T.card : ℝ) ≤ chainGap S.card m j := by
        have hTle : T.card ≤ S.card := by
          exact remaining_subset_card_le S T
        nlinarith [hgapRemain]
      exact_mod_cast hgapfit
      nlinarith
    have hcorT :
        ∀ (U : Finset (ZMod p)), 2 ≤ U.card →
        ∀ (r : ℕ), 0 < r →
          (r : ℝ) ≤ (1 - ε) * U.card →
          ∀ q : ZMod p,
            sliceMass U r q ≤
              1 / (p : ℝ) +
                Cε * Real.sqrt (Real.log (U.card : ℝ)) /
                  ((U.card : ℝ) * Real.sqrt (r : ℝ)) := by
      intro U hU r hr hrf q'
      exact hCor p hp U hU r hr hrf q'
    exact chain_factor_from_cor14 hp S hS ε Cε hε0 hε1 hCε
      hcorT T (remaining_subset S T) hTlower
      (chainGap S.card m i) hgap hfrac q
  have hnonneg : ∀ r : Fin (k + 1),
      0 ≤ ∏ i ∈ Finset.univ.erase r,
        chainFactor p S.card Ck (chainGap S.card m i) := by
    intro r
    positivity
  calc
    chainMass S m z
      ≤ ∏ i ∈ Finset.univ.erase j,
          chainFactor p S.card Ck (chainGap S.card m i) := hprod
    _ ≤ ∑ r : Fin (k + 1),
          ∏ i ∈ Finset.univ.erase r,
            chainFactor p S.card Ck (chainGap S.card m i) := by
          exact Finset.single_le_sum
            (fun r _ => hnonneg r) (Finset.mem_univ j)
    _ = chainUpperBound p S.card Ck m := by
          rfl

theorem chainMass_one_eq_sliceMass {p r : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    chainMass S (fun _ : Fin 1 => r) (fun _ : Fin 1 => z) =
      sliceMass S r z := by
  unfold chainMass sliceMass chainFamily
  apply uniformMass_congr
  · ext R
    simp [IsChainSizeTuple]
  · intro R hR
    constructor
    · intro h
      simpa using h (0 : Fin 1)
    · intro h i
      fin_cases i
      exact h

/-- The k=1 form used repeatedly in Section 5. -/
theorem corollary42_one_bound {p r : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hr : 0 < r) (hrS : r < S.card) (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S r z ≤
      (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (r : ℝ))) +
      (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt ((S.card - r : ℕ) : ℝ))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let m : Fin 1 → ℕ := fun _ => r
  let z' : Fin 1 → ZMod p := fun _ => z
  have hm : IsChainSizeTuple S.card m := by
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b
      simp at hab
    · intro i
      fin_cases i
      exact ⟨hr, hrS⟩
  have h :=
    chainConstant_spec 1 (by norm_num) p hp S hS m hm z'
  rw [chainMass_one_eq_sliceMass S z] at h
  simpa [chainUpperBound, chainFactor, chainGap, extendedSize, m, z'] using h

end

end GrahamRearrangement
