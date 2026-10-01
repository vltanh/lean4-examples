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

theorem chain_nested_from_mem {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    ∀ i j, i ≤ j → R i ⊆ R j := by
  exact (Finset.mem_filter.mp hR).2.2

theorem chain_data_from_mem {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    ∀ i, R i ⊆ S ∧ (R i).card = m i := by
  exact (Finset.mem_filter.mp hR).2.1

theorem subsetSum_sdiff {p : ℕ} [NeZero p]
    {A B : Finset (ZMod p)} (hAB : A ⊆ B) :
    subsetSum (B \ A) = subsetSum B - subsetSum A := by
  unfold subsetSum
  have hsum := Finset.sum_sdiff hAB (fun x => x)
  rw [← hsum]
  abel

theorem chain_prefix_union_eq {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (i : Fin k) :
    (∪ j ∈ Finset.Iic i.val,
      chainIncrements S R ⟨j,by omega⟩) = R i := by
  classical
  induction i.val with
  | zero =>
      simp [chainIncrements]
  | succ r ih =>
      let ip : Fin k := ⟨r,by omega⟩
      have hprev : R ip ⊆ R i :=
        chain_nested_from_mem hR ip i (by simp [ip]; omega)
      have hinc :
          chainIncrements S R ⟨r+1,by omega⟩ =
            R i \ R ip := by
        simp [chainIncrements,ip]
      have hunion :
          (∪ j ∈ Finset.Iic (r + 1),
              chainIncrements S R ⟨j,by omega⟩) =
            (∪ j ∈ Finset.Iic r,
              chainIncrements S R ⟨j,by omega⟩) ∪
              chainIncrements S R ⟨r+1,by omega⟩ := by
        ext x
        simp
        constructor
        · rintro ⟨j,hj,hx⟩
          by_cases hjr : j ≤ r
          · exact Or.inl ⟨j,hjr,hx⟩
          · have : j = r + 1 := by omega
            subst j
            exact Or.inr hx
        · rintro (⟨j,hj,hx⟩ | hx)
          · exact ⟨j,by omega,hx⟩
          · exact ⟨r+1,le_rfl,hx⟩
      rw [hunion, ih ip, hinc]
      exact Finset.union_sdiff_of_subset hprev

theorem chain_all_increments_union_eq {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    (∪ j : Fin (k + 1), chainIncrements S R j) = S := by
  classical
  let last : Fin k := ⟨k-1,by omega⟩
  have hlastSub := (chain_data_from_mem hR last).1
  have hprefix := chain_prefix_union_eq hk S hR last
  rw [show (∪ j : Fin (k + 1), chainIncrements S R j) =
      (∪ j ∈ Finset.Iic (k-1),
        chainIncrements S R ⟨j,by omega⟩) ∪
          chainIncrements S R ⟨k,by omega⟩ by
      ext x
      simp
      omega]
  rw [hprefix]
  simp [chainIncrements, last, Finset.union_sdiff_of_subset hlastSub]

theorem chain_increment_subset {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m)
    (i : Fin (k + 1)) :
    chainIncrements S R i ⊆ S := by
  by_cases hi0 : i.val = 0
  · subst i
    simpa [chainIncrements] using
      (chain_data_from_mem hR ⟨0,hk⟩).1
  by_cases hik : i.val = k
  · subst i
    intro x hx
    exact (Finset.mem_sdiff.mp
      (by simpa [chainIncrements] using hx)).1
  · have hi : i.val < k := by omega
    exact Finset.sdiff_subset.trans
      (chain_data_from_mem hR ⟨i.val,hi⟩).1

theorem chain_increment_disjoint_of_lt {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m)
    {i j : Fin (k + 1)} (hij : i.val < j.val) :
    Disjoint (chainIncrements S R i) (chainIncrements S R j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  by_cases hjk : j.val = k
  · subst j
    have hxiS := chain_increment_subset hk S hR i hxi
    have hxiLast :
        x ∈ R ⟨k-1,by omega⟩ := by
      have hprefix := chain_prefix_union_eq hk S hR ⟨k-1,by omega⟩
      rw [← hprefix]
      simp
      exact ⟨i.val,by omega,hxi⟩
    have hxnot :=
      (Finset.mem_sdiff.mp
        (by simpa [chainIncrements] using hxj)).2
    exact hxnot hxiLast
  · have hj : j.val < k := by omega
    have hxjnot :
        x ∉ R ⟨j.val-1,by omega⟩ := by
      by_cases hj0 : j.val = 0
      · omega
      · exact (Finset.mem_sdiff.mp
          (by simpa [chainIncrements,hj0,hjk] using hxj)).2
    have hxiPrev :
        x ∈ R ⟨j.val-1,by omega⟩ := by
      by_cases hi0 : i.val = 0
      · have hxRi : x ∈ R ⟨0,hk⟩ := by
          simpa [chainIncrements,hi0] using hxi
        exact chain_nested_from_mem hR _ _
          (by simp; omega) hxRi
      · by_cases hik : i.val = k
        · omega
        · have hi : i.val < k := by omega
          have hxRi : x ∈ R ⟨i.val,hi⟩ :=
            (Finset.mem_sdiff.mp
              (by simpa [chainIncrements,hi0,hik] using hxi)).1
          exact chain_nested_from_mem hR _ _
            (by simp; omega) hxRi
    exact hxjnot hxiPrev

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
    by_cases h : i.val < j.val
    · exact chain_increment_disjoint_of_lt hk S hR h
    · have h' : j.val < i.val := by omega
      exact (chain_increment_disjoint_of_lt hk S hR h').symm
  · intro x
    rw [← chain_all_increments_union_eq hk S hR]
    simp

def canonicalChain {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    Fin k → Finset (ZMod p) := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  exact fun i =>
    (finSegment S.card 0 (m i)
      (Nat.le_of_lt (hm.2 i).2)).image
      (fun j => (e j).1)

theorem canonicalChain_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    canonicalChain S m hm ∈ chainFamily S m := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j,hj,rfl⟩
      exact (e j).2
    · unfold canonicalChain
      rw [Finset.card_image_of_injOn]
      · exact card_finSegment S.card 0 (m i)
          (Nat.le_of_lt (hm.2 i).2) |>.trans (by omega)
      · intro a ha b hb hab
        exact e.injective (Subtype.ext hab)
  · intro i j hij x hx
    rcases Finset.mem_image.mp hx with ⟨r,hr,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨r, ?_, rfl⟩
    have hri := (mem_finSegment.mp hr)
    apply mem_finSegment.mpr
    refine ⟨by omega, ?_⟩
    exact lt_of_lt_of_le hri.2 (le_of_lt (hm.1 hij))

theorem chainFamily_nonempty {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    (chainFamily S m).Nonempty :=
  ⟨canonicalChain S m hm, canonicalChain_mem S m hm⟩

theorem chain_eq_of_increments_eq {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ}
    {R R' : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (hR' : R' ∈ chainFamily S m)
    (hEq : chainIncrements S R = chainIncrements S R') :
    R = R' := by
  funext i
  rw [← chain_prefix_union_eq hk S hR i,
      ← chain_prefix_union_eq hk S hR' i]
  simp [hEq]

theorem increments_prefix_union_eq {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (i : Fin k) :
    incrementsToChain Δ i =
      ∪ j ∈ Finset.Iic i.val, Δ ⟨j,by omega⟩ := rfl

theorem increments_chain_inverse {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    chainIncrements S (incrementsToChain Δ) = Δ := by
  classical
  rcases Finset.mem_filter.mp hΔ with ⟨_,hdata,hdisj,hcover⟩
  funext i
  by_cases hi0 : i.val = 0
  · subst i
    simp [chainIncrements,incrementsToChain]
  by_cases hik : i.val = k
  · subst i
    have hunion :
        (∪ j ∈ Finset.Iic (k-1), Δ ⟨j,by omega⟩) =
          S \ Δ ⟨k,by omega⟩ := by
      ext x
      simp
      constructor
      · rintro ⟨j,hj,hx⟩
        refine ⟨(hdata _).1 hx, ?_⟩
        intro hxk
        exact Finset.disjoint_left.mp
          (hdisj ⟨j,by omega⟩ ⟨k,by omega⟩ (by omega)) hx hxk
      · rintro ⟨hxS,hxk⟩
        rcases (hcover x).1 hxS with ⟨j,hxj⟩
        have hjne : j.val ≠ k := by
          intro h; subst j; exact hxk hxj
        exact ⟨j.val,by omega,hxj⟩
    simp [chainIncrements,incrementsToChain,hunion]
  · have hi : i.val < k := by omega
    have hprev :
        (∪ j ∈ Finset.Iic (i.val-1), Δ ⟨j,by omega⟩) ⊆
          (∪ j ∈ Finset.Iic i.val, Δ ⟨j,by omega⟩) := by
      intro x hx
      simp at hx ⊢
      rcases hx with ⟨j,hji,hxj⟩
      exact ⟨j,by omega,hxj⟩
    have hdiff :
        (∪ j ∈ Finset.Iic i.val, Δ ⟨j,by omega⟩) \
          (∪ j ∈ Finset.Iic (i.val-1), Δ ⟨j,by omega⟩) =
          Δ ⟨i.val,hi⟩ := by
      ext x
      simp
      constructor
      · rintro ⟨⟨j,hji,hxj⟩,hnot⟩
        have hjiEq : j = i.val := by
          by_contra hne
          have hjlt : j ≤ i.val - 1 := by omega
          exact hnot ⟨j,hjlt,hxj⟩
        subst j
        exact hxj
      · intro hxi
        refine ⟨⟨i.val,le_rfl,hxi⟩,?_⟩
        rintro ⟨j,hj,hxj⟩
        exact Finset.disjoint_left.mp
          (hdisj ⟨j,by omega⟩ ⟨i.val,hi⟩ (by omega))
          hxj hxi
    simp [chainIncrements,incrementsToChain,hi0,hik,hdiff]

theorem incrementPartitionFamily_nonempty {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ) (hm : IsChainSizeTuple S.card m) :
    (incrementPartitionFamily S m).Nonempty := by
  let R := canonicalChain S m hm
  exact ⟨chainIncrements S R,
    chainIncrements_mem hk S m (canonicalChain_mem S m hm)⟩

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
        card_biUnion_of_pairwise_disjoint
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
            m i := chainGap_prefix_sum m hm i
      simpa [incrementsToChain, (hdata _).2] using htel
  · intro i j hij
    intro x hx
    simp [incrementsToChain] at hx ⊢
    rcases hx with ⟨r,hri,hx⟩
    exact ⟨r, le_trans hri hij, hx⟩

theorem chain_increment_bijection {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ) (hm : IsChainSizeTuple S.card m) :
    (chainFamily S m).card = (incrementPartitionFamily S m).card := by
  classical
  apply Finset.card_bij
    (fun R _ => chainIncrements S R)
  · intro R hR
    exact chainIncrements_mem hk S m hR
  · intro R hR R' hR' hEq
    exact chain_eq_of_increments_eq hk S hR hR' hEq
  · intro Δ hΔ
    refine ⟨incrementsToChain Δ,
      incrementsToChain_mem hk S m hΔ, ?_⟩
    exact increments_chain_inverse hk S m hm hΔ

theorem subsetSum_union_of_disjoint {p : ℕ} [NeZero p]
    {A B : Finset (ZMod p)} (h : Disjoint A B) :
    subsetSum (A ∪ B) = subsetSum A + subsetSum B := by
  unfold subsetSum
  rw [Finset.sum_union h]

theorem subsetSum_biUnion_pairwise_disjoint
    {p ι : ℕ} [NeZero p]
    (I : Finset (Fin ι))
    (A : Fin ι → Finset (ZMod p))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
    subsetSum (∪ i ∈ I, A i) =
      ∑ i ∈ I, subsetSum (A i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [subsetSum]
  | @insert i I hi ih =>
      have hDI :
          Disjoint (A i) (∪ j ∈ I, A j) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i (by simp) j (by simp [hj])
          (by intro h; subst j; exact hi hj)
      rw [Finset.biUnion_insert, subsetSum_union_of_disjoint hDI,
        ih (by
          intro a ha b hb hab
          exact hdisj a (by simp [ha]) b (by simp [hb]) hab)]
      simp [hi]

theorem subsetSum_eq_sum_chain_increments {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (i : Fin k) :
    subsetSum (R i) =
      ∑ j ∈ Finset.Iic i.val,
        subsetSum (chainIncrements S R ⟨j,by omega⟩) := by
  rw [← chain_prefix_union_eq hk S hR i]
  apply subsetSum_biUnion_pairwise_disjoint
  intro a ha b hb hab
  by_cases hlt : a.val < b.val
  · exact chain_increment_disjoint_of_lt hk S hR hlt
  · exact (chain_increment_disjoint_of_lt hk S hR (by omega)).symm

def chainGapTarget {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : Fin k → ZMod p)
    (i : Fin (k + 1)) : ZMod p :=
  if h0 : i.val = 0 then z ⟨0,by omega⟩
  else if hk : i.val = k then subsetSum S - z ⟨k-1,by omega⟩
  else z ⟨i.val,by omega⟩ - z ⟨i.val-1,by omega⟩

theorem chainGapTarget_prefix_telescopes {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (z : Fin k → ZMod p) (i : Fin k) :
    ∑ j ∈ Finset.Iic i.val,
      chainGapTarget S z ⟨j,by omega⟩ = z i := by
  induction i.val with
  | zero =>
      simp [chainGapTarget,hk]
  | succ r ih =>
      rw [Finset.sum_Iic_succ_top]
      have hir : r < k := by omega
      have hir' : r + 1 < k := i.isLt
      have htarget :
          chainGapTarget S z ⟨r+1,by omega⟩ =
            z ⟨r+1,hir'⟩ - z ⟨r,hir⟩ := by
        simp [chainGapTarget]
        omega
      rw [htarget]
      have ih' := ih ⟨r,hir⟩
      simpa using add_sub_cancel_left _ _

theorem chain_sum_event_iff_increment_targets {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} (R : Fin k → Finset (ZMod p))
    (hR : R ∈ chainFamily S m)
    (z : Fin k → ZMod p) :
    (∀ i, subsetSum (R i) = z i) ↔
      ∀ i : Fin (k + 1),
        subsetSum (chainIncrements S R i) = chainGapTarget S z i := by
  constructor
  · intro hz i
    by_cases h0 : i.val = 0
    · subst i
      simpa [chainIncrements,chainGapTarget] using hz ⟨0,hk⟩
    by_cases hlast : i.val = k
    · subst i
      have hlastSub :=
        (chain_data_from_mem hR ⟨k-1,by omega⟩).1
      rw [subsetSum_sdiff hlastSub]
      simp [chainIncrements,chainGapTarget,hk,hz]
    · have hi : i.val < k := by omega
      have hsub :=
        chain_nested_from_mem hR
          ⟨i.val-1,by omega⟩ ⟨i.val,hi⟩ (by simp; omega)
      rw [show chainIncrements S R i =
          R ⟨i.val,hi⟩ \ R ⟨i.val-1,by omega⟩ by
            simp [chainIncrements,h0,hlast]]
      rw [subsetSum_sdiff hsub]
      simp [chainGapTarget,h0,hlast,hz]
  · intro hΔ i
    rw [subsetSum_eq_sum_chain_increments hk S hR i]
    simp_rw [hΔ]
    exact chainGapTarget_prefix_telescopes hk S z i

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

def historyKey {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → Option (Finset (ZMod p)) :=
  fun i => if i ∈ L then some (Δ i) else none

def exposedUnion {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Finset (ZMod p) :=
  ∪ i ∈ L, Δ i

def remainingAfter {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Finset (ZMod p) :=
  S \ exposedUnion L Δ

theorem unexposed_component_subset_remaining {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1))) {i : Fin (k + 1)}
    (hi : i ∉ L) :
    Δ i ⊆ remainingAfter S L Δ := by
  rcases Finset.mem_filter.mp hΔ with ⟨_,hdata,hdisj,_⟩
  intro x hxi
  apply Finset.mem_sdiff.mpr
  refine ⟨(hdata i).1 hxi,?_⟩
  intro hxU
  simp [exposedUnion] at hxU
  rcases hxU with ⟨j,hjL,hxj⟩
  exact Finset.disjoint_left.mp (hdisj i j (by
    intro h; subst j; exact hi hjL)) hxi hxj

theorem unexposed_component_card_le_remaining {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1))) {i : Fin (k + 1)}
    (hi : i ∉ L) :
    chainGap S.card m i ≤ (remainingAfter S L Δ).card := by
  have hsub := unexposed_component_subset_remaining S m hΔ L hi
  have hcard := Finset.card_le_card hsub
  rw [(Finset.mem_filter.mp hΔ).2.1 i |>.2] at hcard
  exact hcard

def partitionPermMap {p k : ℕ} [NeZero p]
    (π : Equiv.Perm (ZMod p))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → Finset (ZMod p) :=
  fun i => (Δ i).image π

theorem partitionPermMap_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    partitionPermMap π Δ ∈ incrementPartitionFamily S m := by
  classical
  rcases Finset.mem_filter.mp hΔ with ⟨_,hdata,hdisj,hcover⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro i
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
      rw [← hπS]
      exact Finset.mem_image.mpr ⟨y,(hdata i).1 hy,rfl⟩
    · rw [Finset.card_image_of_injective _ π.injective,
        (hdata i).2]
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_image.mp hxi with ⟨a,hai,ha⟩
    rcases Finset.mem_image.mp hxj with ⟨b,hbj,hb⟩
    have hab : a = b := π.injective (ha.trans hb.symm)
    subst b
    exact Finset.disjoint_left.mp (hdisj i j hij) hai hbj
  · intro x
    constructor
    · intro hxS
      rw [← hπS] at hxS
      rcases Finset.mem_image.mp hxS with ⟨y,hyS,rfl⟩
      rcases (hcover y).1 hyS with ⟨i,hyi⟩
      exact ⟨i,Finset.mem_image.mpr ⟨y,hyi,rfl⟩⟩
    · rintro ⟨i,hxi⟩
      exact (show x ∈ S from (by
        rcases Finset.mem_image.mp hxi with ⟨y,hyi,rfl⟩
        rw [← hπS]
        exact Finset.mem_image.mpr ⟨y,(hdata i).1 hyi,rfl⟩))

theorem partitionPermMap_history_fixed {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (π : Equiv.Perm (ZMod p))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hfix : ∀ x ∈ exposedUnion L Δ, π x = x) :
    historyKey L (partitionPermMap π Δ) = historyKey L Δ := by
  funext i
  by_cases hi : i ∈ L
  · simp [historyKey,hi,partitionPermMap]
    apply Finset.image_eq_self.mpr
    intro x hx
    exact hfix x (by
      simp [exposedUnion]
      exact ⟨i,hi,hx⟩)
  · simp [historyKey,hi]

theorem remaining_invariant_under_history
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ) :
    remainingAfter S L Δ = remainingAfter S L Γ := by
  unfold remainingAfter exposedUnion
  congr 1
  apply Finset.biUnion_congr rfl
  intro i hi
  have := congrFun hkey i
  simp [historyKey,hi] at this
  exact this

theorem history_component_eq {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ)
    {i : Fin (k + 1)} (hi : i ∈ L) :
    Δ i = Γ i := by
  have h := congrFun hkey i
  simp [historyKey,hi] at h
  exact h

theorem exposedUnion_eq_of_history {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ) :
    exposedUnion L Δ = exposedUnion L Γ := by
  unfold exposedUnion
  apply Finset.biUnion_congr rfl
  intro i hi
  exact history_component_eq L hkey hi

theorem exposed_subset_S {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1))) :
    exposedUnion L Δ ⊆ S := by
  intro x hx
  simp [exposedUnion] at hx
  rcases hx with ⟨i,hiL,hxi⟩
  exact ((Finset.mem_filter.mp hΔ).2.1 i).1 hxi

theorem exposed_not_remaining {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1)))
    {x : ZMod p} (hx : x ∈ exposedUnion L Δ) :
    x ∉ remainingAfter S L Δ := by
  intro hxrem
  exact (Finset.mem_sdiff.mp hxrem).2 hx

theorem perm_fix_exposed_of_fix_outside_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1)))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∉ remainingAfter S L Δ, π x = x) :
    ∀ x ∈ exposedUnion L Δ, π x = x := by
  intro x hx
  exact hfix x (exposed_not_remaining S m hΔ L hx)

theorem perm_fix_outside_S_of_fix_outside_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1)))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∉ remainingAfter S L Δ, π x = x) :
    ∀ x ∉ S, π x = x := by
  intro x hxS
  apply hfix
  intro hxU
  exact hxS (Finset.mem_sdiff.mp hxU).1

theorem component_fiber_equipotent
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1))) (i : Fin (k + 1))
    (hi : i ∉ L)
    (H : Fin (k + 1) → Option (Finset (ZMod p)))
    (Δ₀ : Fin (k + 1) → Finset (ZMod p))
    (hΔ₀ : Δ₀ ∈ incrementPartitionFamily S m)
    (hH : historyKey L Δ₀ = H)
    (A B : Finset (ZMod p))
    (hA : A ∈ (remainingAfter S L Δ₀).powersetCard
      (chainGap S.card m i))
    (hB : B ∈ (remainingAfter S L Δ₀).powersetCard
      (chainGap S.card m i)) :
    ((incrementPartitionFamily S m).filter fun Δ =>
      historyKey L Δ = H ∧ Δ i = A).card =
    ((incrementPartitionFamily S m).filter fun Δ =>
      historyKey L Δ = H ∧ Δ i = B).card := by
  classical
  let U := remainingAfter S L Δ₀
  obtain ⟨π,hπA,hπU,hπfix⟩ :=
    exists_perm_maps_finset U A B
      (Finset.mem_powersetCard.mp hA).1
      (Finset.mem_powersetCard.mp hB).1
      (by simpa using congrArg (fun T => T.card)
        (show A.card = B.card by
          rw [(Finset.mem_powersetCard.mp hA).2,
              (Finset.mem_powersetCard.mp hB).2]))
  have hπS : S.image π = S := by
    ext x
    by_cases hxU : x ∈ U
    · rw [← hπU]
      exact Finset.mem_image.mpr ⟨x,hxU,rfl⟩
    · have hxfix : π x = x := by
        by_cases hxS : x ∈ S
        · have hxExp : x ∈ exposedUnion L Δ₀ := by
            have : x ∉ S \ exposedUnion L Δ₀ := by
              simpa [U] using hxU
            exact by
              simp at this
              exact this hxS
          exact perm_fix_exposed_of_fix_outside_remaining
            S m L hΔ₀ π (by simpa [U] using hπfix) x hxExp
        · exact hπfix x (by
            intro hx; exact hxS
              (Finset.mem_sdiff.mp hx).1)
      simp [hxfix]
  apply Finset.card_bij
    (fun Δ _ => partitionPermMap π Δ)
  · intro Δ hΔ
    rcases Finset.mem_filter.mp hΔ with
      ⟨hmem,hkey,hAi⟩
    apply Finset.mem_filter.mpr
    refine ⟨partitionPermMap_mem S m π hπS hmem, ?_, ?_⟩
    · rw [partitionPermMap_history_fixed L π
        (fun x hx => perm_fix_exposed_of_fix_outside_remaining
          S m L hΔ₀ π (by simpa [U] using hπfix) x
          (by
            rw [exposedUnion_eq_of_history L (hkey.trans hH.symm)]
            exact hx))]
      exact hkey
    · simp [partitionPermMap,hAi,hπA]
  · intro Δ hΔ Γ hΓ hEq
    funext r
    apply π.injective
    exact finset_image_injective_of_injective π.injective
      (congrFun hEq r)
  · intro Γ hΓ
    let Δ := partitionPermMap π.symm Γ
    refine ⟨Δ, ?_, ?_⟩
    · rcases Finset.mem_filter.mp hΓ with
        ⟨hmem,hkey,hBi⟩
      apply Finset.mem_filter.mpr
      refine ⟨partitionPermMap_mem S m π.symm
          (by simpa using congrArg (Finset.image π.symm) hπS) hmem,
        ?_, ?_⟩
      · exact partitionPermMap_history_fixed L π.symm
          ((by
            intro x hx
            have hx0 : x ∈ exposedUnion L Δ₀ := by
              rw [← exposedUnion_eq_of_history L (hkey.trans hH.symm)]
              exact hx
            have hfx :=
              perm_fix_exposed_of_fix_outside_remaining
                S m L hΔ₀ π (by simpa [U] using hπfix) x hx0
            exact perm_symm_fixes_of_fixes π hfx))
          |>.trans hkey
      · simp [Δ,partitionPermMap,hBi,hπA]
    · funext r
      simp [Δ,partitionPermMap]

theorem increment_conditional_uniform_given_history
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (L : Finset (Fin (k + 1))) (i : Fin (k + 1))
    (hi : i ∉ L)
    (H : Fin (k + 1) → Option (Finset (ZMod p)))
    (Δ₀ : Fin (k + 1) → Finset (ZMod p))
    (hΔ₀ : Δ₀ ∈ incrementPartitionFamily S m)
    (hH : historyKey L Δ₀ = H)
    (q : ZMod p) :
    uniformConditionalMass (incrementPartitionFamily S m)
      (fun Δ => historyKey L Δ = H)
      (fun Δ => subsetSum (Δ i) = q) =
    sliceMass (remainingAfter S L Δ₀)
      (chainGap S.card m i) q := by
  classical
  let U := remainingAfter S L Δ₀
  let ΩH := (incrementPartitionFamily S m).filter
    (fun Δ => historyKey L Δ = H)
  let choices := U.powersetCard (chainGap S.card m i)
  have hmap : ∀ Δ ∈ ΩH, Δ i ∈ choices := by
    intro Δ hΔ
    rcases Finset.mem_filter.mp hΔ with ⟨hmem,hkey⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · have hrem :=
        remaining_invariant_under_history S L
          (hkey.trans hH.symm)
      rw [hrem]
      exact unexposed_component_subset_remaining S m hΔ₀ L hi
    · exact (Finset.mem_filter.mp hmem).2.1 i |>.2
  have hchoices : choices.Nonempty :=
    powersetCard_nonempty U
      (unexposed_component_card_le_remaining S m hΔ₀ L hi)
  have hΩH : ΩH.Nonempty := by
    refine ⟨Δ₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨hΔ₀,hH⟩
  have heq' :
      ∀ A ∈ choices, ∀ B ∈ choices,
        (ΩH.filter fun Δ => Δ i = A).card =
          (ΩH.filter fun Δ => Δ i = B).card := by
    intro A hA B hB
    exact component_fiber_equipotent S m L i hi H
      Δ₀ hΔ₀ hH A B hA hB
  simpa [ΩH,choices,U,uniformConditionalMass,sliceMass] using
    (uniformMass_statistic_of_pairwise_equal_fibers
      ΩH choices (fun Δ => Δ i) hmap hchoices hΩH heq'
      (fun A => subsetSum A = q))

def historySatisfies {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (target : Fin (k + 1) → ZMod p)
    (H : Fin (k + 1) → Option (Finset (ZMod p))) : Prop :=
  ∀ i ∈ L, ∃ A, H i = some A ∧ subsetSum A = target i

theorem historySatisfies_key_iff {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (target : Fin (k + 1) → ZMod p)
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    historySatisfies L target (historyKey L Δ) ↔
      ∀ i ∈ L, subsetSum (Δ i) = target i := by
  constructor
  · intro h i hi
    rcases h i hi with ⟨A,hA,hSum⟩
    simp [historyKey,hi] at hA
    simpa [hA] using hSum
  · intro h i hi
    exact ⟨Δ i, by simp [historyKey,hi], h i hi⟩

theorem two_unexposed_gaps_sum_le_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1)))
    {i j : Fin (k + 1)} (hi : i ∉ L) (hj : j ∉ L)
    (hij : i ≠ j) :
    chainGap S.card m i + chainGap S.card m j ≤
      (remainingAfter S L Δ).card := by
  have hiSub := unexposed_component_subset_remaining S m hΔ L hi
  have hjSub := unexposed_component_subset_remaining S m hΔ L hj
  have hdisj := (Finset.mem_filter.mp hΔ).2.2.1 i j hij
  have hunion :
      Δ i ∪ Δ j ⊆ remainingAfter S L Δ :=
    Finset.union_subset hiSub hjSub
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj,
      ((Finset.mem_filter.mp hΔ).2.1 i).2,
      ((Finset.mem_filter.mp hΔ).2.1 j).2] at hcard
  exact hcard

theorem remainingAfter_subset {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    remainingAfter S L Δ ⊆ S :=
  Finset.sdiff_subset

theorem increment_event_list_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (j : Fin (k + 1))
    (target : Fin (k + 1) → ZMod p)
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (L : List (Fin (k + 1))) (hLnodup : L.Nodup)
    (hjL : j ∉ L) :
    uniformMass (incrementPartitionFamily S m)
      (fun Δ => ∀ i ∈ L, subsetSum (Δ i) = target i) ≤
        (L.map b).prod := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
      simpa using uniformMass_le_one
        (incrementPartitionFamily S m)
        (fun _ => True)
  | append_singleton L i ih =>
      have hiL : i ∉ L := by
        simpa using (List.nodup_append.mp hLnodup).2.1
      have hjL' : j ∉ L := by
        intro hj
        exact hjL (by simp [hj])
      have hij : i ≠ j := by
        intro h
        subst i
        exact hjL (by simp)
      let Prev : (Fin (k + 1) → Finset (ZMod p)) → Prop :=
        fun Δ => ∀ r ∈ L, subsetSum (Δ r) = target r
      let Cur : (Fin (k + 1) → Finset (ZMod p)) → Prop :=
        fun Δ => subsetSum (Δ i) = target i
      have hchain :
          uniformMass (incrementPartitionFamily S m)
              (fun Δ => Prev Δ ∧ Cur Δ) =
            uniformMass (incrementPartitionFamily S m) Prev *
              uniformConditionalMass (incrementPartitionFamily S m)
                Prev Cur :=
        uniformMass_chain_rule _ Prev Cur
      have hcond :
          uniformConditionalMass (incrementPartitionFamily S m)
            Prev Cur ≤ b i := by
        let LF : Finset (Fin (k + 1)) := L.toFinset
        let key := historyKey LF
        let P : (Fin (k + 1) → Option (Finset (ZMod p))) → Prop :=
          historySatisfies LF target
        have hPrev :
            Prev = fun Δ => P (key Δ) := by
          funext Δ
          apply propext
          simpa [Prev,P,key,LF,List.mem_toFinset] using
            (historySatisfies_key_iff LF target Δ).symm
        rw [hPrev]
        apply uniformConditionalMass_le_of_fibers
          (incrementPartitionFamily S m) key P Cur
          (b i) (hb i)
        intro H hPH
        by_cases hfiber :
            ((incrementPartitionFamily S m).filter
              fun Δ => key Δ = H).Nonempty
        · obtain ⟨Δ₀,hΔ₀fiber⟩ := hfiber
          rcases Finset.mem_filter.mp hΔ₀fiber with ⟨hΔ₀,hkey⟩
          have hiLF : i ∉ LF := by
            simpa [LF,List.mem_toFinset] using hiL
          have hjLF : j ∉ LF := by
            simpa [LF,List.mem_toFinset] using hjL'
          let U := remainingAfter S LF Δ₀
          have htwo :
              chainGap S.card m i + chainGap S.card m j ≤ U.card :=
            two_unexposed_gaps_sum_le_remaining
              S m hΔ₀ LF hiLF hjLF hij
          have huniform :=
            increment_conditional_uniform_given_history
              S m hm LF i hiLF H Δ₀ hΔ₀ hkey (target i)
          rw [huniform]
          exact hstep i hij U (remainingAfter_subset S LF Δ₀)
            htwo (target i)
        · unfold uniformConditionalMass
          have hempty :
              (incrementPartitionFamily S m).filter
                (fun Δ => key Δ = H) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hfiber
          simp [hempty]
      rw [show (fun Δ => ∀ r ∈ L ++ [i],
          subsetSum (Δ r) = target r) =
          (fun Δ => Prev Δ ∧ Cur Δ) by
            funext Δ
            apply propext
            simp [Prev,Cur]]
      rw [hchain]
      have hLnodup' : L.Nodup :=
        (List.nodup_append.mp hLnodup).1
      have hprev := ih hLnodup' hjL'
      have hnonneg : 0 ≤ uniformConditionalMass
          (incrementPartitionFamily S m) Prev Cur :=
        uniformMass_nonneg _ _
      calc
        uniformMass (incrementPartitionFamily S m) Prev *
            uniformConditionalMass (incrementPartitionFamily S m) Prev Cur
          ≤ (L.map b).prod * b i :=
            mul_le_mul hprev hcond hnonneg (by positivity)
        _ = ((L ++ [i]).map b).prod := by simp

/-- Sequential exposure of all increments except j. -/
theorem incrementPartition_product_bound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (j : Fin (k + 1))
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (target : Fin (k + 1) → ZMod p) :
    uniformMass (incrementPartitionFamily S m)
      (fun Δ => ∀ i, i ≠ j → subsetSum (Δ i) = target i) ≤
        ∏ i ∈ Finset.univ.erase j, b i := by
  classical
  let L := exposureOrder j
  have hlist :=
    increment_event_list_bound S m hm j target b hb hstep
      L (exposureOrder_nodup j)
      (by
        intro hj
        exact (mem_exposureOrder_iff j j).mp hj rfl)
  have hevent :
      (fun Δ => ∀ i, i ≠ j → subsetSum (Δ i) = target i) =
        (fun Δ => ∀ i ∈ L, subsetSum (Δ i) = target i) := by
    funext Δ
    apply propext
    constructor
    · intro h i hi
      exact h i ((mem_exposureOrder_iff j i).mp hi)
    · intro h i hij
      exact h i ((mem_exposureOrder_iff j i).mpr hij)
  rw [hevent]
  calc
    uniformMass (incrementPartitionFamily S m)
        (fun Δ => ∀ i ∈ L, subsetSum (Δ i) = target i)
      ≤ (L.map b).prod := hlist
    _ = ∏ i ∈ Finset.univ.erase j, b i := by
      rw [list_prod_eq_finset_prod_of_nodup
        L (exposureOrder_nodup j) b]
      congr 1
      ext i
      simp [L,mem_exposureOrder_iff]

theorem chainMass_fixed_gap_product_bound {p k : ℕ} [NeZero p]
    (hk : 0 < k)
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (j : Fin (k + 1))
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
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
    apply uniformMass_bij
      (chainFamily S m) (incrementPartitionFamily S m)
      (fun R => chainIncrements S R)
    · intro R hR
      exact chainIncrements_mem hk S m hR
    · intro R hR R' hR' hEq
      exact chain_eq_of_increments_eq hk S hR hR' hEq
    · intro Δ hΔ
      exact ⟨incrementsToChain Δ,
        incrementsToChain_mem hk S m hΔ,
        increments_chain_inverse hk S m hm hΔ⟩
    · intro R hR
      exact chain_sum_event_iff_increment_targets hk S R hR z
  rw [hmass]
  have hmono :
      uniformMass (incrementPartitionFamily S m)
          (fun Δ => ∀ i, subsetSum (Δ i) = chainGapTarget S z i) ≤
        uniformMass (incrementPartitionFamily S m)
          (fun Δ => ∀ i, i ≠ j →
            subsetSum (Δ i) = chainGapTarget S z i) := by
    apply uniformMass_mono_on
    intro Δ hΔ hall i hij
    exact hall i
  exact le_trans hmono
    (incrementPartition_product_bound S m hm j b hb hstep
      (chainGapTarget S z))

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
      (fun i => chainFactor_nonneg Ck (le_of_lt hCk))
    intro i hij T hTS hsum q
    have hgap : 0 < chainGap S.card m i :=
      chainGap_pos hk m hm i
    have hgapjT :
        chainGap S.card m j ≤ T.card :=
      le_trans (Nat.le_add_left _ _) hsum
    have hTlower : ε * S.card ≤ (T.card : ℝ) := by
      exact_mod_cast le_trans (by exact_mod_cast hgapRemain) hgapjT
    have hTle : T.card ≤ S.card := Finset.card_le_card hTS
    have hgapjFrac :
        ε * (T.card : ℝ) ≤ chainGap S.card m j := by
      have hεnonneg : 0 ≤ ε := le_of_lt hε0
      have hscaled :
          ε * (T.card : ℝ) ≤ ε * S.card :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hTle) hεnonneg
      exact le_trans hscaled hgapRemain
    have hsumR :
        (chainGap S.card m i : ℝ) +
          chainGap S.card m j ≤ T.card := by exact_mod_cast hsum
    have hfrac :
        (chainGap S.card m i : ℝ) ≤ (1 - ε) * T.card := by
      nlinarith [hgapjFrac,hsumR]
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
      hcorT T hTS hTlower
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
