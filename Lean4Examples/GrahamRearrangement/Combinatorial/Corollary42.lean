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
  have hprod :
      chainMass S m z ≤
        ∏ i ∈ Finset.univ.erase j,
          chainFactor p S.card Ck (chainGap S.card m i) := by
    apply Section4External.uniformChain_sumProductBound
      S m hm j ε hε0
      (fun i => chainFactor p S.card Ck (chainGap S.card m i))
    intro i hij T hTS hTlower hgapfrac q
    have hgap : 0 < chainGap S.card m i :=
      chainGap_pos hk m hm i
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
      hcorT T hTS hTlower (chainGap S.card m i) hgap hgapfrac q
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

end

end GrahamRearrangement
