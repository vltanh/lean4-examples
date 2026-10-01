import Lean4Examples.GrahamRearrangement.Combinatorial.External

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 4.1
-/

noncomputable section

theorem one_point_sum_event_card_le_one {p : ℕ} [NeZero p]
    (R U : Finset (ZMod p)) (hdisj : Disjoint R U)
    (z : ZMod p) :
    (U.filter fun x => subsetSum (insert x R) = z).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxU := (Finset.mem_filter.1 hx).1
  have hyU := (Finset.mem_filter.1 hy).1
  have hxR : x ∉ R := by
    exact Finset.disjoint_left.1 hdisj (by
      exact (Finset.mem_filter.1 hx).1) hxU
  have hyR : y ∉ R := by
    exact Finset.disjoint_left.1 hdisj (by
      exact (Finset.mem_filter.1 hy).1) hyU
  have hxsum := (Finset.mem_filter.1 hx).2
  have hysum := (Finset.mem_filter.1 hy).2
  rw [subsetSum_insert R x hxR, subsetSum_insert R y hyR] at hxsum hysum
  exact add_right_cancel (hxsum.trans hysum.symm)

theorem one_point_sum_mass_le {p : ℕ} [NeZero p]
    (R U : Finset (ZMod p)) (hU : U.Nonempty)
    (hdisj : Disjoint R U) (z : ZMod p) :
    uniformMass U (fun x => subsetSum (insert x R) = z) ≤
      1 / (U.card : ℝ) := by
  unfold uniformMass
  have hcard := one_point_sum_event_card_le_one R U hdisj z
  have hUpos : (0 : ℝ) < U.card := by
    exact_mod_cast hU.card_pos
  apply (div_le_div_iff_of_pos_right hUpos).2
  exact_mod_cast hcard

/-- Lemma 4.1. -/
theorem lemma4_1 {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤ 1 / ((S.card - m + 1 : ℕ) : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [sliceMass, Section4External.uniformSubset_twoStage S m hm hmS]
  have hspace :
      (S.powersetCard (m - 1)).Nonempty := by
    apply Section4External.powersetCard_nonempty
    omega
  apply Section4External.uniformExpectation_le_const _ hspace
  intro R hR
  have hRsub : R ⊆ S := by
    exact (Finset.mem_powersetCard.1 hR).1
  have hdisj : Disjoint R (S \ R) := by
    exact Finset.disjoint_sdiff_right
  have hcard :
      (S \ R).card = S.card - m + 1 := by
    have hRm1 : R.card = m - 1 :=
      Section4External.mem_powersetCard_card hR
    rw [Finset.card_sdiff hRsub, hRm1]
    omega
  have hnonempty : (S \ R).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hbound :=
    one_point_sum_mass_le R (S \ R) hnonempty hdisj z
  simpa [hcard] using hbound

/-- The max_z formulation stated in the paper. -/
theorem lemma4_1_max {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z : ZMod p,
      sliceMass S m z ≤ 1 / ((S.card - m + 1 : ℕ) : ℝ) := by
  intro z
  exact lemma4_1 hp S hm hmS z

end

end GrahamRearrangement
