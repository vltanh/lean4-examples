import Lean4Examples.GrahamRearrangement.BooleanSlice.External

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: Fourier reduction

Paper equations (3.1)--(3.4).
-/

noncomputable section

/-- The blockwise character estimate used in equation (3.2), proved from
Fact 2.5 exactly as in the paper. -/
theorem block_character_decay {p : ℕ} (hp : p.Prime)
    (T : Finset (ZMod p)) (hT : T.Nonempty) (χ : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ≤
      Real.exp (-
        (1 / (T.card : ℝ) ^ 2) *
          ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let δ : ℝ :=
    (1 / (T.card : ℝ) ^ 2) *
      ∑ x ∈ T, ∑ x' ∈ T,
        zmodNorm (χ * x - χ * x') ^ 2
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hsq :=
    External.zmod_character_average_norm_sq T hT χ
  have hdouble :
      (∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re)
        ≤ (T.card : ℝ) ^ 2 -
          2 * ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2 := by
    calc
      _ ≤ ∑ x ∈ T, ∑ x' ∈ T,
          (1 - 2 * zmodNorm (χ * x - χ * x') ^ 2) := by
            gcongr with x hx x' hx'
            simpa [ep_eq_stdAddChar] using
              fact2_5 hp (χ * x - χ * x')
      _ = (T.card : ℝ) ^ 2 -
          2 * ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2 := by
            simp [pow_two]
            ring
  have hcard : 0 < (T.card : ℝ) := by
    exact_mod_cast hT.card_pos
  have hnormsq :
      ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2
        ≤ 1 - 2 * δ := by
    rw [hsq]
    dsimp [δ]
    have hcoef : 0 ≤ 1 / (T.card : ℝ) ^ 2 := by positivity
    calc
      _ ≤ (1 / (T.card : ℝ) ^ 2) *
          ((T.card : ℝ) ^ 2 -
            2 * ∑ x ∈ T, ∑ x' ∈ T,
              zmodNorm (χ * x - χ * x') ^ 2) := by
            exact mul_le_mul_of_nonneg_left hdouble hcoef
      _ = _ := by field_simp; ring
  have hexp :
      1 - 2 * δ ≤ Real.exp (-2 * δ) := by
    simpa only [neg_mul] using Real.one_sub_le_exp_neg (2 * δ)
  have hsquare :
      (Real.exp (-δ)) ^ 2 = Real.exp (-2 * δ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq' :
      ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2
        ≤ (Real.exp (-δ)) ^ 2 := by
    rw [hsquare]
    exact le_trans hnormsq hexp
  have hnorm0 :
      0 ≤ ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ :=
    norm_nonneg _
  have hexp0 : 0 ≤ Real.exp (-δ) := Real.exp_nonneg _
  nlinarith

theorem zmod_eq_indicator_fourier {p : ℕ} (hp : p.Prime)
    (a : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (((if a = 0 then 1 else 0 : ℝ) : ℂ)) =
      (1 / (p : ℂ)) *
        ∑ χ : ZMod p, ZMod.stdAddChar (χ * a) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [External.zmod_character_orthogonality hp a]
  by_cases ha : a = 0
  · simp [ha, hp.ne_zero]
  · simp [ha]

theorem character_choiceSum_factorization {p m : ℕ}
    [NeZero p]
    (P : Fin m → Finset (ZMod p)) (χ : ZMod p) :
    (∑ X ∈ blockChoices P,
        ZMod.stdAddChar (χ * choiceSum X)) =
      ∏ i : Fin m,
        ∑ x ∈ P i, ZMod.stdAddChar (χ * x) := by
  classical
  unfold blockChoices choiceSum
  rw [Finset.sum_pi]
  simp_rw [Finset.mul_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rfl

theorem conditional_sum_mass_fourier_eq {p m : ℕ}
    (hp : p.Prime)
    (P : Fin m → Finset (ZMod p))
    (hne : ∀ i, (P i).Nonempty) (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (conditionalSumMass P z : ℂ) =
      (1 / (p : ℂ)) *
        ∑ χ : ZMod p,
          ZMod.stdAddChar (-χ * z) *
            ∏ i : Fin m,
              ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                ((P i).card : ℂ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hcardP :
      (blockChoices P).card = ∏ i : Fin m, (P i).card :=
    blockChoices_card P
  have hcardpos :
      (0 : ℝ) < (blockChoices P).card := by
    rw [hcardP]
    exact_mod_cast Finset.prod_pos (fun i hi => (hne i).card_pos)
  unfold conditionalSumMass uniformMass
  have hindicator :
      (((((blockChoices P).filter fun X => choiceSum X = z).card : ℝ)) : ℂ) =
        ∑ X ∈ blockChoices P,
          (((if choiceSum X - z = 0 then 1 else 0 : ℝ) : ℂ)) := by
    norm_cast
    simp [Finset.sum_boole, sub_eq_zero]
  rw [hindicator]
  simp_rw [zmod_eq_indicator_fourier hp]
  rw [Finset.sum_mul, Finset.sum_comm]
  have hfactor :
      ∀ χ : ZMod p,
        (∑ X ∈ blockChoices P,
            ZMod.stdAddChar (χ * (choiceSum X - z))) =
          ZMod.stdAddChar (-χ * z) *
            ∏ i : Fin m,
              ∑ x ∈ P i, ZMod.stdAddChar (χ * x) := by
    intro χ
    calc
      _ = ∑ X ∈ blockChoices P,
          (ZMod.stdAddChar (χ * choiceSum X) *
            ZMod.stdAddChar (-χ * z)) := by
            apply Finset.sum_congr rfl
            intro X hX
            simp [mul_sub, map_add, sub_eq_add_neg,
              mul_add, add_comm, add_left_comm, add_assoc]
      _ = ZMod.stdAddChar (-χ * z) *
          ∑ X ∈ blockChoices P,
            ZMod.stdAddChar (χ * choiceSum X) := by
            rw [Finset.mul_sum]
            ring
      _ = _ := by rw [character_choiceSum_factorization P χ]
  simp_rw [hfactor]
  rw [hcardP]
  have hprodCard :
      (((∏ i : Fin m, (P i).card : ℕ) : ℝ) : ℂ) =
        ∏ i : Fin m, ((P i).card : ℂ) := by
    norm_cast
    simp
  rw [hprodCard]
  field_simp
  ring_nf
  simp_rw [Finset.prod_div_distrib]
  ring

theorem conditional_sum_mass_fourier_bound {p m : ℕ}
    (hp : p.Prime)
    (P : Fin m → Finset (ZMod p))
    (hne : ∀ i, (P i).Nonempty) (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ∏ i,
            ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
              ((P i).card : ℂ))‖ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have heq := conditional_sum_mass_fourier_eq hp P hne z
  have hnonneg : 0 ≤ conditionalSumMass P z :=
    uniformMass_nonneg _ _
  have hnorm :
      conditionalSumMass P z ≤
        ‖((conditionalSumMass P z : ℝ) : ℂ)‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [heq] at hnorm
  calc
    conditionalSumMass P z
      ≤ ‖(1 / (p : ℂ)) *
          ∑ χ : ZMod p,
            ZMod.stdAddChar (-χ * z) *
              ∏ i : Fin m,
                ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := hnorm
    _ = (1 / (p : ℝ)) *
        ‖∑ χ : ZMod p,
            ZMod.stdAddChar (-χ * z) *
              ∏ i : Fin m,
                ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := by
          rw [norm_mul]
          simp [hp.pos.ne']
    _ ≤ (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ‖ZMod.stdAddChar (-χ * z) *
              ∏ i : Fin m,
                ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := by
          gcongr
          exact norm_sum_le _ _
    _ = (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ∏ i,
            ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
              ((P i).card : ℂ))‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [norm_mul, norm_prod]
          simp

/-- Equation (3.1), followed by the blockwise decay that gives (3.2). -/
theorem conditional_sum_mass_le_exp_psi {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) * ∑ χ : ZMod p, Real.exp (-psi P χ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hne : ∀ i, (P i).Nonempty := by
    intro i
    have hb := Section3External.balanced_block_size_bounds S hm hmS hP i
    have hdiv : 0 < S.card / m := Nat.div_pos (Nat.le_of_lt hm) hmS
    exact Finset.card_pos.mp (lt_of_lt_of_le hdiv hb.1)
  have h31 := conditional_sum_mass_fourier_bound hp P hne z
  calc
    conditionalSumMass P z
        ≤ (1 / (p : ℝ)) *
            ∑ χ : ZMod p,
              ∏ i,
                ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := by
            exact h31
    _ ≤ (1 / (p : ℝ)) * ∑ χ : ZMod p, Real.exp (-psi P χ) := by
      gcongr with χ
      calc
        ∏ i,
            ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
              ((P i).card : ℂ))‖
            ≤ ∏ i,
                Real.exp (-
                  (1 / ((P i).card : ℝ) ^ 2) *
                    ∑ x ∈ P i, ∑ x' ∈ P i,
                      zmodNorm (χ * x - χ * x') ^ 2) := by
              apply Finset.prod_le_prod
              · intro i hi
                positivity
              · intro i hi
                exact block_character_decay hp (P i) (hne i) χ
        _ = Real.exp (-psi P χ) := by
              rw [← Real.exp_sum]
              congr 1
              simp [psi, Finset.sum_neg_distrib, mul_assoc]

/-- Equation (3.3), obtained from the balanced block-size upper bound. -/
theorem psi_lower_bound {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) :
    ((m : ℝ) ^ 2 / (2 * (S.card : ℝ) ^ 2)) *
        ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
          zmodNorm (χ * x - χ * x') ^ 2
      ≤ psi P χ := by
  unfold psi
  apply Finset.sum_le_sum
  intro i hi
  have hcard :=
    Section3External.balanced_block_sqrt_two_bound S hS hm4 hP i
  have hcardpos : 0 < ((P i).card : ℝ) := by
    have hbounds :=
      Section3External.balanced_block_size_bounds S hm
        (le_trans hm4 (Nat.div_le_self _ _)) hP i
    have hdiv : 0 < S.card / m := by
      exact Nat.div_pos (Nat.le_of_lt hm) (le_trans hm4 (Nat.div_le_self _ _))
    exact_mod_cast lt_of_lt_of_le hdiv hbounds.1
  have hSpos : 0 < (S.card : ℝ) := by positivity
  have hmpos : 0 < (m : ℝ) := by positivity
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hcoef :
      (m : ℝ) ^ 2 / (2 * (S.card : ℝ) ^ 2) ≤
        1 / ((P i).card : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    field_simp
    nlinarith
  have hsum :
      0 ≤ ∑ x ∈ P i, ∑ x' ∈ P i,
        zmodNorm (χ * x - χ * x') ^ 2 := by positivity
  nlinarith

theorem psi_zero {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) :
    psi P 0 = 0 := by
  simp [psi, zmodNorm]

/-- The crude bound `ψ(χ)≤m` used to terminate the dyadic partition. -/
theorem psi_le_m {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) :
    psi P χ ≤ m := by
  unfold psi
  calc
    ∑ i,
        (1 / ((P i).card : ℝ) ^ 2) *
          ∑ x ∈ P i, ∑ x' ∈ P i,
            zmodNorm (χ * x - χ * x') ^ 2
      ≤ ∑ _i : Fin m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hne : (P i).Nonempty := by
            have hb := Section3External.balanced_block_size_bounds S hm hmS hP i
            have hdiv : 0 < S.card / m := Nat.div_pos (Nat.le_of_lt hm) hmS
            exact Finset.card_pos.mp (lt_of_lt_of_le hdiv hb.1)
          have hcardpos : 0 < ((P i).card : ℝ) := by
            exact_mod_cast hne.card_pos
          have hpair :
              ∑ x ∈ P i, ∑ x' ∈ P i,
                  zmodNorm (χ * x - χ * x') ^ 2
                ≤ ((P i).card : ℝ) ^ 2 := by
            calc
              _ ≤ ∑ x ∈ P i, ∑ _x' ∈ P i, (1 : ℝ) := by
                gcongr with x hx x' hx'
                have hn := zmodNorm_nonneg (χ * x - χ * x')
                have hh := zmodNorm_le_half (χ * x - χ * x')
                nlinarith
              _ = ((P i).card : ℝ) ^ 2 := by simp [pow_two]
          have hcoef : 0 ≤ 1 / ((P i).card : ℝ) ^ 2 := by positivity
          calc
            _ ≤ (1 / ((P i).card : ℝ) ^ 2) *
                  ((P i).card : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hpair hcoef
            _ = 1 := by field_simp
    _ = m := by simp

/-- The dyadic decomposition bound before averaging over partitions. -/
theorem dyadic_conditional_bound {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) * (A0 P).card +
      (1 / (p : ℝ)) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          (At P (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hbase :=
    conditional_sum_mass_le_exp_psi hp S hm
      (le_trans hm4 (Nat.div_le_self _ _)) hP z
  have hψ := psi_le_m S hm (le_trans hm4 (Nat.div_le_self _ _)) hP
  -- Group the character sum according to A₀,A₁,A₂,A₄,...
  calc
    conditionalSumMass P z
      ≤ (1 / (p : ℝ)) * ∑ χ : ZMod p, Real.exp (-psi P χ) := hbase
    _ ≤ (1 / (p : ℝ)) * (A0 P).card +
        (1 / (p : ℝ)) *
          ∑ l ∈ Finset.range (Nat.log2 m + 1),
            (At P (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l) := by
      -- This is a finite partition by the dyadic intervals containing ψ(χ).
      classical
      have hnonneg : ∀ χ, 0 ≤ psi P χ := by
        intro χ
        unfold psi
        positivity
      have hcover : ∀ χ : ZMod p,
          χ ∈ A0 P ∨
            ∃ l < Nat.log2 m + 1, χ ∈ At P (2 ^ l) := by
        intro χ
        by_cases hχ : psi P χ < 1
        · exact Or.inl (by simp [A0, hχ])
        · right
          have hχ1 : 1 ≤ psi P χ := le_of_not_gt hχ
          obtain ⟨l, hl, hlo, hhi⟩ :=
            External.exists_dyadic_interval hχ1 (hψ χ)
          exact ⟨l, hl, by simp [At, hlo, hhi]⟩
      have hA0 : ∀ a ∈ A0 P, psi P a < 1 := by
        intro a ha
        simpa [A0] using (Finset.mem_filter.1 ha).2
      have hAt : ∀ l a, a ∈ At P (2 ^ l) →
          (2 : ℝ) ^ l ≤ psi P a := by
        intro l a ha
        simpa [At] using (Finset.mem_filter.1 ha).2.1
      exact External.dyadic_exp_sum_bound
        (psi P) (A0 P) (At P) m hnonneg hcover hA0 hAt

/-- Equation (3.4): average the preceding inequality over the random partition. -/
theorem equation_3_4 {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      (1 / (p : ℝ)) *
        partitionExpectation S (fun P => ((A0 P).card : ℝ)) +
      (1 / (p : ℝ)) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          partitionExpectation S
            (fun P => ((At P (2 ^ l)).card : ℝ)) *
              Real.exp (-(2 : ℝ) ^ l) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [Section3External.sliceMass_eq_partition_average hp S hm
      (le_trans hm4 (Nat.div_le_self _ _)) z]
  apply uniformExpectation_mono
  intro P hP
  have hP' : IsBalancedPartition S P := by
    simpa [balancedPartitions] using hP
  exact dyadic_conditional_bound hp S hS hm hm4 hP' z

end

end GrahamRearrangement
