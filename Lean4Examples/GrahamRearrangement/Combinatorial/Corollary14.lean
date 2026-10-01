import Lean4Examples.GrahamRearrangement.Combinatorial.Lemma41

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Corollary 1.4

The three-regime deduction from Theorem 1.3 and Lemma 4.1.
-/

noncomputable section

private def section3Constant : ℝ := 2 ^ 24

theorem log_card_ge_half {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
  have hlogmono : Real.log 2 ≤ Real.log (n : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact_mod_cast hn
  exact le_trans External.log_two_ge_half hlogmono

theorem sqrt_log_card_ge_half {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
  have hlog := log_card_ge_half hn
  have hs := Real.sq_sqrt (show 0 ≤ Real.log (n : ℝ) by
    exact le_trans (by norm_num) hlog)
  have hsnonneg := Real.sqrt_nonneg (Real.log (n : ℝ))
  nlinarith

/-- A deliberately generous coefficient that handles all ground sets below N
without disturbing the asymptotic constants in the main three cases. -/
def smallGroundConstant (N : ℕ) : ℝ :=
  4 * (N : ℝ) ^ 3

theorem small_ground_trivial_bound {p m N : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hSN : S.card < N) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    sliceMass S m z ≤
      smallGroundConstant N * Real.sqrt (Real.log (S.card : ℝ)) /
        ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  have hmass := sliceMass_le_one S z
  have hsqrtlog := sqrt_log_card_ge_half hS
  have hsqrtm : Real.sqrt (m : ℝ) ≤ (S.card : ℝ) := by
    calc
      Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
        exact Real.sqrt_le_self (by positivity) (by exact_mod_cast hm)
      _ ≤ S.card := by exact_mod_cast hmS
  have hSN' : (S.card : ℝ) < N := by exact_mod_cast hSN
  have hSpos : 0 < (S.card : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le (by omega : 0 < S.card) (Nat.le_of_lt hSN)
    exact_mod_cast this
  have hone :
      1 ≤ smallGroundConstant N * Real.sqrt (Real.log (S.card : ℝ)) /
        ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
    unfold smallGroundConstant
    apply (le_div_iff₀ (mul_pos hSpos (Real.sqrt_pos.2 (by exact_mod_cast hm)))).2
    have hsq : (S.card : ℝ) ^ 2 < (N : ℝ) ^ 2 := by nlinarith
    nlinarith
  exact le_trans hmass hone

/-- Consequences of the large-ground-set threshold used in Corollary 1.4. -/
theorem cor14_threshold_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n N : ℕ) (hN : N ≤ n)
    (hthreshold :
      (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2 ≤ n)
    (hn : 2 ≤ n) :
    section3Constant * Real.log (n : ℝ) ≤ (n : ℝ) / 2 ∧
    1 ≤ ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) := by
  have hlog := log_card_ge_half hn
  have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hεle : ε ≤ 1 := le_of_lt hε1
  constructor
  · have hpos : 0 < section3Constant := by positivity
    have hbase :
        2 * section3Constant * Real.log (n : ℝ) ≤ n := by
      have hfac :
          2 * section3Constant * Real.log (n : ℝ) ≤
            (4000 * section3Constant / ε) *
              (Real.log (n : ℝ)) ^ 2 := by
        field_simp
        nlinarith
      exact le_trans hfac hthreshold
    nlinarith
  · have hbase :
        (4 * section3Constant : ℝ) * Real.log (n : ℝ) ≤
          ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) := by
      apply (le_div_iff₀ hlogpos).2
      have := hthreshold
      field_simp at this ⊢
      nlinarith
    have hC : 1 ≤ 4 * section3Constant * Real.log (n : ℝ) := by
      unfold section3Constant
      nlinarith
    exact le_trans hC hbase

/-- Small-m regime of Corollary 1.4. -/
theorem cor14_small_m {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m)
    (hmSmall : (m : ℝ) ≤
      section3Constant * Real.log (S.card : ℝ))
    (hHalf : section3Constant * Real.log (S.card : ℝ) ≤
      (S.card : ℝ) / 2)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      2 * Real.sqrt section3Constant *
        Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hmS : m ≤ S.card := by
    exact_mod_cast le_trans hmSmall (le_trans hHalf (by positivity))
  have h41 := lemma4_1 hp S hm hmS z
  have hden : (S.card : ℝ) / 2 ≤ S.card - m + 1 := by
    exact_mod_cast (by
      have hmhalf : m ≤ S.card / 2 := by exact_mod_cast le_trans hmSmall hHalf
      omega)
  have hrecip :
      1 / ((S.card - m + 1 : ℕ) : ℝ) ≤ 2 / (S.card : ℝ) := by
    have hSpos : 0 < (S.card : ℝ) := by positivity
    have hdenpos : 0 < ((S.card - m + 1 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hdenpos).2
    apply (le_div_iff₀ hSpos).2
    nlinarith
  have hsqrt :
      Real.sqrt (m : ℝ) ≤
        Real.sqrt section3Constant *
          Real.sqrt (Real.log (S.card : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hmSmall
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hSpos : 0 < (S.card : ℝ) := by positivity
  calc
    sliceMass S m z
      ≤ 1 / ((S.card - m + 1 : ℕ) : ℝ) := h41
    _ ≤ 2 / (S.card : ℝ) := hrecip
    _ ≤ 2 * Real.sqrt section3Constant *
          Real.sqrt (Real.log (S.card : ℝ)) /
            ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
      apply (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
        hSpos (mul_pos hSpos hsqrtm)).2
      nlinarith

/-- Middle regime: Theorem 1.3 already gives more than Corollary 1.4. -/
theorem cor14_middle_m {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower :
      section3Constant * Real.log (S.card : ℝ) ≤ (m : ℝ))
    (hmUpper :
      (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card /
        Real.log (S.card : ℝ))
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      1 / (p : ℝ) +
        2 * section3Constant *
          Real.sqrt (Real.log (S.card : ℝ)) /
            ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h13 :=
    theorem13_explicit p hp S hS m hmLower hmUpper z
  have hsqrtlog := sqrt_log_card_ge_half hS
  have hden : 0 < (S.card : ℝ) * Real.sqrt (m : ℝ) := by
    have hm : 0 < m := by
      have hlog := log_card_ge_half hS
      have : (0 : ℝ) < m := by
        unfold section3Constant at hmLower
        nlinarith
      exact_mod_cast this
    positivity
  have hcoef :
      section3Constant ≤
        2 * section3Constant *
          Real.sqrt (Real.log (S.card : ℝ)) := by
    have hC : 0 < section3Constant := by positivity
    nlinarith
  nlinarith [h13, div_le_div_of_nonneg_right hcoef (le_of_lt hden)]

/-- Bounds for m₂ in the large-m regime. -/
theorem cor14_m2_bounds (ε : ℝ) (hε0 : 0 < ε)
    (n m : ℕ) (hn : 2 ≤ n)
    (hthreshold :
      (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2 ≤ n)
    (hlarge :
      ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) < m) :
    let m₂ := Nat.floor
      (ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ))
    m₂ ≤ m ∧
    (ε / 2) * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) ≤ m₂ ∧
    section3Constant * Real.log (n : ℝ) ≤ m₂ := by
  intro m₂
  have hlog := log_card_ge_half hn
  have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hlog
  let x := ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ)
  have hx1 : 1 ≤ x := by
    have hbase :
        4 * section3Constant * Real.log (n : ℝ) ≤ x := by
      dsimp [x]
      apply (le_div_iff₀ hlogpos).2
      field_simp at hthreshold ⊢
      nlinarith
    have hC : 1 ≤ 4 * section3Constant * Real.log (n : ℝ) := by
      unfold section3Constant
      nlinarith
    exact le_trans hC hbase
  have hfloorLower := External.natFloor_ge_half hx1
  have hfloorUpper : (m₂ : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hm2m : m₂ ≤ m := by
    exact_mod_cast le_of_lt (lt_of_le_of_lt hfloorUpper hlarge)
  have hhalf :
      (ε / 2) * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) ≤ m₂ := by
    dsimp [x] at hfloorLower
    nlinarith
  have hC :
      section3Constant * Real.log (n : ℝ) ≤ m₂ := by
    have hbase :
        2 * section3Constant * Real.log (n : ℝ) ≤ x := by
      dsimp [x]
      apply (le_div_iff₀ hlogpos).2
      field_simp at hthreshold ⊢
      nlinarith
    nlinarith [hfloorLower]
  exact ⟨hm2m, hhalf, hC⟩

/-- Corollary 1.4. -/
theorem corollary14 : Corollary14Statement := by
  intro ε hε0 hε1
  let C := section3Constant
  obtain ⟨N, hN2, hNthreshold⟩ :=
    External.exists_log_sq_threshold (4000 * C / ε)
  let Cε : ℝ := max (smallGroundConstant N)
    (max (2 * C) (50 * C * ε ^ (-3 / 2 : ℝ)))
  have hCε : 0 < Cε := by
    dsimp [Cε]
    positivity
  refine ⟨Cε, hCε, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hm hmUpper z
  by_cases hSN : S.card < N
  · have hmS : m ≤ S.card := by
      have hε : 0 < 1 - ε := sub_pos.mpr hε1
      have : (m : ℝ) < S.card := lt_of_le_of_lt hmUpper (by
        nlinarith [show (0 : ℝ) < S.card by positivity])
      exact_mod_cast le_of_lt this
    have hsmall := small_ground_trivial_bound S hS hSN hm hmS z
    have hcoef : smallGroundConstant N ≤ Cε := le_max_left _ _
    have hnonneg :
        0 ≤ Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by positivity
    have := mul_le_mul_of_nonneg_right hcoef hnonneg
    nlinarith [hsmall]
  · have hNS : N ≤ S.card := Nat.le_of_not_gt hSN
    have hthreshold :=
      hNthreshold S.card hNS
    have hHalfAndOne :=
      cor14_threshold_bounds ε hε0 hε1 S.card N hNS
        (by simpa [C] using hthreshold) hS
    by_cases hsmallm :
        (m : ℝ) ≤ C * Real.log (S.card : ℝ)
    · have h :=
        cor14_small_m hp S hS hm
          (by simpa [C] using hsmallm)
          (by simpa [C] using hHalfAndOne.1) z
      have hcoef :
          2 * Real.sqrt C ≤ Cε := by
        have hC : 1 ≤ C := by unfold C section3Constant; norm_num
        calc
          2 * Real.sqrt C ≤ 2 * C := by
            gcongr
            exact Real.sqrt_le_self (by positivity) hC
          _ ≤ max (2 * C) (50 * C * ε ^ (-3 / 2 : ℝ)) :=
            le_max_left _ _
          _ ≤ Cε := le_max_right _ _
      have hfactor :
          0 ≤ Real.sqrt (Real.log (S.card : ℝ)) /
            ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by positivity
      nlinarith [h, mul_le_mul_of_nonneg_right hcoef hfactor]
    · have hmidLower :
          C * Real.log (S.card : ℝ) ≤ (m : ℝ) :=
        le_of_not_ge hsmallm
      by_cases hmidUpper :
          (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card /
            Real.log (S.card : ℝ)
      · have h :=
          cor14_middle_m hp S hS
            (by simpa [C] using hmidLower) hmidUpper z
        have hcoef : 2 * C ≤ Cε := by
          exact le_trans (le_max_left _ _ : 2*C ≤ max (2*C) (50*C*ε^(-3/2:ℝ)))
            (le_max_right _ _)
        have hfactor :
            0 ≤ Real.sqrt (Real.log (S.card : ℝ)) /
              ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by positivity
        nlinarith [h, mul_le_mul_of_nonneg_right hcoef hfactor]
      · have hlarge :
          ε * (1 / 1000 : ℝ) * S.card /
              Real.log (S.card : ℝ) < m := by
          have hεlt1 : ε < 1 := hε1
          have hnot :
              (1 / 1000 : ℝ) * S.card /
                  Real.log (S.card : ℝ) < m :=
            lt_of_not_ge hmidUpper
          have hpositive :
              0 < (1 / 1000 : ℝ) * S.card /
                Real.log (S.card : ℝ) := by
            have hlog := log_card_ge_half hS
            positivity
          nlinarith
        let m₂ := Nat.floor
          (ε * (1 / 1000 : ℝ) * S.card /
            Real.log (S.card : ℝ))
        let m₁ := m - m₂
        obtain ⟨hm2m, hm2lower, hm2C⟩ :=
          cor14_m2_bounds ε hε0 S.card m hS
            (by simpa [C] using hthreshold) hlarge
        have hm12 : m₁ + m₂ = m := by
          dsimp [m₁]
          omega
        have hmS : m ≤ S.card := by
          have hεpos : 0 < 1 - ε := sub_pos.mpr hε1
          have : (m : ℝ) < S.card := lt_of_le_of_lt hmUpper (by
            nlinarith [show (0 : ℝ) < S.card by positivity])
          exact_mod_cast le_of_lt this
        rw [sliceMass, ← hm12,
          Section4External.uniformSubset_split S m₁ m₂
            (by simpa [hm12] using hmS)]
        have houter :
            (S.powersetCard m₁).Nonempty :=
          powersetCard_nonempty S
            (le_trans (Nat.sub_le _ _) hmS)
        apply le_trans
          (uniformExpectation_le_const
            (S.powersetCard m₁) houter _ _ ?_)
        · have hcoef :
              50 * C * ε ^ (-3 / 2 : ℝ) ≤ Cε := by
            exact le_trans
              (le_max_right (2*C) (50*C*ε^(-3/2:ℝ)))
              (le_max_right _ _)
          have hfac :
              0 ≤ Real.sqrt (Real.log (S.card : ℝ)) /
                ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcoef hfac]
        · intro R₁ hR₁
          let U := S \ R₁
          have hR₁sub : R₁ ⊆ S := (Finset.mem_powersetCard.1 hR₁).1
          have hR₁card : R₁.card = m₁ :=
            mem_powersetCard_card hR₁
          have hUcard : U.card = S.card - m₁ := by
            dsimp [U]
            rw [Finset.card_sdiff hR₁sub, hR₁card]
          have hUlower :
              ε * S.card ≤ (U.card : ℝ) := by
            rw [hUcard]
            have hm1le : (m₁ : ℝ) ≤ m := by
              exact_mod_cast Nat.sub_le _ _
            nlinarith [hmUpper]
          have hUne : U.Nonempty := by
            rw [← Finset.card_pos]
            have : (0 : ℝ) < U.card := by positivity
            exact_mod_cast this
          have hlogU :
              Real.log (U.card : ℝ) ≤
                Real.log (S.card : ℝ) :=
            log_card_sdiff_le hR₁sub hUne
          have hm2pos : 0 < m₂ := by
            have : (0 : ℝ) < m₂ := lt_of_lt_of_le
              (mul_pos (by positivity)
                (by positivity)) hm2lower
            exact_mod_cast this
          have hm2lowerU :
              C * Real.log (U.card : ℝ) ≤ (m₂ : ℝ) := by
            exact le_trans (mul_le_mul_of_nonneg_left hlogU (by positivity))
              (by simpa [C] using hm2C)
          have hm2upperU :
              (m₂ : ℝ) ≤
                (1 / 1000 : ℝ) * U.card /
                  Real.log (U.card : ℝ) := by
            have hm2upper :
                (m₂ : ℝ) ≤
                  ε * (1 / 1000 : ℝ) * S.card /
                    Real.log (S.card : ℝ) := Nat.floor_le (by positivity)
            have hlogUpos : 0 < Real.log (U.card : ℝ) := by
              have hU2 : 2 ≤ U.card := by
                have hCbig : (2 : ℝ) ≤ m₂ := by
                  have hlog := log_card_ge_half hS
                  unfold C section3Constant at hm2C
                  nlinarith
                omega
              exact lt_of_lt_of_le (by norm_num) (log_card_ge_half hU2)
            have hlogSpos : 0 < Real.log (S.card : ℝ) :=
              lt_of_lt_of_le (by norm_num) (log_card_ge_half hS)
            apply le_trans hm2upper
            apply (div_le_div_iff₀ hlogSpos hlogUpos).2
            nlinarith
          have hU2 : 2 ≤ U.card := by
            have hCbig : (2 : ℝ) ≤ m₂ := by
              have hlog := log_card_ge_half hS
              unfold C section3Constant at hm2C
              nlinarith
            have hm2U : m₂ ≤ U.card := by
              rw [hUcard]
              dsimp [m₁]
              omega
            omega
          have h13U :=
            theorem13_explicit p hp U hU2 m₂
              (by simpa [C] using hm2lowerU) hm2upperU
              (z - subsetSum R₁)
          have hevent :
              uniformMass (U.powersetCard m₂)
                  (fun R₂ => subsetSum (R₁ ∪ R₂) = z) =
                sliceMass U m₂ (z - subsetSum R₁) := by
            rw [sliceMass]
            apply uniformMass_congr
            intro R₂ hR₂
            have hR₂subU := (Finset.mem_powersetCard.1 hR₂).1
            have hdisj : Disjoint R₁ R₂ := by
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              have hxU := hR₂subU hx2
              exact (Finset.mem_sdiff.1 hxU).2 hx1
            rw [subsetSum_union_disjoint hdisj]
            constructor <;> intro h
            · exact sub_eq_iff_eq_add'.2 h.symm
            · exact (sub_eq_iff_eq_add'.1 h).symm
          rw [hevent]
          have hdenlower :
              ε ^ (3 / 2 : ℝ) * (S.card : ℝ) ^ (3 / 2 : ℝ) /
                    (50 * Real.sqrt (Real.log (S.card : ℝ))) ≤
                (U.card : ℝ) * Real.sqrt (m₂ : ℝ) := by
            have hsqrtm2 :
                Real.sqrt
                    ((ε / 2) * (1 / 1000 : ℝ) * S.card /
                      Real.log (S.card : ℝ)) ≤
                  Real.sqrt (m₂ : ℝ) :=
              Real.sqrt_le_sqrt hm2lower
            have hnum :
                (1 / 50 : ℝ) ≤ Real.sqrt ((1 / 2000 : ℝ)) := by
              have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1/2000 by positivity)
              have hn := Real.sqrt_nonneg (1/2000)
              nlinarith
            have hlogpos : 0 < Real.log (S.card : ℝ) :=
              lt_of_lt_of_le (by norm_num) (log_card_ge_half hS)
            nlinarith [hUlower, hsqrtm2, hnum]
          have hsqrtm :
              Real.sqrt (m : ℝ) ≤ Real.sqrt (S.card : ℝ) :=
            Real.sqrt_le_sqrt (by exact_mod_cast hmS)
          have hlargeBound :
              C / ((U.card : ℝ) * Real.sqrt (m₂ : ℝ)) ≤
                50 * C * ε ^ (-3 / 2 : ℝ) *
                  Real.sqrt (Real.log (S.card : ℝ)) /
                    ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
            have hεpow : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε0 _
            have hSpos : 0 < (S.card : ℝ) := by positivity
            have hlogpos : 0 < Real.sqrt (Real.log (S.card : ℝ)) := by
              apply Real.sqrt_pos.2
              exact lt_of_lt_of_le (by norm_num) (log_card_ge_half hS)
            have hUpos : 0 < (U.card : ℝ) := by positivity
            have hm2root : 0 < Real.sqrt (m₂ : ℝ) := Real.sqrt_pos.2 (by
              exact_mod_cast hm2pos)
            calc
              C / ((U.card : ℝ) * Real.sqrt (m₂ : ℝ))
                ≤ 50 * C * Real.sqrt (Real.log (S.card : ℝ)) /
                    (ε ^ (3 / 2 : ℝ) * (S.card : ℝ) ^ (3 / 2 : ℝ)) := by
                      apply div_le_iff₀ (mul_pos hUpos hm2root) |>.2
                      apply (le_div_iff₀ (mul_pos hεpow
                        (Real.rpow_pos_of_pos hSpos _))).2
                      nlinarith [hdenlower]
              _ ≤ 50 * C * ε ^ (-3 / 2 : ℝ) *
                    Real.sqrt (Real.log (S.card : ℝ)) /
                      ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
                    rw [Real.rpow_neg (le_of_lt hε0)]
                    have hrootS :
                        Real.sqrt (S.card : ℝ) =
                          (S.card : ℝ) ^ (1 / 2 : ℝ) := by
                      symm
                      exact Real.rpow_one_div_natCast (by positivity) 2
                    nlinarith [hsqrtm]
          nlinarith [h13U, hlargeBound]

end

end GrahamRearrangement
