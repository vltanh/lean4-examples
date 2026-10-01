import Lean4Examples.GrahamRearrangement.External.Hypergeometric.Sampling
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace GrahamRearrangement.External.Hypergeometric

/-!
# Finite Hoeffding inequality without replacement

We prove the lower-tail estimate needed by Pham--Sauermann.  The only analytic
ingredient is mathlib's proved Hoeffding lemma
`ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`.
The without-replacement part is proved here by exposing one draw at a time.
-/

noncomputable section

theorem uniformExpectation_smul_left
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    uniformExpectation space (fun ω => c * f ω) =
      c * uniformExpectation space f := by
  unfold uniformExpectation
  rw [Finset.mul_sum]
  ring

theorem withoutReplacementExpectation_smul
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (c : ℝ) (f : List α → ℝ) :
    withoutReplacementExpectation U k (fun xs => c * f xs) =
      c * withoutReplacementExpectation U k f := by
  induction k generalizing U f with
  | zero => simp [withoutReplacementExpectation]
  | succ k ih =>
      rw [withoutReplacementExpectation_succ,
        withoutReplacementExpectation_succ]
      simp_rw [ih]
      exact uniformExpectation_smul_left U c _

theorem withoutReplacementExpectation_congr
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f g : List α → ℝ)
    (h : ∀ xs, f xs = g xs) :
    withoutReplacementExpectation U k f =
      withoutReplacementExpectation U k g := by
  apply le_antisymm
  · exact withoutReplacementExpectation_mono U k f g
      (fun xs => (h xs).le)
  · exact withoutReplacementExpectation_mono U k g f
      (fun xs => (h xs).ge)

theorem withoutReplacementMass_le_one
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : List α → Prop) [DecidablePred E] :
    withoutReplacementMass U k E ≤ 1 := by
  unfold withoutReplacementMass
  calc
    withoutReplacementExpectation U k
        (fun xs => if E xs then 1 else 0)
      ≤ withoutReplacementExpectation U k (fun _ => 1) := by
          apply withoutReplacementExpectation_mono
          intro xs
          split <;> norm_num
    _ = 1 := withoutReplacementExpectation_const U hk 1

/-- Hoeffding's lemma written for the repository's finite uniform expectation.
We pass to the finite subtype of points in the sample space, use mathlib's
uniform probability mass function, and translate the resulting finite sum back. -/
theorem finite_uniform_hoeffding_mgf
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (X : Ω → ℝ) (a b t : ℝ)
    (hab : a ≤ b)
    (hX : ∀ ω ∈ space, X ω ∈ Set.Icc a b)
    (hmean : uniformExpectation space X = 0)
    (ht : 0 < t) :
    uniformExpectation space (fun ω => Real.exp (t * X ω)) ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  classical
  let Ωs := ↥space
  letI : Nonempty Ωs := ⟨⟨hspace.choose,hspace.choose_spec⟩⟩
  letI : MeasurableSpace Ωs := ⊤
  let μ := (PMF.uniformOfFintype Ωs).toMeasure
  letI : IsProbabilityMeasure μ :=
    PMF.toMeasure.isProbabilityMeasure _
  let Xs : Ωs → ℝ := fun ω => X ω.1
  have hsum (f : Ω → ℝ) :
      (∑ ω : Ωs, f ω.1) = ∑ ω ∈ space, f ω := by
    simpa [Ωs] using (Finset.sum_attach space f)
  have hint (f : Ω → ℝ) :
      ∫ ω : Ωs, f ω.1 ∂μ = uniformExpectation space f := by
    rw [PMF.integral_eq_sum]
    simp_rw [PMF.uniformOfFintype_apply]
    change (∑ ω : Ωs,
      ((Fintype.card Ωs : ℝ≥0∞)⁻¹).toReal * f ω.1) =
        uniformExpectation space f
    have hcard : Fintype.card Ωs = space.card := by
      simp [Ωs]
    rw [hcard]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← Finset.mul_sum, hsum]
    unfold uniformExpectation
    have hcardpos : (0 : ℝ) < space.card := by
      exact_mod_cast hspace.card_pos
    field_simp
    ring
  have hmeas : AEMeasurable Xs μ :=
    (measurable_of_finite Xs).aemeasurable
  have hbound : ∀ᵐ ω ∂μ, Xs ω ∈ Set.Icc a b := by
    filter_upwards with ω
    exact hX ω.1 ω.2
  have hcenter : ∫ ω, Xs ω ∂μ = 0 := by
    rw [hint X]
    exact hmean
  have hmgf :=
    ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero
      hmeas hbound hcenter ht
  have hleft :
      ProbabilityTheory.mgf Xs μ t =
        uniformExpectation space (fun ω => Real.exp (t * X ω)) := by
    unfold ProbabilityTheory.mgf
    simpa [Xs] using hint (fun ω => Real.exp (t * X ω))
  rw [hleft] at hmgf
  have hnorm :
      (((↑‖b - a‖₊ : ℝ) / 2) ^ 2 * t ^ 2 / 2) =
        (b - a) ^ 2 * t ^ 2 / 8 := by
    rw [coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    ring
  simpa [hnorm] using hmgf

def successIndicator {α : Type*} [DecidableEq α]
    (G : Finset α) (x : α) : ℝ :=
  if x ∈ G then 1 else 0

def successCount {α : Type*} [DecidableEq α]
    (G : Finset α) (xs : List α) : ℕ :=
  (xs.filter fun x => x ∈ G).length

@[simp] theorem successCount_nil {α : Type*} [DecidableEq α]
    (G : Finset α) :
    successCount G [] = 0 := by
  simp [successCount]

@[simp] theorem successCount_cons {α : Type*} [DecidableEq α]
    (G : Finset α) (x : α) (xs : List α) :
    successCount G (x :: xs) =
      (if x ∈ G then 1 else 0) + successCount G xs := by
  simp [successCount]

theorem successCount_eq_card_toFinset
    {α : Type*} [DecidableEq α]
    (G : Finset α) {xs : List α} (hxs : xs.Nodup) :
    successCount G xs = (xs.toFinset ∩ G).card := by
  induction xs with
  | nil => simp [successCount]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hnd := (List.nodup_cons.mp hxs).2
      simp [successCount,hx,ih hnd]
      by_cases hxG : x ∈ G <;> simp [hxG,hx]

def hypergeomMean {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) : ℝ :=
  if U.card = 0 then 0
  else (k : ℝ) * ((U ∩ G).card : ℝ) / (U.card : ℝ)

def exposureDrift {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (x : α) : ℝ :=
  hypergeomMean U G (k + 1) -
    successIndicator G x -
    hypergeomMean (U.erase x) G k

theorem hypergeomMean_zero (U G : Finset α) :
    hypergeomMean U G 0 = 0 := by
  simp [hypergeomMean]

theorem hypergeomMean_of_nonempty
    {α : Type*} [DecidableEq α]
    {U G : Finset α} (hU : U.Nonempty) (k : ℕ) :
    hypergeomMean U G k =
      (k : ℝ) * ((U ∩ G).card : ℝ) / (U.card : ℝ) := by
  simp [hypergeomMean,hU.card_ne_zero]

theorem erase_inter_card
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {x : α} (hxU : x ∈ U) :
    ((U.erase x) ∩ G).card =
      (U ∩ G).card - (if x ∈ G then 1 else 0) := by
  by_cases hxG : x ∈ G
  · have hx : x ∈ U ∩ G := Finset.mem_inter.mpr ⟨hxU,hxG⟩
    rw [show (U.erase x) ∩ G = (U ∩ G).erase x by
      ext y; simp [and_left_comm,and_assoc]]
    simp [Finset.card_erase_of_mem hx,hxG]
  · have heq : (U.erase x) ∩ G = U ∩ G := by
      ext y
      simp
      constructor
      · rintro ⟨hyU,hyx,hyG⟩
        exact ⟨hyU,hyG⟩
      · rintro ⟨hyU,hyG⟩
        exact ⟨hyU,by intro h; subst y; exact hxG hyG,hyG⟩
    simp [heq,hxG]

def exposureLower {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) : ℝ :=
  -(((U.card - (U ∩ G).card : ℕ) : ℝ) *
      ((U.card - (k + 1) : ℕ) : ℝ) /
      ((U.card : ℝ) * (U.card - 1 : ℕ)))

def exposureUpper {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) : ℝ :=
  ((U ∩ G).card : ℝ) *
      ((U.card - (k + 1) : ℕ) : ℝ) /
      ((U.card : ℝ) * (U.card - 1 : ℕ))

theorem exposureDrift_eq_lower_of_mem
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ} {x : α}
    (hxU : x ∈ U) (hxG : x ∈ G)
    (hU2 : 2 ≤ U.card) :
    exposureDrift U G k = exposureLower U G k := by
  have hU : U.Nonempty := ⟨x,hxU⟩
  have heU : (U.erase x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_erase_of_mem hxU] at hc
    simp at hc
    omega
  rw [exposureDrift,hypergeomMean_of_nonempty hU,
    hypergeomMean_of_nonempty heU]
  rw [Finset.card_erase_of_mem hxU,erase_inter_card hxU]
  simp [successIndicator,hxG,exposureLower]
  have hg : 1 ≤ (U ∩ G).card := by
    exact Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxU,hxG⟩⟩
  field_simp
  ring_nf
  exact_mod_cast (by omega :
    (U ∩ G).card - 1 + 1 = (U ∩ G).card)

theorem exposureDrift_eq_upper_of_not_mem
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ} {x : α}
    (hxU : x ∈ U) (hxG : x ∉ G)
    (hU2 : 2 ≤ U.card) :
    exposureDrift U G k = exposureUpper U G k := by
  have hU : U.Nonempty := ⟨x,hxU⟩
  have heU : (U.erase x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_erase_of_mem hxU] at hc
    simp at hc
    omega
  rw [exposureDrift,hypergeomMean_of_nonempty hU,
    hypergeomMean_of_nonempty heU]
  rw [Finset.card_erase_of_mem hxU,erase_inter_card hxU]
  simp [successIndicator,hxG,exposureUpper]
  field_simp
  ring

theorem exposureDrift_mean_zero
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    uniformExpectation U (exposureDrift U G k) = 0 := by
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  let g := (U ∩ G).card
  have hsuccess :
      (U.filter fun x => x ∈ G).card = g := by
    unfold g
    congr 1
    ext x
    simp [and_comm]
  have hfailure :
      (U.filter fun x => x ∉ G).card = U.card - g := by
    have hparts :=
      Finset.card_filter_add_card_filter_neg_eq U (fun x => x ∈ G)
    rw [hsuccess] at hparts
    omega
  have hsumSuccess :
      (∑ x ∈ U with x ∈ G, exposureDrift U G k x) =
        (g : ℝ) * exposureLower U G k := by
    calc
      _ = ∑ _x ∈ U with _x ∈ G, exposureLower U G k := by
            apply Finset.sum_congr rfl
            intro x hx
            rcases Finset.mem_filter.mp hx with ⟨hxU,hxG⟩
            exact exposureDrift_eq_lower_of_mem hxU hxG hU2
      _ = _ := by simp [hsuccess,mul_comm]
  have hsumFailure :
      (∑ x ∈ U with x ∉ G, exposureDrift U G k x) =
        ((U.card - g : ℕ) : ℝ) * exposureUpper U G k := by
    calc
      _ = ∑ _x ∈ U with _x ∉ G, exposureUpper U G k := by
            apply Finset.sum_congr rfl
            intro x hx
            rcases Finset.mem_filter.mp hx with ⟨hxU,hxG⟩
            exact exposureDrift_eq_upper_of_not_mem hxU hxG hU2
      _ = _ := by simp [hfailure,mul_comm]
  unfold uniformExpectation
  rw [show (∑ x ∈ U, exposureDrift U G k x) =
      (∑ x ∈ U with x ∈ G, exposureDrift U G k x) +
      (∑ x ∈ U with x ∉ G, exposureDrift U G k x) by
        symm
        exact Finset.sum_filter_add_sum_filter_not U
          (fun x => x ∈ G) (exposureDrift U G k)]
  rw [hsumSuccess,hsumFailure]
  unfold exposureLower exposureUpper
  have hg : g ≤ U.card := by
    unfold g
    exact Finset.card_le_card Finset.inter_subset_left
  have hden : (0 : ℝ) <
      (U.card : ℝ) * ((U.card - 1 : ℕ) : ℝ) := by
    positivity
  have hpart :
      ((U.card - g : ℕ) : ℝ) + (g : ℝ) = U.card := by
    exact_mod_cast (Nat.sub_add_cancel hg)
  field_simp
  ring

theorem exposureDrift_mem_Icc
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    ∀ x ∈ U,
      exposureDrift U G k x ∈
        Set.Icc (exposureLower U G k) (exposureUpper U G k) := by
  intro x hx
  by_cases hxG : x ∈ G
  · rw [exposureDrift_eq_lower_of_mem hx hxG hU2]
    constructor
    · rfl
    · unfold exposureLower exposureUpper
      have hg : (U ∩ G).card ≤ U.card :=
        Finset.card_le_card Finset.inter_subset_left
      positivity
  · rw [exposureDrift_eq_upper_of_not_mem hx hxG hU2]
    constructor
    · unfold exposureLower exposureUpper
      positivity
    · rfl

theorem exposure_width_le_one
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    exposureUpper U G k - exposureLower U G k ≤ 1 := by
  let N := U.card
  let g := (U ∩ G).card
  let r := U.card - (k + 1)
  have hg : g ≤ N := by
    dsimp [g,N]
    exact Finset.card_le_card Finset.inter_subset_left
  have hpart : (N - g) + g = N := Nat.sub_add_cancel hg
  have hr : r ≤ N - 1 := by
    dsimp [r,N]
    omega
  have hN2 : 2 ≤ N := by simpa [N] using hU2
  have hden : (0 : ℝ) < (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
    positivity
  have hnum :
      (((g : ℝ) + (N - g : ℕ)) * (r : ℝ)) ≤
        (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
    norm_num at hpart ⊢
    exact_mod_cast Nat.mul_le_mul_left N hr
  unfold exposureUpper exposureLower
  change (g : ℝ) * r / ((N : ℝ) * (N - 1 : ℕ)) -
      (-(((N - g : ℕ) : ℝ) * r /
        ((N : ℝ) * (N - 1 : ℕ)))) ≤ 1
  apply (div_le_iff₀ hden).2
  nlinarith [hnum, show ((N - g : ℕ) : ℝ) + (g : ℝ) = N by
    exact_mod_cast hpart]

theorem exposure_mgf_le
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card)
    (t : ℝ) (ht : 0 < t) :
    uniformExpectation U
        (fun x => Real.exp (t * exposureDrift U G k x)) ≤
      Real.exp (t ^ 2 / 8) := by
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  have hmgf :=
    finite_uniform_hoeffding_mgf
      U hU (exposureDrift U G k)
      (exposureLower U G k) (exposureUpper U G k) t
      (by
        have hwidth := exposure_width_le_one U G k hU2 hk
        linarith)
      (exposureDrift_mem_Icc U G k hU2 hk)
      (exposureDrift_mean_zero U G k hU2 hk) ht
  have hwidth := exposure_width_le_one U G k hU2 hk
  have hsquare :
      (exposureUpper U G k - exposureLower U G k) ^ 2 ≤ 1 := by
    have hnonneg :
        0 ≤ exposureUpper U G k - exposureLower U G k := by
      have hmem := exposureDrift_mem_Icc U G k hU2 hk
      obtain ⟨x,hx⟩ := hU
      exact sub_nonneg.mpr (hmem x hx).1.trans (hmem x hx).2
    nlinarith
  exact le_trans hmgf (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))

theorem centered_success_decomposition
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (x : α) (xs : List α) :
    hypergeomMean U G (k + 1) -
        (successCount G (x :: xs) : ℝ) =
      exposureDrift U G k x +
        (hypergeomMean (U.erase x) G k -
          (successCount G xs : ℝ)) := by
  simp [exposureDrift,successCount]
  ring

/-- Centered exponential moment for sampling without replacement. -/
theorem withoutReplacement_centered_mgf_le
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (t : ℝ) (ht : 0 ≤ t) :
    withoutReplacementExpectation U k
      (fun xs =>
        Real.exp (t *
          (hypergeomMean U G k - (successCount G xs : ℝ)))) ≤
      Real.exp (t ^ 2 * k / 8) := by
  induction k generalizing U with
  | zero =>
      simp [withoutReplacementExpectation,hypergeomMean,successCount]
  | succ k ih =>
      by_cases ht0 : t = 0
      · subst t
        simp [withoutReplacementExpectation_const U hk]
      have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hU : U.Nonempty :=
        Finset.card_pos.mp (lt_of_lt_of_le (Nat.zero_lt_succ k) hk)
      by_cases hU1 : U.card = 1
      · have hk0 : k = 0 := by omega
        subst k
        have hsingle : ∃ x, U = {x} := Finset.card_eq_one.mp hU1
        rcases hsingle with ⟨x,rfl⟩
        simp [withoutReplacementExpectation,hypergeomMean,
          successCount,successIndicator]
        by_cases hxG : x ∈ G <;> simp [hxG]
      have hU2 : 2 ≤ U.card := by omega
      rw [withoutReplacementExpectation_succ]
      have hchild :
          ∀ x ∈ U, k ≤ (U.erase x).card := by
        intro x hx
        rw [Finset.card_erase_of_mem hx]
        omega
      have hpoint : ∀ x ∈ U,
          withoutReplacementExpectation (U.erase x) k
            (fun xs =>
              Real.exp (t *
                (hypergeomMean U G (k + 1) -
                  (successCount G (x :: xs) : ℝ)))) ≤
          Real.exp (t * exposureDrift U G k x) *
            Real.exp (t ^ 2 * k / 8) := by
        intro x hx
        have hdec : ∀ xs,
            Real.exp (t *
                (hypergeomMean U G (k + 1) -
                  (successCount G (x :: xs) : ℝ))) =
              Real.exp (t * exposureDrift U G k x) *
                Real.exp (t *
                  (hypergeomMean (U.erase x) G k -
                    (successCount G xs : ℝ))) := by
          intro xs
          rw [centered_success_decomposition]
          rw [mul_add,Real.exp_add]
        rw [withoutReplacementExpectation_congr
          (U.erase x) k _ _
          hdec]
        rw [withoutReplacementExpectation_smul]
        gcongr
        exact ih (U.erase x) (hchild x hx)
      calc
        uniformExpectation U
            (fun x =>
              withoutReplacementExpectation (U.erase x) k
                (fun xs =>
                  Real.exp (t *
                    (hypergeomMean U G (k + 1) -
                      (successCount G (x :: xs) : ℝ)))))
          ≤ uniformExpectation U
              (fun x =>
                Real.exp (t * exposureDrift U G k x) *
                  Real.exp (t ^ 2 * k / 8)) := by
              apply uniformExpectation_mono U hU
              exact hpoint
        _ = uniformExpectation U
              (fun x => Real.exp (t * exposureDrift U G k x)) *
                Real.exp (t ^ 2 * k / 8) := by
              unfold uniformExpectation
              rw [← Finset.sum_mul]
              ring
        _ ≤ Real.exp (t ^ 2 / 8) *
              Real.exp (t ^ 2 * k / 8) := by
              gcongr
              exact exposure_mgf_le U G k hU2 hk t htpos
        _ = Real.exp (t ^ 2 * (k + 1) / 8) := by
              rw [← Real.exp_add]
              congr 1
              ring

/-- Exponential Markov applied to the centered without-replacement statistic. -/
theorem withoutReplacement_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (d : ℝ) (hd : 0 ≤ d) :
    withoutReplacementMass U k
      (fun xs =>
        (successCount G xs : ℝ) ≤ hypergeomMean U G k - d) ≤
      if k = 0 then 1 else
        Real.exp (-2 * d ^ 2 / k) := by
  by_cases hk0 : k = 0
  · subst k
    simp [withoutReplacementMass,withoutReplacementExpectation]
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
  by_cases hd0 : d = 0
  · subst d
    simpa [hk0] using
      withoutReplacementMass_le_one U k hk
        (fun xs => (successCount G xs : ℝ) ≤ hypergeomMean U G k)
  let t : ℝ := 4 * d / k
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hpoint : ∀ xs,
      (if (successCount G xs : ℝ) ≤ hypergeomMean U G k - d
       then 1 else 0) ≤
        Real.exp (-t * d) *
          Real.exp (t *
            (hypergeomMean U G k - (successCount G xs : ℝ))) := by
    intro xs
    by_cases hE :
        (successCount G xs : ℝ) ≤ hypergeomMean U G k - d
    · simp [hE]
      rw [← Real.exp_add]
      have : 0 ≤ -t*d +
          t*(hypergeomMean U G k - successCount G xs) := by
        nlinarith
      exact (show (1 : ℝ) ≤ Real.exp
        (-t*d + t*(hypergeomMean U G k - successCount G xs)) by
          simpa using Real.one_le_exp this)
    · simp [hE]
      positivity
  unfold withoutReplacementMass
  calc
    withoutReplacementExpectation U k
        (fun xs =>
          if (successCount G xs : ℝ) ≤ hypergeomMean U G k - d
          then 1 else 0)
      ≤ withoutReplacementExpectation U k
          (fun xs =>
            Real.exp (-t*d) *
              Real.exp (t *
                (hypergeomMean U G k - (successCount G xs : ℝ)))) := by
          exact withoutReplacementExpectation_mono U k _ _ hpoint
    _ = Real.exp (-t*d) *
        withoutReplacementExpectation U k
          (fun xs =>
            Real.exp (t *
              (hypergeomMean U G k - (successCount G xs : ℝ)))) := by
          rw [withoutReplacementExpectation_smul]
    _ ≤ Real.exp (-t*d) * Real.exp (t^2*k/8) := by
          gcongr
          exact withoutReplacement_centered_mgf_le U G k hk t (le_of_lt ht)
    _ = Real.exp (-2*d^2/k) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [t]
          field_simp
          ring

end

end GrahamRearrangement.External.Hypergeometric
