import Lean4Examples.GrahamRearrangement.External.Hypergeometric.Hoeffding

open scoped BigOperators

namespace GrahamRearrangement.External.Hypergeometric

/-!
# Hypergeometric lower tails

The generic without-replacement Hoeffding inequality is transferred from the
sequential sampler to uniform fixed-cardinality subsets, then specialized to
the two constants used by Pham--Sauermann.
-/

noncomputable section

theorem withoutReplacementMass_success_to_subset
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : ℕ → Prop) [DecidablePred E] :
    withoutReplacementMass U k (fun xs => E (successCount G xs)) =
      uniformMass (U.powersetCard k)
        (fun T => E ((T ∩ G).card)) := by
  calc
    withoutReplacementMass U k (fun xs => E (successCount G xs))
      = withoutReplacementMass U k
          (fun xs => E ((xs.toFinset ∩ G).card)) := by
            apply withoutReplacementMass_congr_on_samples
            intro xs hxs
            rw [successCount_eq_card_toFinset G hxs.2.1]
    _ = uniformMass (U.powersetCard k)
          (fun T => E ((T ∩ G).card)) :=
        withoutReplacementMass_toFinset U k hk
          (fun T => E ((T ∩ G).card))

theorem hypergeomMean_eq_of_subset
    {α : Type*} [DecidableEq α]
    {U G : Finset α} (hGU : G ⊆ U)
    {k : ℕ} (hU : U.Nonempty) :
    hypergeomMean U G k =
      (k : ℝ) * (G.card : ℝ) / (U.card : ℝ) := by
  rw [hypergeomMean_of_nonempty hU,
    Finset.inter_eq_right.mpr hGU]

/-- Hoeffding lower tail for a uniformly random k-subset. -/
theorem uniformSubset_hoeffding_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (d : ℝ) (hd : 0 ≤ d) :
    uniformMass (U.powersetCard k)
      (fun T =>
        ((T ∩ G).card : ℝ) ≤ hypergeomMean U G k - d) ≤
      if k = 0 then 1 else Real.exp (-2 * d ^ 2 / k) := by
  rw [← withoutReplacementMass_success_to_subset
    U G k hk
    (fun r => (r : ℝ) ≤ hypergeomMean U G k - d)]
  exact withoutReplacement_lower_tail U G k hk d hd

theorem quarter_mean_lower
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ}
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hkpos : 0 < k) (hk : k ≤ U.card) :
    (k : ℝ) / 4 ≤ hypergeomMean U G k := by
  have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hkpos hk)
  rw [hypergeomMean_eq_of_subset hGU hU]
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hdensityR : (U.card : ℝ) ≤ 4 * (G.card : ℝ) := by
    exact_mod_cast hdensity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  apply (le_div_iff₀ hUpos).2
  nlinarith

theorem three_quarters_mean_lower
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ}
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hkpos : 0 < k) (hk : k ≤ U.card) :
    3 * (k : ℝ) / 4 ≤ hypergeomMean U G k := by
  have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hkpos hk)
  rw [hypergeomMean_eq_of_subset hGU hU]
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hdensityR : 3 * (U.card : ℝ) ≤ 4 * (G.card : ℝ) := by
    exact_mod_cast hdensity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  apply (le_div_iff₀ hUpos).2
  nlinarith

theorem nat_lt_div_implies_real_lt_div
    {r k q : ℕ} (hq : 0 < q)
    (h : r < k / q) :
    (r : ℝ) < (k : ℝ) / q := by
  have hle : r + 1 ≤ k / q := Nat.succ_le_iff.mpr h
  have hmul : q * (r + 1) ≤ k := by
    have h1 : q * (r + 1) ≤ q * (k / q) :=
      Nat.mul_le_mul_left q hle
    have h2 : q * (k / q) ≤ k := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self k q
    exact le_trans h1 h2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).2
  exact_mod_cast (lt_of_lt_of_le
    (show q * r < q * (r + 1) by
      exact Nat.mul_lt_mul_left q (Nat.lt_succ_self r))
    hmul)

/-- The density-1/4 specialization needed in Lemma 3.1. -/
theorem hypergeom_quarter_lower_tail_proved
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 8) ≤
        Real.exp (-(k : ℝ) / 32) := by
  by_cases hk0 : k = 0
  · subst k
    simp [uniformMass]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  let d : ℝ := (k : ℝ) / 8
  have hd : 0 ≤ d := by positivity
  have hmean := quarter_mean_lower hGU hdensity hkpos hk
  have hmono :
      uniformMass (U.powersetCard k)
          (fun T => (T ∩ G).card < k / 8) ≤
        uniformMass (U.powersetCard k)
          (fun T =>
            ((T ∩ G).card : ℝ) ≤ hypergeomMean U G k - d) := by
    apply uniformMass_mono
    intro T hT
    have hreal :
        (((T ∩ G).card : ℕ) : ℝ) < (k : ℝ) / 8 :=
      nat_lt_div_implies_real_lt_div (r := (T ∩ G).card)
        (k := k) (q := 8) (by norm_num) hT
    dsimp [d]
    linarith
  have htail :=
    uniformSubset_hoeffding_lower_tail U G k hk d hd
  rw [if_neg hk0] at htail
  have hexp :
      Real.exp (-2 * d ^ 2 / k) =
        Real.exp (-(k : ℝ) / 32) := by
    congr 1
    dsimp [d]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    field_simp
    ring
  exact le_trans hmono (by simpa [hexp] using htail)

/-- The density-3/4 specialization needed in Lemma 3.3.  Hoeffding gives the
stronger exponent k/8; we weaken it to the paper's k/24. -/
theorem hypergeom_three_quarters_lower_tail_proved
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 2) ≤
        Real.exp (-(k : ℝ) / 24) := by
  by_cases hk0 : k = 0
  · subst k
    simp [uniformMass]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  let d : ℝ := (k : ℝ) / 4
  have hd : 0 ≤ d := by positivity
  have hmean := three_quarters_mean_lower hGU hdensity hkpos hk
  have hmono :
      uniformMass (U.powersetCard k)
          (fun T => (T ∩ G).card < k / 2) ≤
        uniformMass (U.powersetCard k)
          (fun T =>
            ((T ∩ G).card : ℝ) ≤ hypergeomMean U G k - d) := by
    apply uniformMass_mono
    intro T hT
    have hreal :
        (((T ∩ G).card : ℕ) : ℝ) < (k : ℝ) / 2 :=
      nat_lt_div_implies_real_lt_div (r := (T ∩ G).card)
        (k := k) (q := 2) (by norm_num) hT
    dsimp [d]
    linarith
  have htail :=
    uniformSubset_hoeffding_lower_tail U G k hk d hd
  rw [if_neg hk0] at htail
  have hstrong :
      -2 * d ^ 2 / k = -(k : ℝ) / 8 := by
    dsimp [d]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    field_simp
    ring
  have hweak :
      Real.exp (-(k : ℝ) / 8) ≤
        Real.exp (-(k : ℝ) / 24) := by
    apply Real.exp_le_exp.mpr
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
    linarith
  exact le_trans hmono (le_trans
    (by simpa [hstrong] using htail) hweak)

end

end GrahamRearrangement.External.Hypergeometric

namespace GrahamRearrangement.External

/-! Public wrappers preserving the names used by the paper formalization. -/

theorem hypergeom_quarter_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 8) ≤
        Real.exp (-(k : ℝ) / 32) :=
  Hypergeometric.hypergeom_quarter_lower_tail_proved
    U G k hGU hdensity hk

theorem hypergeom_three_quarters_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 2) ≤
        Real.exp (-(k : ℝ) / 24) :=
  Hypergeometric.hypergeom_three_quarters_lower_tail_proved
    U G k hGU hdensity hk

end GrahamRearrangement.External
