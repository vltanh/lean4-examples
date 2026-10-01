import Lean4Examples.GrahamRearrangement.BooleanSlice.Lemmas

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: proof of Theorem 1.3

This file combines Lemmas 3.1--3.7 with the dyadic Fourier reduction.
-/

noncomputable section

def lowPsiNonzero {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => χ ≠ 0 ∧ psi P χ < 2 * t

theorem lowPsi_partition {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (P : Fin m → Finset (ZMod p)) :
    (lowPsiNonzero P t).card ≤
      (((Finset.univ.erase (0 : ZMod p)) \\ Dset S m t).filter
        (fun χ => psi P χ < 2 * t)).card +
      ((Dset S m t \\ Bset S m (2000 * t)).filter
        (fun χ => psi P χ < 2 * t)).card +
      (Bset S m (2000 * t) \\ {0}).card := by
  classical
  apply Finset.card_le_card
  intro χ hχ
  have hlow := (Finset.mem_filter.1 hχ).2
  by_cases hD : χ ∈ Dset S m t
  · by_cases hB : χ ∈ Bset S m (2000 * t)
    · right
      right
      exact Finset.mem_sdiff.2 ⟨hB, by simpa using hlow.1⟩
    · right
      left
      exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hD, hB⟩, hlow.2⟩
  · left
    exact Finset.mem_filter.2
      ⟨Finset.mem_sdiff.2 ⟨by simpa using hlow.1, hD⟩, hlow.2⟩

/-- Expected number of nonzero characters with ψ(χ)<2t.  This is the estimate
immediately preceding the bounds for A₀ and A_t in the proof of Theorem 1.3. -/
theorem expected_lowPsi_bound {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (htsmall : t ≤ m / (2000 ^ 2)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation S
        (fun P => ((lowPsiNonzero P t).card : ℝ)) ≤
      (10 ^ 4 : ℝ) * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hm, hm4, hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  let T₁ := (Finset.univ.erase (0 : ZMod p)) \\ Dset S m t
  let T₂ := Dset S m t \\ Bset S m (2000 * t)
  let T₃ := Bset S m (2000 * t) \\ {0}
  have h1 : ∀ χ ∈ T₁,
      partitionMass S (fun P => psi P χ < 2 * t) ≤
        1 / (S.card : ℝ) ^ 9 := by
    intro χ hχ
    have hχ0 : χ ≠ 0 := by
      simpa [T₁] using (Finset.mem_sdiff.1 hχ).1
    have hχD : χ ∉ Dset S m t := (Finset.mem_sdiff.1 hχ).2
    exact lemma3_1 hp S hS hmLower hmUpper ht χ hχ0 hχD
  have h2 : ∀ χ ∈ T₂,
      partitionMass S (fun P => psi P χ < 2 * t) ≤
        1 / (S.card : ℝ) ^ 9 := by
    intro χ hχ
    rcases Finset.mem_sdiff.1 hχ with ⟨hD, hB⟩
    exact lemma3_3 hp S hS hmLower hmUpper ht χ hD hB
  have hE1 :=
    Section3External.partitionExpectation_filter_le
      S T₁ (fun χ P => psi P χ < 2 * t) h1
  have hE2 :=
    Section3External.partitionExpectation_filter_le
      S T₂ (fun χ P => psi P χ < 2 * t) h2
  have hparts := Section3External.balancedPartitions_nonempty S hm
    (le_trans hm4 (Nat.div_le_self _ _))
  have hpoint : ∀ P ∈ balancedPartitions S,
      ((lowPsiNonzero P t).card : ℝ) ≤
        ((((T₁.filter fun χ => psi P χ < 2 * t).card : ℝ) +
          ((T₂.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
          (T₃.card : ℝ)) := by
    intro P hP
    exact_mod_cast lowPsi_partition S P
  have hExp :
      partitionExpectation S
          (fun P => ((lowPsiNonzero P t).card : ℝ)) ≤
        (T₁.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₂.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₃.card : ℝ) := by
    calc
      _ ≤ partitionExpectation S
          (fun P =>
            (((T₁.filter fun χ => psi P χ < 2 * t).card : ℝ) +
             ((T₂.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
             (T₃.card : ℝ)) := by
            unfold partitionExpectation
            exact uniformExpectation_mono _ _ _ hpoint
      _ = partitionExpectation S
            (fun P => ((T₁.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
          partitionExpectation S
            (fun P => ((T₂.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
          (T₃.card : ℝ) := by
            unfold partitionExpectation
            rw [uniformExpectation_add, uniformExpectation_add,
              uniformExpectation_const _ hparts]
      _ ≤ _ := by linarith
  have hB :=
    lemma3_4 hp S hbig hm (Nat.mul_pos (by norm_num) ht)
      (by
        have : 2000 * t ≤ m / 2000 := by
          exact Nat.mul_le_div_iff_mul_le
            |>.2 (by
              nlinarith [Nat.mul_le_of_le_div_left htsmall])
        simpa [Nat.mul_assoc] using this)
  have hT12 : (T₁.card : ℝ) + T₂.card ≤ p := by
    exact_mod_cast
      (calc
        T₁.card + T₂.card
          ≤ (Finset.univ.erase (0 : ZMod p)).card := by
              apply Finset.card_union_le_iff.mp
              constructor
              · exact Finset.sdiff_subset.trans Finset.erase_subset
              · exact Finset.sdiff_subset.trans
                  (by
                    intro χ hχ
                    exact Finset.mem_erase.2
                      ⟨(Finset.mem_filter.1 hχ).2.1, Finset.mem_univ χ⟩)
        _ ≤ Fintype.card (ZMod p) := by simp)
  have hT3 :
      (T₃.card : ℝ) ≤
        200 * p * Real.sqrt (2000 * t) /
          ((S.card : ℝ) * Real.sqrt m) := by
    have hzero : (0 : ZMod p) ∈ Bset S m (2000 * t) :=
      (Bset_zero_neg S).1
    have hcard :
        T₃.card + 1 = (Bset S m (2000 * t)).card := by
      simp [T₃, hzero]
    nlinarith [hB]
  have hsqrt2000 :
      Real.sqrt ((2000 : ℝ) * t) ≤ 50 * Real.sqrt t := by
    have ht0 : 0 ≤ (t : ℝ) := by positivity
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2000)]
    have hs : Real.sqrt (2000 : ℝ) ≤ 50 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2000)]
    gcongr
  have hnoise :
      (p : ℝ) / (S.card : ℝ) ^ 9 ≤
        (10 ^ 3 : ℝ) * p * Real.sqrt t /
          ((S.card : ℝ) * Real.sqrt m) := by
    have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
    have hrootm : Real.sqrt (m : ℝ) ≤ S.card := by
      calc
        Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
          exact Real.sqrt_le_self (by positivity) (by exact_mod_cast hm)
        _ ≤ S.card := by exact_mod_cast hmS
    have hSbig : (10 ^ 7 : ℝ) ≤ S.card := by exact_mod_cast hbig
    have htroot : 1 ≤ Real.sqrt t := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ t)]
    positivity
  calc
    partitionExpectation S
        (fun P => ((lowPsiNonzero P t).card : ℝ))
      ≤ (T₁.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₂.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₃.card : ℝ) := hExp
    _ ≤ (p : ℝ) / (S.card : ℝ) ^ 9 +
        200 * p * Real.sqrt (2000 * t) /
          ((S.card : ℝ) * Real.sqrt m) := by
          nlinarith [hT12, hT3]
    _ ≤ (10 ^ 4 : ℝ) * p * Real.sqrt t /
          ((S.card : ℝ) * Real.sqrt m) := by
          nlinarith [hnoise, hsqrt2000]

theorem expected_A0_bound {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation S (fun P => ((A0 P).card : ℝ)) ≤
      1 + (10 ^ 4 : ℝ) * p /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hm, hm4, hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have hm2000 : 1 ≤ m / (2000 ^ 2) := by
    have : 2000 ^ 2 ≤ 10 ^ 7 := by norm_num
    omega
  have hlow :=
    expected_lowPsi_bound hp S hS hmLower hmUpper
      (t := 1) (by norm_num) hm2000
  have hpoint : ∀ P ∈ balancedPartitions S,
      ((A0 P).card : ℝ) ≤ 1 + (lowPsiNonzero P 1).card := by
    intro P hP
    have h0 : (0 : ZMod p) ∈ A0 P := by simp [A0, psi_zero]
    apply_mod_cast Finset.card_le_card
      (show A0 P ⊆ insert 0 (lowPsiNonzero P 1) by
        intro χ hχ
        by_cases hz : χ = 0
        · simp [hz]
        · simp only [Finset.mem_insert]
          right
          simp [lowPsiNonzero, hz, (Finset.mem_filter.1 hχ).2])
  have hparts :=
    Section3External.balancedPartitions_nonempty S hm
      (le_trans hm4 (Nat.div_le_self _ _))
  calc
    partitionExpectation S (fun P => ((A0 P).card : ℝ))
      ≤ partitionExpectation S
          (fun P => 1 + ((lowPsiNonzero P 1).card : ℝ)) := by
            unfold partitionExpectation
            exact uniformExpectation_mono _ _ _ hpoint
    _ = 1 + partitionExpectation S
          (fun P => ((lowPsiNonzero P 1).card : ℝ)) := by
            unfold partitionExpectation
            rw [uniformExpectation_add, uniformExpectation_const _ hparts]
    _ ≤ 1 + (10 ^ 4 : ℝ) * p /
          ((S.card : ℝ) * Real.sqrt m) := by
            simpa using hlow

theorem expected_At_bound {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (htsmall : t ≤ m / 2 ^ 22) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation S (fun P => ((At P t).card : ℝ)) ≤
      (10 ^ 4 : ℝ) * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h2000 : 2000 ^ 2 ≤ 2 ^ 22 := by norm_num
  have hsmall' : t ≤ m / (2000 ^ 2) := by
    exact le_trans htsmall (Nat.div_le_div_left m h2000)
  have hlow :=
    expected_lowPsi_bound hp S hS hmLower hmUpper ht hsmall'
  have hpoint : ∀ P ∈ balancedPartitions S,
      (At P t).card ≤ (lowPsiNonzero P t).card := by
    intro P hP
    apply Finset.card_le_card
    intro χ hχ
    have htmem := (Finset.mem_filter.1 hχ).2
    have hχ0 : χ ≠ 0 := by
      intro hz
      subst hz
      have := psi_zero P
      nlinarith [htmem.1]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hχ0, htmem.2⟩
  calc
    partitionExpectation S (fun P => ((At P t).card : ℝ))
      ≤ partitionExpectation S
          (fun P => ((lowPsiNonzero P t).card : ℝ)) := by
            unfold partitionExpectation
            exact uniformExpectation_mono _ _ _ (by
              intro P hP
              exact_mod_cast hpoint P hP)
    _ ≤ _ := hlow

theorem expected_At_trivial {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    partitionExpectation S (fun P => ((At P t).card : ℝ)) ≤ p := by
  unfold partitionExpectation
  apply uniformExpectation_mono
  intro P hP
  exact_mod_cast (At P t).card_le_univ

/-- Theorem 1.3 with the paper's explicit choice C=2^24. -/
theorem theorem13_explicit :
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : ℕ),
        (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card /
          Real.log (S.card : ℝ) →
        ∀ z : ZMod p,
          sliceMass S m z ≤
            1 / (p : ℝ) +
              (2 ^ 24 : ℝ) /
                ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hmLower hmUpper z
  obtain ⟨hm, hm4, hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have h34 := equation_3_4 hp S hS hm hm4 z
  have hA0 := expected_A0_bound hp S hS hmLower hmUpper
  let E : ℕ → ℝ :=
    fun l => partitionExpectation S
      (fun P => ((At P (2 ^ l)).card : ℝ))
  have hsmall : ∀ l, 2 ^ l ≤ m / 2 ^ 22 →
      E l ≤ (p : ℝ) *
        ((10 ^ 4 : ℝ) / ((S.card : ℝ) * Real.sqrt m)) *
          Real.sqrt ((2 : ℝ) ^ l) := by
    intro l hl
    have ht : 0 < 2 ^ l := pow_pos (by norm_num) _
    have h := expected_At_bound hp S hS hmLower hmUpper ht hl
    dsimp [E]
    nlinarith
  have htriv : ∀ l, E l ≤ p := by
    intro l
    exact expected_At_trivial S
  have hdy :=
    External.weighted_dyadic_split m p
      ((10 ^ 4 : ℝ) / ((S.card : ℝ) * Real.sqrt m)) E
      (by exact_mod_cast hp.pos) hsmall htriv
  have htail :
      22 * Real.exp (-(m : ℝ) / 2 ^ 22) ≤
        22 / (S.card : ℝ) ^ 4 := by
    have hlog :
        4 * Real.log (S.card : ℝ) ≤ (m : ℝ) / 2 ^ 22 := by
      nlinarith [hmLower]
    have hexp := External.exp_antitone hlog
    have hid :=
      External.exp_neg_mul_log (n := (S.card : ℝ)) (c := 4)
        (by positivity)
    rw [hid] at hexp
    nlinarith
  have htail2 :
      22 / (S.card : ℝ) ^ 4 ≤
        22 / ((S.card : ℝ) * Real.sqrt m) := by
    have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
    have hroot : Real.sqrt (m : ℝ) ≤ (S.card : ℝ) ^ 3 := by
      have hrootm : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
        exact Real.sqrt_le_self (by positivity) (by exact_mod_cast hm)
      have hmreal : (m : ℝ) ≤ S.card := by exact_mod_cast hmS
      have hScube : (S.card : ℝ) ≤ (S.card : ℝ) ^ 3 := by
        have : (1 : ℝ) ≤ S.card := by exact_mod_cast le_trans (by norm_num) hS
        nlinarith
      linarith
    field_simp
    nlinarith
  have h30022 : (30022 : ℝ) ≤ 2 ^ 24 := by norm_num
  calc
    sliceMass S m z
      ≤ (1 / (p : ℝ)) *
          partitionExpectation S (fun P => ((A0 P).card : ℝ)) +
        (1 / (p : ℝ)) *
          ∑ l ∈ Finset.range (Nat.log2 m + 1),
            E l * Real.exp (-(2 : ℝ) ^ l) := h34
    _ ≤ (1 / (p : ℝ)) *
          (1 + (10 ^ 4 : ℝ) * p /
            ((S.card : ℝ) * Real.sqrt m)) +
        2 * ((10 ^ 4 : ℝ) /
          ((S.card : ℝ) * Real.sqrt m)) +
        22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
          nlinarith [hA0, hdy]
    _ ≤ 1 / (p : ℝ) +
          30022 / ((S.card : ℝ) * Real.sqrt m) := by
          have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
          field_simp
          nlinarith [htail, htail2]
    _ ≤ 1 / (p : ℝ) +
          (2 ^ 24 : ℝ) /
            ((S.card : ℝ) * Real.sqrt m) := by
          gcongr

/-- Theorem 1.3. -/
theorem theorem13 : Theorem13Statement := by
  refine ⟨(2 ^ 24 : ℝ), by norm_num, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hmLower hmUpper z
  exact theorem13_explicit p hp S hS m hmLower hmUpper z

end

end GrahamRearrangement
