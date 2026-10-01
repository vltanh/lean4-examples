import Lean4Examples.GrahamRearrangement.BooleanSlice.Fourier

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: concentration and deterministic low-spectrum lemmas

Lemmas 3.1--3.7 and the proof of Lemma 3.4.
-/

noncomputable section

/-- The set of points farther than the Lemma 3.1 threshold from `χx'`. -/
def farSet {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ x' : ZMod p) : Finset (ZMod p) :=
  S.filter fun x =>
    8 * Real.sqrt ((t : ℝ) / m) <
      zmodNorm (χ * x - χ * x')

theorem near_far_card {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (χ x' : ZMod p) :
    (nearSet S m t χ (χ * x')).card +
      (farSet S m t χ x').card = S.card := by
  classical
  have hdisj :
      Disjoint (nearSet S m t χ (χ * x')) (farSet S m t χ x') := by
    rw [Finset.disjoint_left]
    intro x hnear hfar
    have hn := (Finset.mem_filter.1 hnear).2
    have hf := (Finset.mem_filter.1 hfar).2
    linarith
  have hunion :
      nearSet S m t χ (χ * x') ∪ farSet S m t χ x' = S := by
    ext x
    simp only [nearSet, farSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
    · intro hx
      by_cases hle :
          zmodNorm (χ * x - χ * x') ≤
            8 * Real.sqrt ((t : ℝ) / m)
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr ⟨hx, lt_of_not_ge hle⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- If χ is not in D_t, every translate χx' has at least a quarter of S outside
the radius-8 ball. -/
theorem farSet_quarter {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (χ : ZMod p)
    (hχ0 : χ ≠ 0) (hχD : χ ∉ Dset S m t)
    {x' : ZMod p} (hx' : x' ∈ S) :
    S.card ≤ 4 * (farSet S m t χ x').card := by
  classical
  by_contra h
  have hnot : 4 * (farSet S m t χ x').card < S.card := Nat.lt_of_not_ge h
  let y : ZMod p := χ * x'
  have hnear :
      3 * S.card ≤ 4 * (nearSet S m t χ y).card := by
    have hpartition :
        (nearSet S m t χ y).card + (farSet S m t χ x').card = S.card := by
      apply Finset.card_congr
      exact near_far_card S χ x'
    omega
  have : χ ∈ Dset S m t := by
    simp [Dset, hχ0, hnear, y]
  exact hχD this

/-- Section 3 range implies the elementary bounds used by the random partition. -/
theorem section3_basic_bounds (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hlower : (2 ^ 24 : ℝ) * Real.log (SCard : ℝ) ≤ m)
    (hupper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ)) :
    0 < m ∧ m ≤ SCard / 4 ∧ 10 ^ 7 ≤ SCard := by
  have hlogmono : Real.log 2 ≤ Real.log (SCard : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact_mod_cast hS
  have hlog : (1 / 2 : ℝ) ≤ Real.log (SCard : ℝ) :=
    le_trans External.log_two_ge_half hlogmono
  have hmreal : (0 : ℝ) < m := by
    nlinarith [hlower]
  have hm : 0 < m := by exact_mod_cast hmreal
  have hmSreal : (m : ℝ) ≤ (SCard : ℝ) / 4 := by
    have hlogpos : 0 < Real.log (SCard : ℝ) := lt_of_lt_of_le (by norm_num) hlog
    calc
      (m : ℝ) ≤ (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ) := hupper
      _ ≤ (SCard : ℝ) / 500 := by
        apply div_le_iff₀ hlogpos |>.2
        nlinarith
      _ ≤ (SCard : ℝ) / 4 := by
        positivity
  have hmS : m ≤ SCard / 4 := by exact_mod_cast hmSreal
  have hbigm : (10 ^ 7 : ℝ) ≤ m := by
    have : (10 ^ 7 : ℝ) ≤ (2 ^ 24 : ℝ) * (1 / 2 : ℝ) := by norm_num
    linarith
  have hbigS : 10 ^ 7 ≤ SCard := by
    have hmle : m ≤ SCard := le_trans hmS (Nat.div_le_self _ _)
    omega
  exact ⟨hm, hmS, hbigS⟩

/-- The numerical exponential tail comparison used in Lemmas 3.1 and 3.3. -/
theorem section3_tail_nine (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ))
    (c : ℝ) (hc : c ≤ 100) :
    (SCard : ℝ) * Real.exp (-(SCard : ℝ) / (c * m)) ≤
      1 / (SCard : ℝ) ^ 9 := by
  have hlogmono : Real.log 2 ≤ Real.log (SCard : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact_mod_cast hS
  have hlogpos : 0 < Real.log (SCard : ℝ) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogmono
  have hmpos : (0 : ℝ) < m := by
    by_contra hm
    have hm0 : (m : ℝ) = 0 := le_antisymm (le_of_not_gt hm) (by positivity)
    rw [hm0] at hmUpper
    positivity
  have hratio :
      10 * Real.log (SCard : ℝ) ≤
        (SCard : ℝ) / (c * m) := by
    have hcpos : 0 < c := by
      by_cases hz : c ≤ 0
      · have : (SCard : ℝ) / (c * m) ≤ 0 := by positivity
        nlinarith
      · exact lt_of_not_ge hz
    field_simp
    nlinarith [hmUpper, hc]
  have hexp :=
    External.exp_antitone hratio
  have hpow :=
    External.exp_neg_mul_log (n := (SCard : ℝ)) (c := 10)
      (by positivity)
  calc
    (SCard : ℝ) * Real.exp (-(SCard : ℝ) / (c * m))
      ≤ (SCard : ℝ) * Real.exp (-10 * Real.log (SCard : ℝ)) := by
        gcongr
    _ = (SCard : ℝ) * (SCard : ℝ) ^ (-10 : ℝ) := by rw [hpow]
    _ = 1 / (SCard : ℝ) ^ 9 := by
      field_simp
      ring

/-- Deterministic implication used in Lemma 3.1: if every point sees enough far
points in its own block, then ψ(χ)≥2t. -/
theorem psi_ge_two_of_far_rows {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p)
    (hrow : ∀ x' ∈ S,
      S.card / (16 * m) ≤
        ((pointBlock S P x' \\ {x'}) ∩ farSet S m t χ x').card) :
    (2 : ℝ) * t ≤ psi P χ := by
  have h33 := psi_lower_bound S hS hm hm4 hP χ
  have henergy :
      (4 : ℝ) * t * (S.card : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤
        ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
          zmodNorm (χ * x - χ * x') ^ 2 := by
    have hp := Section3External.partition_energy_lower_by_rows
      S P ⟨hP.1, hP.2.1, hP.2.2.1⟩
      (fun x x' => zmodNorm (χ * x - χ * x') ^ 2)
      (fun _ => (4 : ℝ) * t * S.card / m ^ 2)
      (by
        intro i x' hx'
        have hxS : x' ∈ S := hP.1 i hx'
        have hcount := hrow x' hxS
        have hthreshold :
            ∀ x ∈ ((pointBlock S P x' \\ {x'}) ∩ farSet S m t χ x'),
              (64 : ℝ) * t / m <
                zmodNorm (χ * x - χ * x') ^ 2 := by
          intro x hx
          have hfar := (Finset.mem_inter.1 hx).2
          have hdist := (Finset.mem_filter.1 hfar).2
          have hsqrt : 0 ≤ Real.sqrt ((t : ℝ) / m) := Real.sqrt_nonneg _
          have hsqrt_sq :
              (Real.sqrt ((t : ℝ) / m)) ^ 2 = (t : ℝ) / m := by
            rw [Real.sq_sqrt]
            positivity
          nlinarith
        calc
          (4 : ℝ) * t * S.card / m ^ 2
            ≤ (((pointBlock S P x' \\ {x'}) ∩ farSet S m t χ x').card : ℝ) *
                ((64 : ℝ) * t / m) := by
                  exact_mod_cast hcount
                  positivity
          _ ≤ ∑ x ∈ P i, zmodNorm (χ * x - χ * x') ^ 2 := by
                apply Finset.card_mul_le_sum
                intro x hx
                exact le_of_lt (hthreshold x (by
                  simpa [pointBlock, mem_blockIndex S P x' hm hP hxS] using hx)))
    simpa using hp
  nlinarith [h33, henergy]

/-- Lemma 3.1. -/
theorem lemma3_1 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (χ : ZMod p) (hχ0 : χ ≠ 0)
    (hχD : χ ∉ Dset S m t) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionMass S (fun P => psi P χ < 2 * t) ≤
      1 / (S.card : ℝ) ^ 9 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hm, hm4, hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  let BadRow : ZMod p → (Fin m → Finset (ZMod p)) → Prop :=
    fun x' P =>
      ((pointBlock S P x' \\ {x'}) ∩ farSet S m t χ x').card <
        S.card / (16 * m)
  have hsubset : ∀ P, IsBalancedPartition S P →
      psi P χ < 2 * t → ∃ x' ∈ S, BadRow x' P := by
    intro P hP hψ
    by_contra hall
    push_neg at hall
    have hrows : ∀ x' ∈ S,
        S.card / (16 * m) ≤
          ((pointBlock S P x' \\ {x'}) ∩ farSet S m t χ x').card := hall
    have hge := psi_ge_two_of_far_rows S hS hm hm4 hP χ hrows
    linarith
  calc
    partitionMass S (fun P => psi P χ < 2 * t)
      ≤ partitionMass S (fun P => ∃ x' ∈ S, BadRow x' P) := by
          apply uniformMass_mono
          intro P hψ
          have hP : IsBalancedPartition S P := by
            simpa [balancedPartitions] using hψ.1
          exact hsubset P hP hψ.2
    _ ≤ ∑ x' ∈ S, partitionMass S (BadRow x') := by
          exact uniformMass_exists_le_sum
            (balancedPartitions S) S (fun x' P => BadRow x' P)
    _ ≤ ∑ _x' ∈ S, Real.exp (-(S.card : ℝ) / (64 * m)) := by
          gcongr with x' hx'
          have hfar := farSet_quarter S χ hχ0 hχD hx'
          have htail :=
            Section3External.block_sparse_tail S (farSet S m t χ x') x'
              hx'
              (by
                simp [farSet,zmodNorm_nonneg])
              (by intro x hx; exact (Finset.mem_filter.1 hx).1)
              hfar hm hm4
          exact htail
    _ = (S.card : ℝ) * Real.exp (-(S.card : ℝ) / (64 * m)) := by simp
    _ ≤ 1 / (S.card : ℝ) ^ 9 :=
      section3_tail_nine S.card m hS hmUpper 64 (by norm_num)

/-- Lemma 3.2. -/
theorem lemma3_2 {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (ht : 0 < t)
    (χ : ZMod p) (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t)) :
    (200 : ℝ) * t / m * S.card ≤
      ∑ x ∈ S \\ Jset S m t χ,
        zmodNorm (χ * x - centerAt S m t χ) ^ 2 := by
  have hPsi : (2000 : ℝ) * t < Psi S m χ := by
    have hnot :=
      (Finset.mem_filter.not.mp hχB)
    simpa [Bset] using hnot
  have hpair : ∀ x x' : ZMod p,
      zmodNorm (χ * x - χ * x') ^ 2 ≤
        2 * zmodNorm (χ * x - centerAt S m t χ) ^ 2 +
        2 * zmodNorm (χ * x' - centerAt S m t χ) ^ 2 := by
    intro x x'
    have h := fact2_3_general
      [χ * x - centerAt S m t χ,
       -(χ * x' - centerAt S m t χ)]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have htotal :
      (500 : ℝ) * t / m * S.card <
        ∑ x ∈ S,
          zmodNorm (χ * x - centerAt S m t χ) ^ 2 := by
    unfold Psi at hPsi
    have hsum :
        ∑ x ∈ S, ∑ x' ∈ S,
            zmodNorm (χ * x - χ * x') ^ 2 ≤
          4 * S.card *
            ∑ x ∈ S,
              zmodNorm (χ * x - centerAt S m t χ) ^ 2 := by
      calc
        _ ≤ ∑ x ∈ S, ∑ x' ∈ S,
            (2 * zmodNorm (χ * x - centerAt S m t χ) ^ 2 +
             2 * zmodNorm (χ * x' - centerAt S m t χ) ^ 2) := by
              gcongr with x hx x' hx'
              exact hpair x x'
        _ = 4 * S.card *
            ∑ x ∈ S,
              zmodNorm (χ * x - centerAt S m t χ) ^ 2 := by
              ring_nf
              simp
    have hSpos : 0 < (S.card : ℝ) := by
      have hc := centerAt_spec S m t ht hχD
      omega
    field_simp [Psi] at hPsi
    nlinarith [hsum]
  have hJ :
      ∑ x ∈ S ∩ Jset S m t χ,
          zmodNorm (χ * x - centerAt S m t χ) ^ 2
        ≤ (265 : ℝ) * t / m * S.card := by
    calc
      _ ≤ ∑ _x ∈ S ∩ Jset S m t χ,
          (265 : ℝ) * t / m := by
            gcongr with x hx
            have hxJ := (Finset.mem_inter.1 hx).2
            have hdist := (Finset.mem_filter.1 hxJ).2
            have hsqrt_sq :
                (Real.sqrt ((t : ℝ) / m)) ^ 2 = (t : ℝ) / m := by
              rw [Real.sq_sqrt]
              positivity
            nlinarith [zmodNorm_nonneg (χ * x - centerAt S m t χ)]
      _ ≤ (265 : ℝ) * t / m * S.card := by
            simp
            positivity
  have hsplit :
      ∑ x ∈ S,
          zmodNorm (χ * x - centerAt S m t χ) ^ 2 =
        (∑ x ∈ S \\ Jset S m t χ,
          zmodNorm (χ * x - centerAt S m t χ) ^ 2) +
        (∑ x ∈ S ∩ Jset S m t χ,
          zmodNorm (χ * x - centerAt S m t χ) ^ 2) := by
    exact Finset.sum_sdiff_add_sum_inter _ _
  rw [hsplit] at htotal
  nlinarith [hJ]

/-- Deterministic implication used in Lemma 3.3. -/
theorem psi_ge_five_of_dense_rows {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t))
    (hrow : ∀ x ∈ S \\ Jset S m t χ,
      S.card / (4 * m) ≤
        ((pointBlock S P x \\ {x}) ∩
          nearSet S m t χ (centerAt S m t χ)).card) :
    (5 : ℝ) * t ≤ psi P χ := by
  have h33 := psi_lower_bound S hS hm hm4 hP χ
  have hL32 := lemma3_2 S hm (by omega) χ hχD hχB
  have henergy :
      (m : ℝ) / (16 * S.card) *
          ∑ x ∈ S \\ Jset S m t χ,
            zmodNorm (χ * x - centerAt S m t χ) ^ 2 ≤
        ((m : ℝ) ^ 2 / (2 * (S.card : ℝ) ^ 2)) *
          ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
            zmodNorm (χ * x - χ * x') ^ 2 := by
    have hp := Section3External.partition_energy_lower_by_rows
      S P ⟨hP.1, hP.2.1, hP.2.2.1⟩
      (fun x x' => zmodNorm (χ * x - χ * x') ^ 2)
      (fun x =>
        if x ∈ S \\ Jset S m t χ then
          (S.card : ℝ) / (16 * m) *
            zmodNorm (χ * x - centerAt S m t χ) ^ 2
        else 0)
      (by
        intro i x hx
        by_cases hxout : x ∈ S \\ Jset S m t χ
        · simp [hxout]
          have hcount := hrow x hxout
          have hxJ : x ∉ Jset S m t χ := (Finset.mem_sdiff.1 hxout).2
          have hfarcenter :
              16 * Real.sqrt ((t : ℝ) / m) <
                zmodNorm (χ * x - centerAt S m t χ) := by
            simpa [Jset] using hxJ
          calc
            (S.card : ℝ) / (16 * m) *
                zmodNorm (χ * x - centerAt S m t χ) ^ 2
              ≤ (((pointBlock S P x \\ {x}) ∩
                    nearSet S m t χ (centerAt S m t χ)).card : ℝ) *
                  (zmodNorm (χ * x - centerAt S m t χ) / 2) ^ 2 := by
                    exact_mod_cast hcount
                    positivity
            _ ≤ ∑ x' ∈ P i,
                  zmodNorm (χ * x - χ * x') ^ 2 := by
                  apply Finset.card_mul_le_sum
                  intro x' hx'
                  have hnear := (Finset.mem_inter.1 hx').2
                  have hdist := (Finset.mem_filter.1 hnear).2
                  have htri := fact2_3_general
                    [χ * x - χ * x',
                     χ * x' - centerAt S m t χ]
                  nlinarith
        · simp [hxout])
    simp only [Finset.sum_ite_irrel, Finset.sum_sdiff] at hp
    nlinarith [hp]
  nlinarith [h33, henergy, hL32]

/-- Lemma 3.3. -/
theorem lemma3_3 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (χ : ZMod p)
    (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionMass S (fun P => psi P χ < 2 * t) ≤
      1 / (S.card : ℝ) ^ 9 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hm, hm4, hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  let G := nearSet S m t χ (centerAt S m t χ)
  have hGdensity : 3 * S.card ≤ 4 * G.card := centerAt_spec S m t ht hχD
  let BadRow : ZMod p → (Fin m → Finset (ZMod p)) → Prop :=
    fun x P =>
      ((pointBlock S P x \\ {x}) ∩ G).card <
        S.card / (4 * m)
  have hsubset : ∀ P, IsBalancedPartition S P →
      psi P χ < 2 * t → ∃ x ∈ S \\ Jset S m t χ, BadRow x P := by
    intro P hP hψ
    by_contra hall
    push_neg at hall
    have hrows : ∀ x ∈ S \\ Jset S m t χ,
        S.card / (4 * m) ≤
          ((pointBlock S P x \\ {x}) ∩ G).card := hall
    have hge :=
      psi_ge_five_of_dense_rows S hS hm hm4 hP χ hχD hχB hrows
    nlinarith
  calc
    partitionMass S (fun P => psi P χ < 2 * t)
      ≤ partitionMass S
          (fun P => ∃ x ∈ S \\ Jset S m t χ, BadRow x P) := by
          apply uniformMass_mono
          intro P hψ
          have hP : IsBalancedPartition S P := by
            simpa [balancedPartitions] using hψ.1
          exact hsubset P hP hψ.2
    _ ≤ ∑ x ∈ S \\ Jset S m t χ, partitionMass S (BadRow x) := by
          exact uniformMass_exists_le_sum
            (balancedPartitions S) (S \\ Jset S m t χ)
              (fun x P => BadRow x P)
    _ ≤ ∑ _x ∈ S \\ Jset S m t χ,
          Real.exp (-(S.card : ℝ) / (48 * m)) := by
          gcongr with x hx
          have hxS := (Finset.mem_sdiff.1 hx).1
          have htail :=
            Section3External.block_dense_tail S G x hxS
              (by
                have hxJ := (Finset.mem_sdiff.1 hx).2
                intro hxG
                have hnear := (Finset.mem_filter.1 hxG).2
                have hJ : x ∈ Jset S m t χ := by
                  apply Finset.mem_filter.mpr
                  have hsqrt : 0 ≤ Real.sqrt ((t : ℝ) / m) :=
                    Real.sqrt_nonneg _
                  constructor
                  · simp
                  · nlinarith
                exact hxJ hJ)
              (by intro y hy; exact (Finset.mem_filter.1 hy).1)
              hGdensity hm hm4
          exact htail
    _ ≤ (S.card : ℝ) * Real.exp (-(S.card : ℝ) / (48 * m)) := by
          simp
          positivity
    _ ≤ 1 / (S.card : ℝ) ^ 9 :=
      section3_tail_nine S.card m hS hmUpper 48 (by norm_num)

/-- Lemma 3.5. -/
theorem lemma3_5 {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty)
    (hm : 0 < m) (ht : 0 < t) :
    (9 : ℝ) / 10 * S.card ≤ (Qset S m t (10 * t / m)).card := by
  let Ω := S.product S
  let X : ZMod p × ZMod p → ℝ :=
    fun q => ∑ χ ∈ Bset S m t,
      zmodNorm (χ * q.1 - χ * q.2) ^ 2
  have hEX :
      uniformExpectation Ω X ≤
        (Bset S m t).card * ((t : ℝ) / m) := by
    rw [Section3External.pair_uniform_expectation S hS]
    unfold X Psi Bset
    simp_rw [Finset.sum_comm]
    gcongr with χ hχ
    have hmem := (Finset.mem_filter.1 hχ).2
    nlinarith
  have hmarkov :=
    External.uniform_markov Ω X
      ((10 : ℝ) * t / m * (Bset S m t).card)
      (by intro q hq; unfold X; positivity)
      (by
        have hB : 0 < (Bset S m t).card := by
          have h0 : (0 : ZMod p) ∈ Bset S m t := by simp [Bset, Psi]
          exact Finset.card_pos.mpr ⟨0, h0⟩
        positivity)
  have hpair :
      (9 : ℝ) / 10 ≤
        uniformMass Ω
          (fun q => q.1 - q.2 ∈ Qset S m t (10 * t / m)) := by
    have hbad :
        uniformMass Ω
          (fun q => q.1 - q.2 ∉ Qset S m t (10 * t / m)) ≤ 1 / 10 := by
      have hident :
          (fun q => q.1 - q.2 ∉ Qset S m t (10 * t / m)) =
          (fun q => (10 : ℝ) * t / m * (Bset S m t).card ≤ X q) := by
        funext q
        simp [Qset, X]
      rw [hident]
      calc
        _ ≤ uniformExpectation Ω X /
            ((10 : ℝ) * t / m * (Bset S m t).card) := hmarkov
        _ ≤ 1 / 10 := by
          rw [div_le_iff₀]
          · nlinarith [hEX]
          · positivity
    have hcompl :=
      uniformMass_compl_eq_one Ω
        (by
          dsimp [Ω]
          exact hS.product hS)
        (fun q => q.1 - q.2 ∈ Qset S m t (10 * t / m))
    nlinarith
  obtain ⟨y', hyS, hyfiber⟩ :=
    Section3External.exists_fiber_mass_ge_pair_mass S hS
      (fun y y' => y - y' ∈ Qset S m t (10 * t / m))
  have hcardfiber :
      (9 : ℝ) / 10 * S.card ≤
        (S.filter fun y => y - y' ∈ Qset S m t (10 * t / m)).card := by
    unfold uniformMass at hyfiber
    field_simp at hyfiber
    nlinarith [hpair]
  have hinj :
      Set.InjOn (fun y : ZMod p => y - y')
        (S.filter fun y => y - y' ∈ Qset S m t (10 * t / m)) := by
    intro a ha b hb hab
    exact sub_right_injective hab
  calc
    (9 : ℝ) / 10 * S.card
      ≤ (S.filter fun y => y - y' ∈ Qset S m t (10 * t / m)).card :=
        hcardfiber
    _ = ((S.filter fun y => y - y' ∈ Qset S m t (10 * t / m)).image
          (fun y => y - y')).card := by
          symm
          exact Finset.card_image_iff.mpr hinj
    _ ≤ (Qset S m t (10 * t / m)).card := by
          exact_mod_cast Finset.card_le_card (by
            intro x hx
            rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
            exact (Finset.mem_filter.1 hy).2)

/-- The low-energy set is symmetric and contains zero. -/
theorem Bset_zero_neg {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (0 : ZMod p) ∈ Bset S m t ∧
      ∀ χ ∈ Bset S m t, -χ ∈ Bset S m t := by
  constructor
  · simp [Bset, Psi]
  · intro χ hχ
    have hE : Psi S m (-χ) = Psi S m χ := by
      unfold Psi
      congr 2
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro x' hx'
      rw [show (-χ) * x - (-χ) * x' = -(χ * x - χ * x') by ring]
      congr 2
      exact zmodNorm_neg _
    simp [Bset, hE] at hχ ⊢
    exact hχ

theorem character_sum_real_of_neg_symmetric
    {p : ℕ} [NeZero p]
    (B : Finset (ZMod p))
    (hsymm : ∀ χ ∈ B, -χ ∈ B)
    (x : ZMod p) :
    ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) : ℂ).im = 0 := by
  let F : ℂ := ∑ χ ∈ B, ZMod.stdAddChar (χ * x)
  have hconj : Complex.conj F = F := by
    unfold F
    rw [map_sum]
    simp_rw [map_sum]
    have hneg :
        ∑ χ ∈ B, ZMod.stdAddChar ((-χ) * x) =
          ∑ χ ∈ B, ZMod.stdAddChar (χ * x) := by
      apply Finset.sum_bij (fun χ _ => -χ)
      · intro χ hχ
        exact hsymm χ hχ
      · intro χ hχ
        simp
      · intro a ha b hb hab
        exact neg_injective hab
      · intro χ hχ
        exact ⟨-χ, hsymm (-χ) (hsymm χ hχ),
          by simp⟩
    simpa [map_neg, neg_mul] using hneg
  have := congrArg Complex.im hconj
  simpa [F] using this

theorem symmetric_character_square_sum
    {p : ℕ} (hp : p.Prime)
    (B : Finset (ZMod p)) (hzero : 0 ∈ B)
    (hsymm : ∀ χ ∈ B, -χ ∈ B) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∑ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 =
        (p : ℝ) * B.card := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hreal : ∀ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) : ℂ).im = 0 :=
    character_sum_real_of_neg_symmetric B hsymm
  have hsquare : ∀ x : ZMod p,
      ((((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) : ℂ).re) ^ 2 : ℂ) =
        (∑ χ ∈ B, ZMod.stdAddChar (χ * x)) *
          Complex.conj (∑ ψ ∈ B, ZMod.stdAddChar (ψ * x)) := by
    intro x
    apply Complex.ext
    · simp [Complex.normSq_apply, hreal x, pow_two]
    · simp [hreal x]
  have hexpand :
      ∑ x : ZMod p,
        (∑ χ ∈ B, ZMod.stdAddChar (χ * x)) *
          Complex.conj (∑ ψ ∈ B, ZMod.stdAddChar (ψ * x)) =
        (p : ℂ) * B.card := by
    simp_rw [map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ χ ∈ B, ∑ ψ ∈ B,
          ∑ x : ZMod p,
            ZMod.stdAddChar ((χ - ψ) * x) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            apply Finset.sum_congr rfl
            intro ψ hψ
            apply Finset.sum_congr rfl
            intro x hx
            simp [sub_mul, map_sub]
      _ = ∑ χ ∈ B, ∑ ψ ∈ B,
          if χ = ψ then (p : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro χ hχ
            apply Finset.sum_congr rfl
            intro ψ hψ
            have horth :=
              External.zmod_character_orthogonality hp (χ - ψ)
            simpa [mul_comm, sub_eq_zero] using horth
      _ = (p : ℂ) * B.card := by
            simp
  have hre := congrArg Complex.re hexpand
  simp_rw [← hsquare] at hre
  simpa using hre

/-- Lemma 3.6. -/
theorem lemma3_6 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ((Qset S m t (1 / 200)).card : ℝ) ≤
      (5 : ℝ) / 4 * p / (Bset S m t).card := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rcases Bset_zero_neg S with ⟨hzero, hsymm⟩
  have horth :=
    symmetric_character_square_sum hp (Bset S m t) hzero hsymm
  have hpoint : ∀ x ∈ Qset S m t (1 / 200),
      (4 : ℝ) / 5 * (Bset S m t).card ^ 2 ≤
        ((∑ χ ∈ Bset S m t, ZMod.stdAddChar (χ * x)).re) ^ 2 := by
    intro x hx
    have hQ := (Finset.mem_filter.1 hx).2
    have hreal :
        (9 : ℝ) / 10 * (Bset S m t).card ≤
          (∑ χ ∈ Bset S m t, ZMod.stdAddChar (χ * x)).re := by
      calc
        _ = ∑ χ ∈ Bset S m t,
              (1 - 20 * zmodNorm (χ * x) ^ 2) := by
                ring_nf
                simp
        _ ≤ ∑ χ ∈ Bset S m t,
              (ZMod.stdAddChar (χ * x)).re := by
                gcongr with χ hχ
                rw [← ep_eq_stdAddChar]
                exact (fact2_2 ((χ * x).val / p)).1.trans_eq
                  (by rw [stdAddChar_re_eq_cos])
        _ = _ := by simp
      nlinarith [hQ]
    nlinarith
  have hsum :
      ((Qset S m t (1 / 200)).card : ℝ) *
          ((4 : ℝ) / 5 * (Bset S m t).card ^ 2)
        ≤ (p : ℝ) * (Bset S m t).card := by
    calc
      _ ≤ ∑ x ∈ Qset S m t (1 / 200),
          ((∑ χ ∈ Bset S m t, ZMod.stdAddChar (χ * x)).re) ^ 2 := by
            apply Finset.card_mul_le_sum
            exact hpoint
      _ ≤ ∑ x : ZMod p,
          ((∑ χ ∈ Bset S m t, ZMod.stdAddChar (χ * x)).re) ^ 2 := by
            apply Finset.sum_le_sum_of_subset Finset.subset_univ
            intro x hx hnot
            positivity
      _ = (p : ℝ) * (Bset S m t).card := horth
  have hBpos : 0 < ((Bset S m t).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hzero⟩
  field_simp
  nlinarith [hsum]

theorem Qset_mono_delta {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    Qset S m t δ₁ ⊆ Qset S m t δ₂ := by
  intro x hx
  have hx' := (Finset.mem_filter.1 hx).2
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, ?_⟩
  have hB : 0 ≤ ((Bset S m t).card : ℝ) := by positivity
  nlinarith

theorem finset_list_sum_comm {ι α : Type*} [DecidableEq ι]
    [AddCommMonoid α] (s : Finset ι) (xs : List α)
    (f : ι → α → α) :
    (∑ i ∈ s, (xs.map fun x => f i x).sum) =
      (xs.map fun x => ∑ i ∈ s, f i x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Finset.sum_add_distrib]

/-- Lemma 3.7. -/
theorem lemma3_7 {p m t k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (δ : ℝ)
    (hk : 0 < k) (hδ : 0 < δ) :
    kfoldSumset (Qset S m t δ) k ⊆
      Qset S m t ((k : ℝ) ^ 2 * δ) := by
  intro x hx
  rcases ((mem_kfoldSumset (Qset S m t δ) x).1 hx) with
    ⟨xs, hlen, hmem, rfl⟩
  simp only [Qset, Finset.mem_filter, Finset.mem_univ, true_and]
  have hχ : ∀ χ ∈ Bset S m t,
      zmodNorm (χ * xs.sum) ^ 2 ≤
        (k : ℝ) * (xs.map fun y => zmodNorm (χ * y) ^ 2).sum := by
    intro χ hχ
    have hsum :
        (xs.map fun y => χ * y).sum = χ * xs.sum := by
      induction xs with
      | nil => simp
      | cons y ys ih => simp [ih, mul_add]
    have h := fact2_3_general (xs.map fun y => χ * y)
    simpa [hsum, hlen, List.map_map, Function.comp_def] using h
  calc
    ∑ χ ∈ Bset S m t, zmodNorm (χ * xs.sum) ^ 2
      ≤ ∑ χ ∈ Bset S m t,
          (k : ℝ) * (xs.map fun y => zmodNorm (χ * y) ^ 2).sum := by
            gcongr with χ hχ'
            exact hχ χ hχ'
    _ = (k : ℝ) *
        (xs.map fun y =>
          ∑ χ ∈ Bset S m t, zmodNorm (χ * y) ^ 2).sum := by
          rw [← finset_list_sum_comm]
          simp [Finset.mul_sum]
    _ < (k : ℝ) * ((k : ℝ) * δ * (Bset S m t).card) := by
          have hy : ∀ y ∈ xs,
              ∑ χ ∈ Bset S m t, zmodNorm (χ * y) ^ 2 <
                δ * (Bset S m t).card := by
            intro y hy
            have hymem : y ∈ Qset S m t δ := hmem y hy
            exact (Finset.mem_filter.1 hymem).2
          have hlist :
              (xs.map fun y =>
                ∑ χ ∈ Bset S m t, zmodNorm (χ * y) ^ 2).sum <
                (xs.length : ℝ) * (δ * (Bset S m t).card) := by
            induction xs with
            | nil => simp at hk
            | cons y ys ih =>
                simp only [List.mem_cons] at hy
                have hy0 := hy y (Or.inl rfl)
                have hys : ∀ z ∈ ys,
                    ∑ χ ∈ Bset S m t, zmodNorm (χ * z) ^ 2 <
                      δ * (Bset S m t).card := by
                  intro z hz
                  exact hy z (Or.inr hz)
                have ih' := ih hys
                simp
                nlinarith
          rw [hlen] at hlist
          exact mul_lt_mul_of_pos_left hlist (by positivity)
    _ = (k : ℝ) ^ 2 * δ * (Bset S m t).card := by ring

/-- Lemma 3.4. -/
theorem lemma3_4 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hSbig : 10 ^ 7 ≤ S.card)
    (hm : 0 < m) (ht : 0 < t) (htm : t ≤ m / 2000) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ((Bset S m t).card : ℝ) ≤
      1 + 200 * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hsmall : (Bset S m t).card < 2
  · have : ((Bset S m t).card : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_two_iff.mp hsmall
    positivity
  · have hB2 : 2 ≤ (Bset S m t).card := Nat.le_of_not_gt hsmall
    have hQsmall :=
      lemma3_6 hp S
    have hQltp : (Qset S m t (1 / 200)).card < p := by
      have hp0 : 0 < p := hp.pos
      have hBreal : (2 : ℝ) ≤ (Bset S m t).card := by exact_mod_cast hB2
      nlinarith [hQsmall]
    let k := Nat.floor (Real.sqrt ((m : ℝ) / (2000 * t)))
    have hsqrt1 : 1 ≤ Real.sqrt ((m : ℝ) / (2000 * t)) := by
      rw [Real.le_sqrt (by norm_num)]
      have htcast : (2000 : ℝ) * t ≤ m := by exact_mod_cast (Nat.mul_le_of_le_div_left htm)
      nlinarith
    have hk1 : 1 ≤ k := by
      exact_mod_cast (le_trans (External.natFloor_ge_half hsqrt1)
        (by nlinarith [hsqrt1]))
    have hklower :
        (1 / 100 : ℝ) * Real.sqrt ((m : ℝ) / t) ≤ k := by
      have hfloor := External.natFloor_ge_half hsqrt1
      have hsqrt_scale :
          (1 / 100 : ℝ) * Real.sqrt ((m : ℝ) / t) ≤
            (1 / 2 : ℝ) * Real.sqrt ((m : ℝ) / (2000 * t)) := by
        rw [← Real.sqrt_div (by positivity), ← Real.sqrt_div (by positivity)]
        nlinarith [Real.sq_sqrt (show 0 ≤ (m : ℝ) / t by positivity)]
      linarith
    have hkδ : (k : ℝ) ^ 2 * ((10 : ℝ) * t / m) ≤ 1 / 200 := by
      have hfloorle : (k : ℝ) ≤ Real.sqrt ((m : ℝ) / (2000 * t)) :=
        Nat.floor_le (Real.sqrt_nonneg _)
      have hsqrt_sq :
          (Real.sqrt ((m : ℝ) / (2000 * t))) ^ 2 =
            (m : ℝ) / (2000 * t) := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith
    have hsumsubset :
        kfoldSumset (Qset S m t ((10 : ℝ) * t / m)) k ⊆
          Qset S m t (1 / 200) := by
      intro x hx
      have hx' :=
        lemma3_7 S ((10 : ℝ) * t / m) (by omega) (by positivity) hx
      exact Qset_mono_delta hkδ hx'
    have hproper :
        kfoldSumset (Qset S m t ((10 : ℝ) * t / m)) k ≠ Finset.univ := by
      intro h
      have hcard :
          p ≤ (Qset S m t (1 / 200)).card := by
        rw [← ZMod.card p, ← Finset.card_univ, ← h]
        exact Finset.card_le_card hsumsubset
      omega
    have hCD :=
      fact2_4 hp (Qset S m t ((10 : ℝ) * t / m)) (by omega) hproper
    have hQlarge := lemma3_5 S (by
      have : 0 < S.card := lt_of_lt_of_le (by norm_num) hSbig
      exact Finset.card_pos.mp this) hm ht
    have hsumcard :
        (4 : ℝ) / 5 * k * S.card ≤
          (kfoldSumset (Qset S m t ((10 : ℝ) * t / m)) k).card := by
      have hSreal : (10 ^ 7 : ℝ) ≤ S.card := by exact_mod_cast hSbig
      have hCDreal : (1 : ℝ) + k *
          (((Qset S m t ((10 : ℝ) * t / m)).card : ℝ) - 1) ≤
          (kfoldSumset (Qset S m t ((10 : ℝ) * t / m)) k).card := by
        exact_mod_cast hCD
      nlinarith [hQlarge]
    have hupper :
        (kfoldSumset (Qset S m t ((10 : ℝ) * t / m)) k).card ≤
          (Qset S m t (1 / 200)).card :=
      Finset.card_le_card hsumsubset
    have hBbound := lemma3_6 hp S
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
    have hSpos : 0 < (S.card : ℝ) := by positivity
    have hrootm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hroott : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by positivity)
    calc
      ((Bset S m t).card : ℝ)
        ≤ 25 / 16 * p / ((k : ℝ) * S.card) := by
          nlinarith [hsumcard, hupper, hBbound]
      _ ≤ 200 * p * Real.sqrt t /
          ((S.card : ℝ) * Real.sqrt m) := by
          have hkl := hklower
          field_simp
          nlinarith
      _ ≤ 1 + 200 * p * Real.sqrt t /
          ((S.card : ℝ) * Real.sqrt m) := by positivity

end

end GrahamRearrangement
