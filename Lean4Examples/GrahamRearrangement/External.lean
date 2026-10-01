import Lean4Examples.GrahamRearrangement.Probability
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log

open scoped BigOperators Pointwise

namespace GrahamRearrangement.External

/-!
# External inputs

Only results not proved in Pham--Sauermann are axiomatized here.  The paper's own
Facts, Lemmas, Corollaries, and Theorems are proved in the section modules.

The axioms below are deliberately generic: analytic inequalities, Cauchy--Davenport,
finite Fourier orthogonality/factorization, elementary finite sampling symmetries,
Markov/union bounds, and the hypergeometric Chernoff estimates cited by the paper.
-/

noncomputable section

-- ---------------------------------------------------------------------------
-- Standard real/complex analysis
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Additive combinatorics
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Finite Fourier analysis
-- ---------------------------------------------------------------------------

/-- Orthogonality of the additive characters of Z/pZ. -/
theorem zmod_character_orthogonality {p : ℕ} (hp : p.Prime) (a : ZMod p) :
    (∑ χ : ZMod p, ZMod.stdAddChar (χ * a)) =
      if a = 0 then (p : ℂ) else 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar.mulShift a
  have hsum := AddChar.sum_eq_ite ψ
  have hzero : ψ = 0 ↔ a = 0 := by
    constructor
    · intro hψ
      have h1 := congrArg (fun φ : AddChar (ZMod p) ℂ => φ 1) hψ
      simp [ψ, AddChar.mulShift_apply] at h1
      exact ZMod.injective_stdAddChar (by simpa using h1)
    · intro ha
      subst a
      simp [ψ]
  simpa [ψ, AddChar.mulShift_apply, hzero] using hsum

/-- Character-average norm-square identity, obtained by expanding the square. -/
theorem zmod_character_average_norm_sq {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (hT : T.Nonempty) (χ : ZMod p) :
    ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2 =
      (1 / (T.card : ℝ) ^ 2) *
        ∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re := by
  let A : ℂ := ∑ x ∈ T, ZMod.stdAddChar (χ * x)
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hnorm :
      ‖A / (T.card : ℂ)‖ ^ 2 =
        Complex.normSq A / (T.card : ℝ) ^ 2 := by
    rw [Complex.sq_norm, map_div]
    simp [Complex.normSq_natCast, pow_two]
  have hexpand :
      Complex.normSq A =
        ∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re := by
    have hmul :
        ((Complex.normSq A : ℝ) : ℂ) =
          Complex.conj A * A := Complex.normSq_eq_conj_mul_self
    unfold A at hmul ⊢
    rw [map_sum, Finset.sum_mul, Finset.mul_sum] at hmul
    have hre := congrArg Complex.re hmul
    simp only [Complex.ofReal_re] at hre
    simpa [AddChar.map_sub_eq_div, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using hre
  rw [hnorm, hexpand]
  ring

-- ---------------------------------------------------------------------------
-- Finite probability and sampling symmetry
-- ---------------------------------------------------------------------------

/-- Markov inequality on a finite uniform sample space. -/
theorem uniform_markov {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (X : Ω → ℝ) (a : ℝ)
    (hX : ∀ ω ∈ space, 0 ≤ X ω) (ha : 0 < a) :
    uniformMass space (fun ω => a ≤ X ω) ≤
      uniformExpectation space X / a := by
  unfold uniformMass uniformExpectation
  by_cases hs : space.card = 0
  · simp [hs]
  have hcardpos : (0 : ℝ) < space.card := by
    exact_mod_cast Nat.pos_of_ne_zero hs
  have hsum :
      a * ((space.filter fun ω => a ≤ X ω).card : ℝ) ≤
        ∑ ω ∈ space, X ω := by
    calc
      _ = ∑ _ω ∈ (space.filter fun ω => a ≤ X ω), a := by simp
      _ ≤ ∑ ω ∈ (space.filter fun ω => a ≤ X ω), X ω := by
            gcongr with ω hω
            exact (Finset.mem_filter.mp hω).2
      _ ≤ ∑ ω ∈ space, X ω := by
            apply Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
            intro ω hω hnot
            exact hX ω hω
  apply (div_le_div_iff₀ hcardpos ha).2
  nlinarith

-- ---------------------------------------------------------------------------
-- Hypergeometric concentration (Janson--Luczak--Rucinski)
-- ---------------------------------------------------------------------------

/-- The lower-tail estimate used in Lemma 3.1. -/
axiom hypergeom_quarter_lower_tail {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 8) ≤
        Real.exp (-(k : ℝ) / 32)

/-- The lower-tail estimate used in Lemma 3.3. -/
axiom hypergeom_three_quarters_lower_tail {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 2) ≤
        Real.exp (-(k : ℝ) / 24)

/-- A convenient monotonic consequence of exp for the numerical tail comparisons. -/
theorem exp_antitone {a b : ℝ} (h : a ≤ b) :
    Real.exp (-b) ≤ Real.exp (-a) :=
  Real.exp_le_exp.mpr (neg_le_neg h)

/-- exp(-c log n) = n^{-c}, in the positive range used throughout the paper. -/
theorem exp_neg_mul_log {n c : ℝ} (hn : 0 < n) :
    Real.exp (-c * Real.log n) = n ^ (-c) := by
  rw [Real.rpow_def_of_pos hn]
  congr 1
  ring

-- ---------------------------------------------------------------------------
-- Elementary asymptotic facts used to choose constants
-- ---------------------------------------------------------------------------

/-- Every real x in [1,m] lies in a dyadic interval [2^l,2^(l+1)). -/
theorem exists_dyadic_interval {x : ℝ} {m : ℕ}
    (hx : 1 ≤ x) (hm : x ≤ m) :
    ∃ l < Nat.log2 m + 1,
      (2 : ℝ) ^ l ≤ x ∧ x < 2 * (2 : ℝ) ^ l := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hfloor1 : 1 ≤ Nat.floor x := (Nat.one_le_floor_iff x).2 hx
  have hfloor0 : Nat.floor x ≠ 0 := by omega
  let l := Nat.log 2 (Nat.floor x)
  have hlowN : 2 ^ l ≤ Nat.floor x :=
    Nat.pow_log_le_self 2 hfloor0
  have hlow : ((2 : ℕ) ^ l : ℝ) ≤ x :=
    le_trans (by exact_mod_cast hlowN) (Nat.floor_le hx0)
  have huppN : Nat.floor x < 2 ^ (l + 1) := by
    simpa [l] using Nat.lt_pow_succ_log_self Nat.one_lt_two (Nat.floor x)
  have hxFloor : x < (Nat.floor x : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hupp : x < ((2 : ℕ) ^ (l + 1) : ℝ) := by
    have : (Nat.floor x : ℝ) + 1 ≤ ((2 : ℕ) ^ (l + 1) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr huppN)
    exact lt_of_lt_of_le hxFloor this
  have hfm : Nat.floor x ≤ m :=
    Nat.floor_le_of_le (le_trans hm (by norm_num))
  have hm0 : m ≠ 0 := by
    intro hmz
    subst m
    norm_num at hm
  have hlog : l ≤ Nat.log 2 m := by
    unfold l
    exact Nat.log_mono Nat.one_lt_two hfm
  refine ⟨l, ?_, by exact_mod_cast hlow, ?_⟩
  · rw [Nat.log2_eq_log_two]
    omega
  · norm_num [pow_succ] at hupp ⊢
    simpa [pow_succ] using hupp

/-- A convenient explicit lower bound for the natural logarithm of two. -/
theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)

/-- Generic weighted dyadic split: small shells are controlled by a square-root
bound and the at most 22 remaining shells by the trivial bound. -/
theorem dyadic_weight_le_geometric (l : ℕ) :
    Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l) ≤
      (1 / 2 : ℝ) ^ l := by
  cases l with
  | zero =>
      simp
      exact le_trans (le_of_lt Real.exp_neg_one_lt_half) (by norm_num)
  | succ l =>
      by_cases hl : l < 3
      · interval_cases l <;>
          norm_num [pow_succ, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
            Real.exp_neg] <;>
          nlinarith [Real.exp_one_gt_two, Real.sqrt_two_lt_two]
      · let x : ℝ := (2 : ℝ) ^ (l + 1)
        have hx16 : (16 : ℝ) ≤ x := by
          dsimp [x]
          exact_mod_cast Nat.pow_le_pow_right (by omega)
            (show 4 ≤ l + 1 by omega)
        have hx0 : 0 < x := by positivity
        have hlog :=
          Real.log_le_rpow_div (le_of_lt hx0)
            (show (0 : ℝ) < 1 / 2 by norm_num)
        have hroot : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow
        have h4root : 4 * Real.sqrt x ≤ x := by
          have hs : (4 : ℝ) ≤ Real.sqrt x := by
            apply (le_sqrt hx0.le).2
            nlinarith
          nlinarith [Real.sq_sqrt hx0.le]
        have h2log : 2 * Real.log x ≤ x := by
          rw [hroot] at hlog
          nlinarith
        have hx2exp : x ^ 2 ≤ Real.exp x := by
          have hlogx2 :
              Real.log (x ^ 2) ≤ x := by
            rw [Real.log_pow]
            simpa using h2log
          exact (Real.log_le_iff_le_exp (by positivity)).mp hlogx2
        have hexpinv :
            Real.exp (-x) ≤ 1 / x ^ 2 := by
          rw [Real.exp_neg]
          exact inv_le_inv₀ (by positivity) hx2exp
        have hsqrtle : Real.sqrt x ≤ x := Real.sqrt_le_self (by positivity) (by linarith)
        calc
          Real.sqrt ((2 : ℝ) ^ (l + 1)) *
              Real.exp (-(2 : ℝ) ^ (l + 1))
            = Real.sqrt x * Real.exp (-x) := rfl
          _ ≤ Real.sqrt x * (1 / x ^ 2) := by gcongr
          _ ≤ 1 / x := by
                have : 0 < x := hx0
                field_simp
                nlinarith
          _ = (1 / 2 : ℝ) ^ (l + 1) := by
                dsimp [x]
                rw [one_div, inv_pow]
                ring

theorem dyadic_weight_sum_le_two (N : ℕ) :
    (∑ l ∈ Finset.range N,
      Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l)) ≤ 2 := by
  calc
    _ ≤ ∑ l ∈ Finset.range N, (1 / 2 : ℝ) ^ l := by
          gcongr with l hl
          exact dyadic_weight_le_geometric l
    _ ≤ ∑' l : ℕ, (1 / 2 : ℝ) ^ l :=
      (summable_geometric_two.sum_le_tsum
        (fun l hl => by positivity) (Finset.range N))
    _ = 2 := tsum_geometric_two

theorem terminal_dyadic_indices_card_le
    (m : ℕ) :
    ((Finset.range (Nat.log2 m + 1)).filter
      fun l => m / 2 ^ 22 < 2 ^ l).card ≤ 22 := by
  classical
  let L := Nat.log2 m
  have hsub :
      (Finset.range (L + 1)).filter
          (fun l => m / 2 ^ 22 < 2 ^ l) ⊆
        Finset.Icc (L + 1 - 22) L := by
    intro l hl
    rcases Finset.mem_filter.mp hl with ⟨hlrange, htail⟩
    have hlL : l ≤ L := by
      simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hlrange)
    refine Finset.mem_Icc.mpr ⟨?_,hlL⟩
    by_contra hlow
    have hl22 : l + 22 ≤ L := by omega
    have hm0 : m ≠ 0 := by
      intro hm
      subst m
      simp at htail
    have hpw : 2 ^ (l + 22) ≤ m := by
      rw [Nat.log2_eq_log_two] at hl22
      exact Nat.pow_le_of_le_log hm0 hl22
    have : 2 ^ l ≤ m / 2 ^ 22 := by
      apply (Nat.le_div_iff_mul_le (by positivity)).2
      simpa [pow_add, mul_comm] using hpw
    omega
  calc
    _ ≤ (Finset.Icc (L + 1 - 22) L).card := Finset.card_le_card hsub
    _ ≤ 22 := by
      rw [Nat.card_Icc]
      omega

/-- The final dyadic split in the proof of Theorem 1.3. -/
theorem weighted_dyadic_split (m : ℕ) (p K : ℝ) (E : ℕ → ℝ)
    (hp : 0 < p) (hK : 0 ≤ K)
    (hsmall : ∀ l, 2 ^ l ≤ m / 2 ^ 22 →
      E l ≤ p * K * Real.sqrt ((2 : ℝ) ^ l))
    (htriv : ∀ l, E l ≤ p) :
    (1 / p) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          E l * Real.exp (-(2 : ℝ) ^ l)
      ≤ 2 * K + 22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
  classical
  let I := Finset.range (Nat.log2 m + 1)
  let Ismall := I.filter fun l => 2 ^ l ≤ m / 2 ^ 22
  let Itail := I.filter fun l => m / 2 ^ 22 < 2 ^ l
  have hpartition : I = Ismall ∪ Itail := by
    ext l
    simp [I,Ismall,Itail]
    omega
  have hdisj : Disjoint Ismall Itail := by
    rw [Finset.disjoint_left]
    intro l hs ht
    simp [Ismall,Itail] at hs ht
    omega
  rw [hpartition, Finset.sum_union hdisj, mul_add]
  apply add_le_add
  · calc
      (1 / p) * ∑ l ∈ Ismall,
          E l * Real.exp (-(2 : ℝ) ^ l)
        ≤ K * ∑ l ∈ Ismall,
          Real.sqrt ((2 : ℝ) ^ l) *
            Real.exp (-(2 : ℝ) ^ l) := by
            apply Finset.sum_le_sum
            intro l hl
            have hs := (Finset.mem_filter.mp hl).2
            have he := hsmall l hs
            have hexp : 0 ≤ Real.exp (-(2 : ℝ) ^ l) := Real.exp_nonneg _
            have hp0 : 0 < p := hp
            field_simp
            nlinarith
      _ ≤ K * 2 := by
            gcongr
            apply le_trans
              (Finset.sum_le_sum_of_subset
                (by exact Finset.filter_subset _ _)
                (by intro l hl hnot; positivity))
              (dyadic_weight_sum_le_two (Nat.log2 m + 1))
      _ = 2 * K := by ring
  · have hcard : Itail.card ≤ 22 := by
      simpa [Itail,I] using terminal_dyadic_indices_card_le m
    have hterm : ∀ l ∈ Itail,
        (1 / p) * (E l * Real.exp (-(2 : ℝ) ^ l)) ≤
          Real.exp (-(m : ℝ) / 2 ^ 22) := by
      intro l hl
      have hI := (Finset.mem_filter.mp hl).1
      have htail := (Finset.mem_filter.mp hl).2
      have he := htriv l
      have hreal :
          (m : ℝ) / 2 ^ 22 ≤ (2 : ℝ) ^ l := by
        have hdiv :
            (m : ℝ) / 2 ^ 22 <
              (m / 2 ^ 22 : ℕ) + 1 := by
          have hmod := Nat.mod_lt m (by positivity : 0 < 2^22)
          have hdec := Nat.div_add_mod m (2^22)
          exact (div_lt_iff₀ (by positivity : (0:ℝ)<2^22)).2
            (by exact_mod_cast (by omega :
              m < (m / 2^22 + 1) * 2^22))
        have hint : (m / 2^22 : ℕ) + 1 ≤ 2^l := by omega
        exact le_trans (le_of_lt hdiv) (by exact_mod_cast hint)
      have hexp :=
        exp_antitone hreal
      have hp0 := hp
      calc
        _ ≤ (1 / p) * (p * Real.exp (-(2 : ℝ) ^ l)) := by
              gcongr
              positivity
        _ = Real.exp (-(2 : ℝ) ^ l) := by field_simp
        _ ≤ _ := hexp
    calc
      (1 / p) * ∑ l ∈ Itail,
          E l * Real.exp (-(2 : ℝ) ^ l)
        = ∑ l ∈ Itail,
            (1 / p) * (E l * Real.exp (-(2 : ℝ) ^ l)) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ _l ∈ Itail,
          Real.exp (-(m : ℝ) / 2 ^ 22) := by
            gcongr with l hl
            exact hterm l hl
      _ = (Itail.card : ℝ) *
          Real.exp (-(m : ℝ) / 2 ^ 22) := by simp
      _ ≤ 22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
            gcongr
            exact_mod_cast hcard

/-- Elementary floor estimate used with k=floor(sqrt x). -/
theorem natFloor_ge_half {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  by_cases hx2 : x < 2
  · have hfloor1 : 1 ≤ Nat.floor x :=
      (Nat.one_le_floor_iff x).2 hx
    exact le_trans (by nlinarith) (by exact_mod_cast hfloor1)
  · have hlt : x < (Nat.floor x : ℝ) + 1 :=
      Nat.lt_floor_add_one x
    have hx2' : 2 ≤ x := le_of_not_gt hx2
    nlinarith

/-- The standard reciprocal-square-root summation estimate. -/
theorem inv_sqrt_le_twice_sqrt_sub
    (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt (n : ℝ) ≤
      2 * (Real.sqrt (n : ℝ) - Real.sqrt (n - 1 : ℝ)) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hm0 : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsM : 0 ≤ Real.sqrt ((n - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsquaresN : (Real.sqrt (n : ℝ)) ^ 2 = n :=
    Real.sq_sqrt (le_of_lt hn0)
  have hsquaresM :
      (Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 = n - 1 :=
    Real.sq_sqrt hm0
  have hden :
      Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1)
  have hid :
      (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) = 1 := by
    nlinarith
  have hsum :
      Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt (n : ℝ) := by nlinarith
  apply (div_le_iff₀ hsN).2
  nlinarith [hid,hsum]

theorem sum_inv_sqrt_le_two_sqrt (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (1 / Real.sqrt (i : ℝ))) ≤
      2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hn : n = 0
      · subst n; norm_num
      have hsplit :
          Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
        ext i
        simp
        omega
      rw [hsplit, Finset.sum_insert]
      · have hstep := inv_sqrt_le_twice_sqrt_sub (n + 1) (by omega)
        have hsimp : (n + 1 - 1 : ℕ) = n := by omega
        rw [hsimp] at hstep
        linarith
      · simp

/-- Numerical consequence of D=ceil(3/α) when 0<α<1/2. -/
theorem ceil_three_div_ge_seven {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    7 ≤ Nat.ceil (3 / α) := by
  have h6 : (6 : ℝ) < 3 / α := by
    apply (lt_div_iff₀ hα0).2
    nlinarith
  exact Nat.add_one_le_ceil_iff.mpr h6

/-- Elementary power inequalities used for the Section 5 choice of C_α. -/
theorem section5_power_inequalities (D : ℕ) (hD : 7 ≤ D) :
    (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
        (D + 1 : ℝ) * (2 : ℝ) ^ D *
          (D : ℝ) ^ (14 * D ^ 2) ∧
      (40 * D : ℝ) ^ D ≤
        (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (le_trans (by norm_num) hD)
  have h100 : (100 : ℝ) ≤ (2 : ℝ) ^ D := by
    have : (100 : ℝ) ≤ 2 ^ 7 := by norm_num
    exact le_trans this (pow_le_pow_right₀ (by norm_num) (by omega))
  have h5D : (5 * D : ℝ) ≤ (D : ℝ) ^ 2 := by
    nlinarith
  have hpow5 :
      (5 * D : ℝ) ^ (2 * D) ≤
        (D : ℝ) ^ (4 * D) := by
    calc
      _ ≤ ((D : ℝ) ^ 2) ^ (2 * D) :=
        pow_le_pow_left₀ (by positivity) h5D _
      _ = _ := by rw [← pow_mul]; congr; ring
  have hexp : 4 * D ≤ 14 * D ^ 2 := by omega
  have hpowD :
      (D : ℝ) ^ (4 * D) ≤ (D : ℝ) ^ (14 * D ^ 2) :=
    Real.monotone_rpow_of_base_ge_one hD1 (by exact_mod_cast hexp)
  have hfirst :
      (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
        (D + 1 : ℝ) * (2 : ℝ) ^ D *
          (D : ℝ) ^ (14 * D ^ 2) := by
    have hDp : (1 : ℝ) ≤ D + 1 := by positivity
    nlinarith [mul_le_mul h100 (le_trans hpow5 hpowD)
      (by positivity) (by positivity)]
  have hbase : (40 * D : ℝ) ≤ (5 * D : ℝ) ^ 2 := by
    nlinarith
  have hsecond0 :
      (40 * D : ℝ) ^ D ≤ (5 * D : ℝ) ^ (2 * D) := by
    calc
      _ ≤ ((5 * D : ℝ) ^ 2) ^ D :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [← pow_mul]; congr; ring
  constructor
  · exact hfirst
  · exact le_trans hsecond0 (by
      have hnonneg : 0 ≤ (5 * D : ℝ) ^ (2 * D) := by positivity
      nlinarith)

/-- Raising the first Section 5 threshold to α recovers the required
10^4*2^(40D) lower bound. -/
theorem section5_rpow_threshold {α : ℝ} {D : ℕ}
    (hα0 : 0 < α) :
    (10 ^ 4 * (2 : ℝ) ^ (40 * D)) ≤
      (((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α)) ^ α := by
  let A : ℝ := (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)
  have hA : 0 ≤ A := by positivity
  have hα : α ≠ 0 := ne_of_gt hα0
  have hmul : (1 / α) * α = 1 := by field_simp
  rw [← Real.rpow_mul hA, hmul, Real.rpow_one]
  rfl

/-- Standard real-power consequence used in Section 5:
n ≤ p^(1-α) implies n/p ≤ n^(-α). -/
theorem card_div_prime_le_neg_rpow {α : ℝ} {n p : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hupper : (n : ℝ) ≤ (p : ℝ) ^ (1 - α)) :
    (n : ℝ) / p ≤ (n : ℝ) ^ (-α) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogupper :
      Real.log (n : ℝ) ≤ (1 - α) * Real.log (p : ℝ) := by
    have h := Real.log_le_log hn0 hupper
    rw [Real.log_rpow hp0] at h
    simpa [mul_comm] using h
  have hcoef : 0 < 1 - α := sub_pos.mpr hα1
  have hrecip :
      1 + α ≤ 1 / (1 - α) := by
    apply (le_div_iff₀ hcoef).2
    nlinarith [sq_nonneg α]
  have hlogp :
      (1 + α) * Real.log (n : ℝ) ≤ Real.log (p : ℝ) := by
    have hdiv :
        Real.log (n : ℝ) / (1 - α) ≤ Real.log (p : ℝ) :=
      (div_le_iff₀ hcoef).2 (by simpa [mul_comm] using hlogupper)
    exact le_trans
      (mul_le_mul_of_nonneg_right hrecip hlogn) hdiv
  have hlogs :
      Real.log ((n : ℝ) / p) ≤ Real.log ((n : ℝ) ^ (-α)) := by
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hp0),
      Real.log_rpow hn0]
    nlinarith [hlogp]
  have hleft : 0 < (n : ℝ) / p := div_pos hn0 hp0
  have hright : 0 < (n : ℝ) ^ (-α) :=
    Real.rpow_pos_of_pos hn0 _
  exact (Real.log_le_log_iff hleft hright).mp hlogs

/-- Monotonicity of x↦x^{-α} for positive α on [1,∞). -/
theorem neg_rpow_antitone {α : ℝ} (hα : 0 < α)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    y ^ (-α) ≤ x ^ (-α) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  rw [Real.rpow_neg (le_of_lt hy0), Real.rpow_neg (le_of_lt hx0)]
  exact inv_le_inv₀ (Real.rpow_pos_of_pos hx0 α)
    (Real.rpow_le_rpow (le_of_lt hx0) hxy (le_of_lt hα))

/-- Two-sided reciprocal-square-root kernel sum used for a fixed interval endpoint. -/
theorem reverse_Icc_inv_sqrt_sum (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      1 / Real.sqrt ((n - r : ℕ) : ℝ)) =
    ∑ r ∈ Finset.Icc 1 (n - 1),
      1 / Real.sqrt (r : ℝ) := by
  classical
  apply Finset.sum_bij (fun r _ => n - r)
  · intro r hr
    simp at hr ⊢
    omega
  · intro r hr
    rfl
  · intro a ha b hb h
    simp at ha hb
    omega
  · intro r hr
    refine ⟨n-r, ?_, by omega⟩
    simp at hr ⊢
    omega

theorem two_sided_interval_kernel_sum_le
    (n p : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      ((1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt (r : ℝ))) +
       (1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt ((n - r : ℕ) : ℝ))))) ≤
      2 * (n : ℝ) / p +
        4 * C * Real.sqrt (Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcount : (Finset.Icc 1 (n - 1)).card ≤ n := by
    rw [Nat.card_Icc]
    omega
  have hs := sum_inv_sqrt_le_two_sqrt (n - 1)
  have hs' :
      (∑ r ∈ Finset.Icc 1 (n - 1), 1 / Real.sqrt (r : ℝ))
        ≤ 2 * Real.sqrt (n : ℝ) := by
    exact le_trans hs (by
      gcongr
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1))
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.sum_add_distrib]
  rw [reverse_Icc_inv_sqrt_sum]
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = n :=
    Real.sq_sqrt (le_of_lt hnR)
  calc
    _ = 2 * ((Finset.Icc 1 (n - 1)).card : ℝ) / p +
        2 * (C * Real.sqrt (Real.log (n : ℝ)) / n) *
          (∑ r ∈ Finset.Icc 1 (n - 1),
            1 / Real.sqrt (r : ℝ)) := by
          ring_nf
    _ ≤ 2 * (n : ℝ) / p +
        2 * (C * Real.sqrt (Real.log (n : ℝ)) / n) *
          (2 * Real.sqrt (n : ℝ)) := by
          gcongr
          · exact_mod_cast hcount
          · positivity
    _ = 2 * (n : ℝ) / p +
        4 * C * Real.sqrt (Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ) := by
          field_simp
          nlinarith

/-- Crude elementary growth used in Section 5 numerical union bounds. -/
theorem nat_le_two_pow_40 (D : ℕ) :
    (D : ℝ) ≤ (2 : ℝ) ^ (40 * D) := by
  induction D with
  | zero => simp
  | succ D ih =>
      have hbase : (D + 1 : ℝ) ≤ 2 ^ (D + 1) := by
        induction D with
        | zero => norm_num
        | succ D ihD =>
          rw [pow_succ]
          nlinarith
      have hexp : D + 1 ≤ 40 * (D + 1) := by omega
      exact le_trans hbase
        (pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hexp))

/-- Elementary growth used in the Section 5 counting estimates. -/
theorem D_plus_one_le_fiveD_pow (D : ℕ) (hD : 7 ≤ D) :
    (D + 1 : ℝ) ≤ (5 * D : ℝ) ^ (2 * D) := by
  have hbase : (D + 1 : ℝ) ≤ (5 * D : ℝ) ^ 2 := by
    nlinarith
  have hexp : 2 ≤ 2 * D := by omega
  exact le_trans hbase
    (Real.monotone_rpow_of_base_ge_one
      (by nlinarith : (1 : ℝ) ≤ 5 * D)
      (by exact_mod_cast hexp))

/-- Monotonicity of real powers in the exponent for a base at least one. -/
theorem rpow_exponent_mono_of_one_le {x a b : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b) :
    x ^ a ≤ x ^ b :=
  Real.monotone_rpow_of_base_ge_one hx hab

/-- Linear eventually dominates log-squared. -/
theorem exists_log_sq_threshold (A : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        A * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
  by_cases hA : A ≤ 0
  · refine ⟨2,le_rfl,?_⟩
    intro n hn
    have hlog2 : 0 ≤ (Real.log (n : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  · have hApos : 0 < A := lt_of_not_ge hA
    let B : ℝ := (16 * A) ^ 2
    let N := max 2 (Nat.ceil B)
    refine ⟨N,le_max_left _ _,?_⟩
    intro n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hnB : B ≤ (n : ℝ) := by
      have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil _
      exact le_trans hceil (by
        exact_mod_cast le_trans (le_max_right 2 (Nat.ceil B)) hn)
    have hlog :=
      Real.log_natCast_le_rpow_div n
        (show (0 : ℝ) < 1 / 4 by norm_num)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := by positivity
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hquarter :
        (n : ℝ) ^ (1 / 4 : ℝ) ^ 2 =
          (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul hn0]
      norm_num
    have hlogsq :
        (Real.log (n : ℝ)) ^ 2 ≤
          16 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have := sq_le_sq₀ hlog0 (by positivity) hlog
      simpa [hquarter] using this
    have hrootB :
        16 * A ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hB0 : 0 ≤ 16 * A := by positivity
      have hsquare :
          (16 * A) ^ 2 ≤ (n : ℝ) := by simpa [B] using hnB
      have hsqrt := Real.sqrt_le_sqrt hsquare
      simpa [Real.sqrt_sq_eq_abs,hB0,Real.sqrt_eq_rpow] using hsqrt
    nlinarith [mul_le_mul_of_nonneg_left hlogsq (le_of_lt hApos)]

/-- n^{-1/2} sqrt(log n) is eventually below n^{-α} for α < 1/2. -/
theorem exists_sqrt_log_power_threshold {α K : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) (hK : 0 ≤ K) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        K * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) ≤
          (n : ℝ) ^ (-α) := by
  let β : ℝ := (1 / 2 - α) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  let M : ℝ := max 1 (K / Real.sqrt (2 * β))
  have hM : 1 ≤ M := le_max_left _ _
  let N := max 2 (Nat.ceil (M ^ (1 / β)))
  refine ⟨N,le_max_left _ _,?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hNpow :
      M ^ (1 / β) ≤ (n : ℝ) := by
    have hceil : M ^ (1 / β) ≤ (Nat.ceil (M ^ (1 / β)) : ℝ) :=
      Nat.le_ceil _
    exact le_trans hceil (by
      exact_mod_cast le_trans (le_max_right 2 (Nat.ceil (M ^ (1 / β)))) hn)
  have hMpow : M ≤ (n : ℝ) ^ β := by
    have hmono :=
      Real.rpow_le_rpow (by positivity : 0 ≤ M)
        hNpow (le_of_lt hβ)
    have hM0 : 0 ≤ M := le_trans (by norm_num) hM
    rw [← Real.rpow_mul hM0] at hmono
    have hmul : (1 / β) * β = 1 := by field_simp
    simpa [hmul] using hmono
  have hlog :=
    Real.log_natCast_le_rpow_div n (show 0 < 2 * β by positivity)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by positivity
  have hsqrtlog :
      Real.sqrt (Real.log (n : ℝ)) ≤
        (n : ℝ) ^ β / Real.sqrt (2 * β) := by
    have hs := Real.sqrt_le_sqrt hlog
    rw [Real.sqrt_div (by positivity), Real.sqrt_rpow (by positivity)] at hs
    have hrpow :
        Real.sqrt ((n : ℝ) ^ (2 * β)) = (n : ℝ) ^ β := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hn0)]
      ring_nf
    simpa [hrpow] using hs
  have hKM :
      K / Real.sqrt (2 * β) ≤ M := le_max_right _ _
  have hKsqrt :
      K * Real.sqrt (Real.log (n : ℝ)) ≤
        (n : ℝ) ^ (2 * β) := by
    calc
      _ ≤ K * ((n : ℝ) ^ β / Real.sqrt (2 * β)) := by gcongr
      _ = (K / Real.sqrt (2 * β)) * (n : ℝ) ^ β := by ring
      _ ≤ M * (n : ℝ) ^ β := by gcongr; positivity
      _ ≤ (n : ℝ) ^ β * (n : ℝ) ^ β := by gcongr; positivity
      _ = (n : ℝ) ^ (2 * β) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  have hroot : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  rw [hroot]
  have hexp : 2 * β - 1 / 2 = -α := by
    dsimp [β]
    ring
  have hden : 0 < (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hn0 _
  apply (div_le_iff₀ hden).2
  rw [← Real.rpow_add hn0, show (-α : ℝ) + 1 / 2 = 2 * β by
    dsimp [β]; ring]
  exact hKsqrt

end

end GrahamRearrangement.External
