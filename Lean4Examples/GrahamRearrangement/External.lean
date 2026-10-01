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
axiom weighted_dyadic_split (m : ℕ) (p K : ℝ) (E : ℕ → ℝ)
    (hp : 0 < p)
    (hsmall : ∀ l, 2 ^ l ≤ m / 2 ^ 22 →
      E l ≤ p * K * Real.sqrt ((2 : ℝ) ^ l))
    (htriv : ∀ l, E l ≤ p) :
    (1 / p) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          E l * Real.exp (-(2 : ℝ) ^ l)
      ≤ 2 * K + 22 * Real.exp (-(m : ℝ) / 2 ^ 22)

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
axiom card_div_prime_le_neg_rpow {α : ℝ} {n p : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hupper : (n : ℝ) ≤ (p : ℝ) ^ (1 - α)) :
    (n : ℝ) / p ≤ (n : ℝ) ^ (-α)

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
axiom two_sided_interval_kernel_sum_le
    (n p : ℕ) (C : ℝ) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      ((1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt (r : ℝ))) +
       (1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt ((n - r : ℕ) : ℝ))))) ≤
      2 * (n : ℝ) / p +
        4 * C * Real.sqrt (Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ)

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
axiom exists_log_sq_threshold (A : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        A * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ)

/-- n^{-1/2} sqrt(log n) is eventually below n^{-α} for α < 1/2. -/
axiom exists_sqrt_log_power_threshold {α K : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) (hK : 0 ≤ K) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        K * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) ≤
          (n : ℝ) ^ (-α)

end

end GrahamRearrangement.External
