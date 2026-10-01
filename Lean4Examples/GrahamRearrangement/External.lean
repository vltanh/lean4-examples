import Lean4Examples.GrahamRearrangement.Probability

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
axiom exp_antitone {a b : ℝ} (h : a ≤ b) :
    Real.exp (-b) ≤ Real.exp (-a)

/-- exp(-c log n) = n^{-c}, in the positive range used throughout the paper. -/
axiom exp_neg_mul_log {n c : ℝ} (hn : 0 < n) :
    Real.exp (-c * Real.log n) = n ^ (-c)

-- ---------------------------------------------------------------------------
-- Elementary asymptotic facts used to choose constants
-- ---------------------------------------------------------------------------

/-- Every real x in [1,m] lies in a dyadic interval [2^l,2^(l+1)). -/
axiom exists_dyadic_interval {x : ℝ} {m : ℕ}
    (hx : 1 ≤ x) (hm : x ≤ m) :
    ∃ l < Nat.log2 m + 1,
      (2 : ℝ) ^ l ≤ x ∧ x < 2 * (2 : ℝ) ^ l

/-- A convenient explicit lower bound for the natural logarithm of two. -/
axiom log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2

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
axiom natFloor_ge_half {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ)

/-- The standard reciprocal-square-root summation estimate. -/
axiom sum_inv_sqrt_le_two_sqrt (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (1 / Real.sqrt (i : ℝ))) ≤
      2 * Real.sqrt (n : ℝ)

/-- Numerical consequence of D=ceil(3/α) when 0<α<1/2. -/
axiom ceil_three_div_ge_seven {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    7 ≤ Nat.ceil (3 / α)

/-- Elementary power inequalities used for the Section 5 choice of C_α. -/
axiom section5_power_inequalities (D : ℕ) (hD : 7 ≤ D) :
    (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
        (D + 1 : ℝ) * (2 : ℝ) ^ D *
          (D : ℝ) ^ (14 * D ^ 2) ∧
      (40 * D : ℝ) ^ D ≤
        (100 : ℝ) * (5 * D : ℝ) ^ (2 * D)

/-- Raising the first Section 5 threshold to α recovers the required
10^4*2^(40D) lower bound. -/
axiom section5_rpow_threshold {α : ℝ} {D : ℕ}
    (hα0 : 0 < α) :
    (10 ^ 4 * (2 : ℝ) ^ (40 * D)) ≤
      (((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α)) ^ α

/-- Standard real-power consequence used in Section 5:
n ≤ p^(1-α) implies n/p ≤ n^(-α). -/
axiom card_div_prime_le_neg_rpow {α : ℝ} {n p : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hupper : (n : ℝ) ≤ (p : ℝ) ^ (1 - α)) :
    (n : ℝ) / p ≤ (n : ℝ) ^ (-α)

/-- Monotonicity of x↦x^{-α} for positive α on [1,∞). -/
axiom neg_rpow_antitone {α : ℝ} (hα : 0 < α)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    y ^ (-α) ≤ x ^ (-α)

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
axiom nat_le_two_pow_40 (D : ℕ) :
    (D : ℝ) ≤ (2 : ℝ) ^ (40 * D)

/-- Elementary growth used in the Section 5 counting estimates. -/
axiom D_plus_one_le_fiveD_pow (D : ℕ) (hD : 7 ≤ D) :
    (D + 1 : ℝ) ≤ (5 * D : ℝ) ^ (2 * D)

/-- Monotonicity of real powers in the exponent for a base at least one. -/
axiom rpow_exponent_mono_of_one_le {x a b : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b) :
    x ^ a ≤ x ^ b

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
