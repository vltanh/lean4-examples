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

/-- Finite Cauchy--Schwarz in the exact scalar form used in Fact 2.1. -/
axiom cauchySchwarz_sq (xs : List ℝ) :
    xs.sum ^ 2 ≤ (xs.length : ℝ) * (xs.map fun x => x ^ 2).sum

/-- Normed-group list estimate combining the triangle inequality and finite
Cauchy--Schwarz. -/
axiom norm_list_sum_sq {E : Type*} [SeminormedAddCommGroup E] (xs : List E) :
    ‖xs.sum‖ ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => ‖x‖ ^ 2).sum

/-- Triangle inequality for distance to the nearest integer. -/
axiom distToInt_triangle (ys : List ℝ) :
    min (Int.fract ys.sum) (1 - Int.fract ys.sum) ≤
      (ys.map fun y => min (Int.fract y) (1 - Int.fract y)).sum

/-- Periodicity/symmetry reduction for the cosine estimate. -/
axiom cosine_nearest_integer_reduction (y : ℝ) :
    Real.cos (2 * Real.pi * y) =
      Real.cos (2 * Real.pi * min (Int.fract y) (1 - Int.fract y))

/-- The lower Taylor estimate used in Fact 2.2. -/
axiom cosine_taylor_lower {y : ℝ} (hy0 : 0 ≤ y) (hyh : y ≤ 1 / 2) :
    1 - 20 * y ^ 2 ≤ Real.cos (2 * Real.pi * y)

/-- The upper Taylor estimate used in Fact 2.2. -/
axiom cosine_taylor_upper {y : ℝ} (hy0 : 0 ≤ y) (hyh : y ≤ 1 / 2) :
    Real.cos (2 * Real.pi * y) ≤ 1 - 2 * y ^ 2

/-- Nearest-integer distance lies in [0,1/2]. -/
axiom fract_min_mem_half (y : ℝ) :
    0 ≤ min (Int.fract y) (1 - Int.fract y) ∧
      min (Int.fract y) (1 - Int.fract y) ≤ 1 / 2

/-- Real part of the standard additive character. -/
axiom zmod_stdAddChar_re {p : ℕ} [NeZero p] (x : ZMod p) :
    (ZMod.stdAddChar x).re =
      Real.cos (2 * Real.pi * ((x.val : ℝ) / (p : ℝ)))

/-- Compatibility between the AddCircle norm and the paper's representative formula. -/
axiom zmod_addCircle_norm_eq {p : ℕ} [NeZero p] (x : ZMod p) :
    ‖ZMod.toAddCircle x‖ =
      min (Int.fract ((x.val : ℝ) / (p : ℝ)))
        (1 - Int.fract ((x.val : ℝ) / (p : ℝ)))

/-- The paper's explicit exponential character agrees with mathlib's standard one. -/
axiom zmod_exp_character_eq {p : ℕ} [NeZero p] (x : ZMod p) :
    Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ)) = ZMod.stdAddChar x

-- ---------------------------------------------------------------------------
-- Additive combinatorics
-- ---------------------------------------------------------------------------

/-- Cauchy--Davenport, written in integer cardinalities so the empty-set edge case
has the same meaning as the paper's displayed inequality. -/
axiom cauchyDavenportProper {p : ℕ} (hp : p.Prime)
    (A B : Finset (ZMod p)) (hproper : A + B ≠ Finset.univ) :
    ((A.card : ℤ) + (B.card : ℤ) - 1) ≤ ((A + B).card : ℤ)

/-- Iterated Cauchy--Davenport for a finite list of summands. -/
axiom iteratedCauchyDavenportProper {p : ℕ} (hp : p.Prime)
    (sets : List (Finset (ZMod p)))
    (hproper : sets.foldl (· + ·) {0} ≠ Finset.univ) :
    (sets.map fun A => ((A.card : ℤ) - 1)).sum ≤
      (((sets.foldl (· + ·) {0}).card : ℤ) - 1)

/-- Properness propagates to a prefix of an iterated sumset. -/
axiom sumset_prefix_proper {p : ℕ} [NeZero p]
    (sets : List (Finset (ZMod p))) (j : ℕ)
    (hproper : sets.foldl (· + ·) {0} ≠ Finset.univ) :
    (sets.take j).foldl (· + ·) {0} ≠ Finset.univ

-- ---------------------------------------------------------------------------
-- Finite Fourier analysis
-- ---------------------------------------------------------------------------

/-- Orthogonality of the additive characters of Z/pZ. -/
axiom zmod_character_orthogonality {p : ℕ} (hp : p.Prime) (a : ZMod p) :
    (∑ χ : ZMod p, ZMod.stdAddChar (χ * a)) =
      if a = 0 then (p : ℂ) else 0

/-- Character factorization for independent uniform choices from nonempty finite blocks.
This is the standard finite-product expectation identity used in (3.1). -/
axiom independent_block_fourier_bound {p m : ℕ} (hp : p.Prime)
    (blocks : Fin m → Finset (ZMod p))
    (hne : ∀ i, (blocks i).Nonempty) (z : ZMod p) :
    uniformMass
        (Finset.univ.pi blocks)
        (fun X => (∑ i, X i) = z) ≤
      (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ∏ i, ‖((∑ x ∈ blocks i, ZMod.stdAddChar (χ * x)) /
            (blocks i).card : ℂ)‖

/-- Parseval/orthogonality identity used in Lemma 3.6 for a negation-symmetric set
of characters. -/
axiom symmetric_character_square_sum {p : ℕ} (hp : p.Prime)
    (B : Finset (ZMod p)) (hzero : 0 ∈ B)
    (hsymm : ∀ χ ∈ B, -χ ∈ B) :
    ∑ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 =
        (p : ℝ) * B.card

-- ---------------------------------------------------------------------------
-- Finite probability and sampling symmetry
-- ---------------------------------------------------------------------------

/-- Markov inequality on a finite uniform sample space. -/
axiom uniform_markov {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (X : Ω → ℝ) (a : ℝ)
    (hX : ∀ ω ∈ space, 0 ≤ X ω) (ha : 0 < a) :
    uniformMass space (fun ω => a ≤ X ω) ≤
      uniformExpectation space X / a

/-- Union bound over a finite family of events. -/
axiom finite_union_bound {Ω ι : Type*} [DecidableEq Ω] [DecidableEq ι]
    (space : Finset Ω) (I : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] :
    uniformMass space (fun ω => ∃ i ∈ I, E i ω) ≤
      ∑ i ∈ I, uniformMass space (E i)

/-- Translation of a uniformly random subset by a fixed group element is uniform. -/
axiom uniform_subset_translate {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (k : ℕ) (a : G) :
    (S.powersetCard k).card =
      ((S + {a}).powersetCard k).card

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

/-- Generic dyadic-shell estimate used when grouping a finite exponential sum. -/
axiom dyadic_exp_sum_bound {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (A0 : Finset α) (At : ℕ → Finset α) (m : ℕ)
    (hnonneg : ∀ a, 0 ≤ f a)
    (hcover : ∀ a, a ∈ A0 ∨ ∃ l < Nat.log2 m + 1, a ∈ At (2 ^ l))
    (hA0 : ∀ a ∈ A0, f a < 1)
    (hAt : ∀ l a, a ∈ At (2 ^ l) →
      (2 : ℝ) ^ l ≤ f a) :
    (∑ a : α, Real.exp (-f a)) ≤
      (A0.card : ℝ) +
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          (At (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l)

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
