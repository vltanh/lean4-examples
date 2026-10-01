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

/-- Image of a fixed index set under a uniformly random bijection is a uniformly
random subset of the corresponding size. -/
axiom random_bijection_image_uniform {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (S : Finset β) (hcard : Fintype.card α = S.card)
    (I : Finset α) :
    True

/-- Conditioning a uniformly random bijection on finitely many positions leaves a
uniform bijection between the remaining positions and remaining values. -/
axiom random_bijection_conditioning {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (S : Finset β) (hcard : Fintype.card α = S.card) :
    True

/-- Composing a uniformly random bijection with a fixed permutation preserves its law. -/
axiom random_bijection_perm_invariant {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (S : Finset β) (π : Equiv.Perm α) :
    True

/-- The balanced-partition experiment followed by one independent uniform choice
from each block gives a uniform subset of the prescribed size. -/
axiom balanced_partition_one_each_uniform {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (hm : 0 < m) (hle : m ≤ S.card) :
    True

/-- Conditional on the block containing a fixed point in a uniformly random balanced
partition, the other points in that block form a uniform subset of the complement. -/
axiom balanced_partition_block_conditional_uniform {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (x : α) (hx : x ∈ S)
    (hm : 0 < m) (hle : m ≤ S.card) :
    True

/-- A uniformly random nested chain can be exposed by successively taking uniform
subsets of the remaining ground set. -/
axiom uniform_chain_exposure {α : Type*} [DecidableEq α]
    (S : Finset α) (sizes : List ℕ)
    (hmono : sizes.Pairwise (· < ·))
    (hupper : ∀ n ∈ sizes, n < S.card) :
    True

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
