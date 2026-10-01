import Lean4Examples.GrahamRearrangement.Combinatorial.Definitions

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section4External

/-!
# External finite-sampling identities used in Section 4

These are generic facts about finite uniform sampling and conditional probability.
They do not encode Lemma 4.1, Corollary 1.4, Corollary 4.2, or Lemma 4.3.
-/

noncomputable section

/-- A uniform m-subset can be sampled by taking a uniform (m-1)-subset and then
one uniform point from its complement. -/
axiom uniformSubset_twoStage {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard m) E =
      uniformExpectation (S.powersetCard (m - 1))
        (fun R =>
          uniformMass (S \ R) (fun x => E (insert x R)))

/-- A uniform (m₁+m₂)-subset can be sampled by first taking m₁ points and then
m₂ points uniformly from the remaining ground set. -/
axiom uniformSubset_split {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    (hle : m₁ + m₂ ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard (m₁ + m₂)) E =
      uniformExpectation (S.powersetCard m₁)
        (fun R₁ =>
          uniformMass ((S \ R₁).powersetCard m₂)
            (fun R₂ => E (R₁ ∪ R₂)))

/-- If R is an m-subset of S, its complement in S has cardinality |S|-m. -/
axiom card_sdiff_of_mem_powersetCard {α : Type*} [DecidableEq α]
    {S R : Finset α} {m : ℕ} (hR : R ∈ S.powersetCard m) :
    (S \ R).card = S.card - m

/-- The increment sets in a uniformly random nested chain are exposed uniformly
from the unchosen elements.  This is the generic finite-sampling law behind the
exposure argument in Corollary 4.2. -/
axiom uniformChain_exposure {α : Type*} [DecidableEq α]
    {k : ℕ} (S : Finset α) (m : Fin k → ℕ)
    (hm : StrictMono m) (hlo : ∀ i, 1 ≤ m i)
    (hhi : ∀ i, m i < S.card) :
    True

/-- Generic conditional product bound: if an event is the conjunction of a
finite sequence of exposed events and the conditional probability at step i is
at most b_i, then the total probability is at most their product. -/
axiom finiteConditionalProductBound
    {Ω ι : Type*} [DecidableEq Ω] [Fintype ι]
    (space : Finset Ω) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hconditional :
      ∀ i, uniformMass space (E i) ≤ b i) :
    uniformMass space (fun ω => ∀ i, E i ω) ≤ ∏ i, b i

/-- Generic chain-rule bound for the standard exposure of a uniform nested chain.
One gap j is not exposed; for every other gap, the caller supplies a uniform-subset
anticoncentration bound valid for every possible remaining ground set. -/
axiom uniformChain_sumProductBound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    (j : Fin (k + 1)) (ε : ℝ) (hε0 : 0 < ε)
    (b : Fin (k + 1) → ℝ)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          ε * S.card ≤ (U.card : ℝ) →
          (chainGap S.card m i : ℝ) ≤ (1 - ε) * U.card →
          ∀ q : ZMod p,
            uniformMass (U.powersetCard (chainGap S.card m i))
              (fun R => subsetSum R = q) ≤ b i)
    (z : Fin k → ZMod p) :
    chainMass S m z ≤ ∏ i ∈ Finset.univ.erase j, b i

/-- Pigeonhole for the k+1 consecutive gaps of an increasing size tuple. -/
axiom exists_large_chain_gap {k n : ℕ} (m : Fin k → ℕ)
    (hm : IsChainSizeTuple n m) :
    ∃ j : Fin (k + 1),
      (n : ℝ) / (k + 1 : ℝ) ≤ chainGap n m j

/-- Averaging a pointwise bound over a nonempty finite uniform space. -/
axiom uniformExpectation_le_const {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (f : Ω → ℝ) (c : ℝ)
    (h : ∀ ω ∈ space, f ω ≤ c) :
    uniformExpectation space f ≤ c

/-- PowersetCard is nonempty whenever the requested cardinality fits. -/
axiom powersetCard_nonempty {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : m ≤ S.card) :
    (S.powersetCard m).Nonempty

/-- A generic uniform m-subset has the requested cardinality. -/
axiom mem_powersetCard_card {α : Type*} [DecidableEq α]
    {S R : Finset α} {m : ℕ} (hR : R ∈ S.powersetCard m) :
    R.card = m

/-- Complement monotonicity for logarithms in the positive range used in Section 4. -/
axiom log_card_sdiff_le {α : Type*} [DecidableEq α]
    {S R : Finset α} (hR : R ⊆ S) (hne : (S \ R).Nonempty) :
    Real.log ((S \ R).card : ℝ) ≤ Real.log (S.card : ℝ)

/-- Generic finite-chain reparametrization by complements preserves the uniform law. -/
axiom complement_chain_uniform {α : Type*} [DecidableEq α]
    {k : ℕ} (S : Finset α) (m : Fin k → ℕ)
    (hm : StrictMono m) :
    True

end

end GrahamRearrangement.Section4External
