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

/-- Generic positive-kernel induction for increasing tuples.  This is the
finite Fubini/reindexing identity used by the induction proving (4.1). -/
axiom prefixKernelSum_le_pow (n h : ℕ) (w : ℕ → ℝ) (B : ℝ)
    (hw : ∀ d, 0 ≤ w d)
    (hrow : ∀ a < n,
      (∑ d ∈ Finset.Icc 1 (n - a), w d) ≤ B) :
    prefixKernelSum n h w ≤ B ^ h

/-- Dropping the one cross-order constraint associated with an omitted gap
factorizes the weighted tuple sum into a left and a reversed right prefix sum. -/
axiom omittedKernelSum_le_prefix_mul (n k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, 0 ≤ w d) (j : Fin (k + 1)) :
    omittedKernelSum n k w j ≤
      prefixKernelSum n j.val w *
        prefixKernelSum n (k - j.val) w

end

end GrahamRearrangement.Section4External
