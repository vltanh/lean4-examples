import Lean4Examples.GrahamRearrangement.BooleanSlice.Definitions
import Lean4Examples.GrahamRearrangement.External

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section3External

/-!
# External sampling/Fourier inputs specialized to the Section 3 model

These are still generic finite-probability or Fourier facts, not results of
Pham--Sauermann.  The paper's Lemmas 3.1--3.7 are proved in subsequent modules.
-/

noncomputable section

axiom balancedPartitions_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedPartitions (p := p) (m := m) S).Nonempty

/-- The balanced-partition/one-choice-per-block sampling experiment is exactly
uniform on size-`m` subsets. -/
axiom sliceMass_eq_partition_average {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z =
      partitionExpectation S (fun P => conditionalSumMass P z)

/-- Every block in a valid balanced partition has the prescribed size. -/
axiom balanced_block_size_bounds {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    S.card / m ≤ (P i).card ∧
      (P i).card ≤ S.card / m + 1

/-- The quantitative block-size estimate used in (3.3). -/
axiom balanced_block_sqrt_two_bound {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    ((P i).card : ℝ) ≤ Real.sqrt 2 * S.card / m

/-- After removing a fixed point, its balanced block still has at least
|S|/(2m) remaining points in the Section 3 range. -/
axiom point_block_remainder_lower {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    S.card / (2 * m) ≤ (pointBlock S P x \ {x}).card

/-- If a subset has density at least 1/4, the block containing a fixed point
misses the expected number of its points only with the hypergeometric tail used
in Lemma 3.1. -/
axiom block_sparse_tail {p m : ℕ} [NeZero p]
    (S G : Finset (ZMod p)) (x : ZMod p)
    (hx : x ∈ S) (hGS : G ⊆ S)
    (hdensity : S.card ≤ 4 * G.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) :
    partitionMass S (fun P =>
      ((pointBlock S P x \\ {x}) ∩ G).card <
        S.card / (16 * m)) ≤
      Real.exp (-(S.card : ℝ) / (64 * m))

/-- If a subset has density at least 3/4, the block containing a fixed point
has fewer than a quarter-block worth of its points only with the tail used in
Lemma 3.3. -/
axiom block_dense_tail {p m : ℕ} [NeZero p]
    (S G : Finset (ZMod p)) (x : ZMod p)
    (hx : x ∈ S) (hGS : G ⊆ S)
    (hdensity : 3 * S.card ≤ 4 * G.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) :
    partitionMass S (fun P =>
      ((pointBlock S P x \\ {x}) ∩ G).card <
        S.card / (4 * m)) ≤
      Real.exp (-(S.card : ℝ) / (48 * m))

/-- Standard finite Fourier estimate for the average of one additive character
over a nonempty block. -/
axiom block_character_decay {p : ℕ} (hp : p.Prime)
    (T : Finset (ZMod p)) (hT : T.Nonempty) (χ : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ≤
      Real.exp (-
        (1 / (T.card : ℝ) ^ 2) *
          ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2)

/-- Fubini for counting a finite family of partition events. -/
axiom partitionExpectation_card_eq_sum_mass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)] :
    partitionExpectation S
        (fun P => ((Finset.univ.filter fun χ => E χ P).card : ℝ)) =
      ∑ χ : ZMod p, partitionMass S (E χ)

/-- Average indicator bound for a deterministic subset of characters. -/
axiom partitionExpectation_filter_le {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (T : Finset (ZMod p))
    (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)]
    (hbound : ∀ χ ∈ T, partitionMass S (E χ) ≤ 1 / (S.card : ℝ) ^ 9) :
    partitionExpectation S
      (fun P => ((T.filter fun χ => E χ P).card : ℝ)) ≤
        (T.card : ℝ) / (S.card : ℝ) ^ 9

/-- Generic double counting over the rows of a partition energy. -/
axiom partition_energy_lower_by_rows {α ι : Type*}
    [Fintype ι] [DecidableEq α]
    (S : Finset α) (P : ι → Finset α)
    (hpartition : (∀ i, P i ⊆ S) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ x, x ∈ S ↔ ∃ i, x ∈ P i))
    (w : α → α → ℝ) (rowLower : α → ℝ)
    (hrow : ∀ i, ∀ x ∈ P i,
      rowLower x ≤ ∑ y ∈ P i, w x y) :
    ∑ i, ∑ x ∈ P i, ∑ y ∈ P i, w x y ≥
      ∑ x ∈ S, rowLower x

/-- Pair-uniform expectation expands into the double average over `S×S`. -/
axiom pair_uniform_expectation {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (f : α → α → ℝ) :
    uniformExpectation (S.product S) (fun q => f q.1 q.2) =
      (1 / (S.card : ℝ) ^ 2) *
        ∑ x ∈ S, ∑ y ∈ S, f x y

/-- Averaging over one coordinate extracts a fixed witness with at least the
global average success probability. -/
axiom exists_fiber_mass_ge_pair_mass {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (E : α → α → Prop)
    [DecidablePred fun q : α × α => E q.1 q.2]
    [∀ y, DecidablePred fun x => E x y] :
    ∃ y ∈ S,
      uniformMass S (fun x => E x y) ≥
        uniformMass (S.product S) (fun q => E q.1 q.2)

/-- The elementary dyadic numerical tail summation used at the end of Theorem 1.3. -/
axiom dyadic_exp_sum_le_two :
    ∑' l : ℕ, Real.exp ((l : ℝ) / 2 - (2 : ℝ) ^ l) ≤ 2

end

end GrahamRearrangement.Section3External
