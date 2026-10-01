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

theorem balancedPartitions_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedPartitions (p := p) (m := m) S).Nonempty := by
  refine ⟨canonicalBalancedPartition S hm hmS, ?_⟩
  simp [balancedPartitions, canonicalBalancedPartition_spec S hm hmS]

/-- The balanced-partition/one-choice-per-block sampling experiment is exactly
uniform on size-`m` subsets. -/
axiom sliceMass_eq_partition_average {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z =
      partitionExpectation S (fun P => conditionalSumMass P z)

/-- Every block in a valid balanced partition has the prescribed size. -/
theorem balanced_block_size_bounds {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    S.card / m ≤ (P i).card ∧
      (P i).card ≤ S.card / m + 1 := by
  rw [hP.2.2.2 i]
  unfold balancedBlockSize
  split <;> omega

/-- The quantitative block-size estimate used in (3.3). -/
theorem balanced_block_sqrt_two_bound {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    ((P i).card : ℝ) ≤ Real.sqrt 2 * S.card / m := by
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact Fin.elim0 i
  have hmS : m ≤ S.card := by
    exact le_trans hm4 (Nat.div_le_self _ _)
  have hb := balanced_block_size_bounds S hm hmS hP i
  have hfloor :
      (S.card / m : ℕ) ≤ (S.card : ℝ) / m := by
    exact_mod_cast Nat.div_le_iff_le_mul (by omega) |>.2
      (Nat.sub_lt_iff_lt_add.mp (Nat.mod_lt S.card hm))
  have hratio : (4 : ℝ) ≤ (S.card : ℝ) / m := by
    have hm4' : 4 * m ≤ S.card := by
      exact (Nat.le_div_iff_mul_le (by omega)).mp hm4
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < m)).2
      (by exact_mod_cast hm4')
  have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    have hs0 := Real.sqrt_nonneg 2
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith
  have hcard :
      ((P i).card : ℝ) ≤ (S.card : ℝ) / m + 1 := by
    exact_mod_cast hb.2
    nlinarith
  nlinarith

/-- After removing a fixed point, its balanced block still has at least
|S|/(2m) remaining points in the Section 3 range. -/
theorem point_block_remainder_lower {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    S.card / (2 * m) ≤ (pointBlock S P x \ {x}).card := by
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hmem : x ∈ pointBlock S P x :=
    mem_blockIndex S P x hm hP hx
  have hcardBlock :=
    (balanced_block_size_bounds S hm hmS hP (blockIndex S P x)).1
  have hcardErase :
      (pointBlock S P x \ {x}).card =
        (pointBlock S P x).card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hmem]
  rw [hcardErase]
  have hq4 : 4 ≤ S.card / m := by
    apply (Nat.le_div_iff_mul_le hm).2
    have hm4' : 4 * m ≤ S.card :=
      (Nat.le_div_iff_mul_le (by omega)).mp hm4
    simpa [mul_comm] using hm4'
  have hhalf :
      S.card / (2 * m) ≤ (S.card / m) / 2 := by
    exact Nat.div_le_div_right
      (Nat.le_of_eq (by omega : 2 * m = m * 2))
  omega

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

/-- Fubini for counting a finite family of partition events. -/
theorem partitionExpectation_card_eq_sum_mass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)] :
    partitionExpectation S
        (fun P => ((Finset.univ.filter fun χ => E χ P).card : ℝ)) =
      ∑ χ : ZMod p, partitionMass S (E χ) := by
  classical
  unfold partitionExpectation partitionMass uniformExpectation uniformMass
  rw [Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  norm_cast
  exact Finset.card_bij
    (fun P _ => P)
    (by intro P hP; simpa using hP)
    (by intro P hP Q hQ h; exact h)
    (by intro P hP; exact ⟨P, by simpa using hP, rfl⟩)

/-- Average indicator bound for a deterministic subset of characters. -/
theorem partitionExpectation_filter_le {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (T : Finset (ZMod p))
    (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)]
    (hbound : ∀ χ ∈ T, partitionMass S (E χ) ≤ 1 / (S.card : ℝ) ^ 9) :
    partitionExpectation S
      (fun P => ((T.filter fun χ => E χ P).card : ℝ)) ≤
        (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
  classical
  unfold partitionExpectation
  have hrewrite :
      uniformExpectation (balancedPartitions S)
          (fun P => ((T.filter fun χ => E χ P).card : ℝ)) =
        ∑ χ ∈ T, partitionMass S (E χ) := by
    unfold uniformExpectation partitionMass uniformMass
    rw [Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    rfl
  rw [hrewrite]
  calc
    ∑ χ ∈ T, partitionMass S (E χ)
      ≤ ∑ _χ ∈ T, 1 / (S.card : ℝ) ^ 9 := by
          gcongr with χ hχ
          exact hbound χ hχ
    _ = (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
          simp [div_eq_mul_inv, mul_comm]

/-- Generic double counting over the rows of a partition energy. -/
theorem partition_energy_lower_by_rows {α ι : Type*}
    [Fintype ι] [DecidableEq α]
    (S : Finset α) (P : ι → Finset α)
    (hpartition : (∀ i, P i ⊆ S) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ x, x ∈ S ↔ ∃ i, x ∈ P i))
    (w : α → α → ℝ) (rowLower : α → ℝ)
    (hrow : ∀ i, ∀ x ∈ P i,
      rowLower x ≤ ∑ y ∈ P i, w x y) :
    ∑ i, ∑ x ∈ P i, ∑ y ∈ P i, w x y ≥
      ∑ x ∈ S, rowLower x := by
  classical
  have hsum :
      ∑ i, ∑ x ∈ P i, rowLower x =
        ∑ x ∈ S, rowLower x := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext x
      simp [hpartition.2.2 x]
    · intro i hi j hj hij
      exact hpartition.2.1 i j hij
  rw [← hsum]
  gcongr with i hi x hx
  exact hrow i x hx

/-- Pair-uniform expectation expands into the double average over `S×S`. -/
theorem pair_uniform_expectation {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (f : α → α → ℝ) :
    uniformExpectation (S.product S) (fun q => f q.1 q.2) =
      (1 / (S.card : ℝ) ^ 2) *
        ∑ x ∈ S, ∑ y ∈ S, f x y := by
  unfold uniformExpectation
  rw [Finset.sum_product, Finset.card_product]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  field_simp
  ring

/-- Averaging over one coordinate extracts a fixed witness with at least the
global average success probability. -/
theorem exists_fiber_mass_ge_pair_mass {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (E : α → α → Prop)
    [DecidablePred fun q : α × α => E q.1 q.2]
    [∀ y, DecidablePred fun x => E x y] :
    ∃ y ∈ S,
      uniformMass S (fun x => E x y) ≥
        uniformMass (S.product S) (fun q => E q.1 q.2) := by
  classical
  have havg :
      uniformMass (S.product S) (fun q => E q.1 q.2) =
        uniformExpectation S (fun y => uniformMass S (fun x => E x y)) := by
    unfold uniformMass uniformExpectation
    rw [Finset.card_product]
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    field_simp
    rw [Finset.sum_comm]
    ring
  rw [havg]
  by_contra h
  push_neg at h
  have hlt :
      uniformExpectation S (fun y => uniformMass S (fun x => E x y)) <
        uniformExpectation S
          (fun _ => uniformExpectation S
            (fun y => uniformMass S (fun x => E x y))) := by
    apply uniformExpectation_strictMono hS
    intro y hy
    exact h y hy
  rw [uniformExpectation_const S hS] at hlt
  exact lt_irrefl _ hlt

/-- The elementary dyadic numerical tail summation used at the end of Theorem 1.3. -/
axiom dyadic_exp_sum_le_two :
    ∑' l : ℕ, Real.exp ((l : ℝ) / 2 - (2 : ℝ) ^ l) ≤ 2

end

end GrahamRearrangement.Section3External
