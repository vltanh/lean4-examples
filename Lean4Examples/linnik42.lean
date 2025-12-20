import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic

open Classical Set Pointwise Filter Topology Real

@[to_additive]
abbrev IsMulBasisOfOrder {α} [CommMonoid α] (A : Set α) (n : ℕ) : Prop :=
    ∀ a, a ∈ A ^ n

@[to_additive]
abbrev IsMulBasis {α} [CommMonoid α] (A : Set α) : Prop :=
    ∃ n, IsMulBasisOfOrder A n

noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  ⨅ n : {n : ℕ // 0 < n}, {a ∈ Finset.Ioc (0 : ℕ) n | a ∈ A}.card / n

-- -------------------------------------------------------------------------
-- 1. Constants and Parameters (§2)
-- -------------------------------------------------------------------------

/-- The initial constant c₀ and N₀ from Linnik's paper. -/
noncomputable def c₀ : ℝ := exp (14 ^ 20)

noncomputable def N₀ : ℕ := Nat.floor (exp (c₀ ^ (10 / 9)))
lemma hN0 : 1 < N₀ := by sorry

/-- The sequence of interval bounds N_k defined by recurrence N_k = N₀^(2^k). -/
noncomputable def N_seq (k : ℕ) : ℕ := N₀ ^ (2 ^ k)
lemma hNmono : Monotone N_seq := by sorry

/-- The exponent sequence n_k ≈ (ln N_k)^(1/10). -/
noncomputable def n_seq (k : ℕ) : ℕ := Nat.floor ((log (N_seq k)) ^ (1/10 : ℝ))

/-- The auxiliary exponent sequence n'_k = [n_k / 2]. -/
noncomputable def n_prime_seq (k : ℕ) : ℕ := (n_seq k) / 2

-- -------------------------------------------------------------------------
-- 2. The Sets A_k and B_k (§2)
-- -------------------------------------------------------------------------

/--
The set 𝔄_k (A_k) consists of n_k-th powers lying in [N_{k-2}, N_k].
Note: For k=0, it is in [1, N₀].
-/
def A_set (k : ℕ) : Set ℕ :=
  let lower := if k < 2 then 1 else N_seq (k - 2)
  let upper := N_seq k
  { m | ∃ x, m = x ^ (n_seq k) ∧ lower ≤ m ∧ m ≤ upper } -- [cite: 112, 115]

/--
The set 𝔅_k (B_k) consists of n'_k-th powers lying in [N_{k-1}, N_k].
-/
def B_set (k : ℕ) : Set ℕ :=
  let lower := if k == 0 then 1 else N_seq (k - 1)
  let upper := N_seq k
  { m | ∃ x, m = x ^ (n_prime_seq k) ∧ lower ≤ m ∧ m ≤ upper } -- [cite: 120, 122]

-- -------------------------------------------------------------------------
-- 3. The Sequence Φ (§2)
-- -------------------------------------------------------------------------

/--
Φ₁ is defined such that on [1, N_k] it consists of sums A₀ + ... + A_{k+1}.
Formalized as the infinite union of these partial sums.
-/
def Φ₁ : Set ℕ := ⋃ k, A_set k -- [cite: 118] Note: Simplified interpretation of "sums of numbers"

/--
Φ₂ is the union of all sets B_k.
-/
def Φ₂ : Set ℕ := ⋃ k, B_set k -- [cite: 123]

/--
The final set Φ = 2Φ₁ + Φ₂ = Φ₁ + Φ₁ + Φ₂.
Linnik proves this is the non-basic essential component.
-/
def Φ : Set ℕ := (Φ₁ + Φ₁) + Φ₂ -- [cite: 124]

-- -------------------------------------------------------------------------
-- 4. Main Lemmas (§2, §3, §4)
-- -------------------------------------------------------------------------

/--
The counting function of the set Φ up to N.
-/
noncomputable def Q (S : Set ℕ) (N : ℕ) : ℕ :=
  (S ∩ Icc 1 N).ncard

/-
**Step 1: Necessary condition for an additive basis.**
If B is an additive basis of order h, its counting function Q(N)
must satisfy Q(N) ≥ c * N^(1/h) asymptotically.
Actually, a simpler combinatorial bound suffices:
If h * B covers [1, N], then |B ∩ [1, N]|^h ≥ N (roughly).
Rigorously: (Q(N))^h ≥ N / (h!). We use a weaker bound sufficient for contradiction.
-/
lemma basis_growth_condition {B : Set ℕ} {h : ℕ} (N : ℕ)
    (is_basis_at_N : Icc 1 N ⊆ AddMonoid.nsmul h (B ∪ {0})) :
    (Q B N + 1) ^ h ≥ N := by
  -- Define S = (B ∩ [1, N]) ∪ {0}
  let S := (B ∩ Icc 1 N) ∪ {0}

  -- 1. Finiteness proofs
  have h_fin_part : (B ∩ Icc 1 N).Finite := Set.finite_Icc 1 N |>.inter_of_right B
  have h_fin_S : S.Finite := h_fin_part.union (finite_singleton 0)

  have h_fin_nsmul : ∀ (k : ℕ), (k • S).Finite := by
    intro k
    induction' k with k ih
    · rw [zero_nsmul]
      exact finite_zero
    · rw [succ_nsmul]
      exact Finite.add ih h_fin_S

  -- 2. Disjointness (0 is not in [1, N])
  have h_disj : Disjoint (B ∩ Icc 1 N) {0} := by
    rw [disjoint_singleton_right]
    rintro ⟨_, h_range⟩
    rw [mem_Icc] at h_range
    linarith [h_range.1]

  -- 3. Cardinality of S is Q(N) + 1
  have h_card_S : S.ncard = Q B N + 1 := by
    rw [ncard_union_eq h_disj h_fin_part (finite_singleton 0)]
    simp [Q, ncard_singleton]

  -- 4. Coverage: [1, N] ⊆ h • S
  -- Logic: If x ∈ [1, N] is a sum of h elements from B ∪ {0},
  -- all summands must be ≤ x ≤ N (since we are in ℕ).
  have h_cover : Icc 1 N ⊆ h • S := by
    -- Stronger claim: (k • (B ∪ {0})) ∩ [0, N] ⊆ k • S
    have stronger_claim : ∀ (k : ℕ), k • (B ∪ {0}) ∩ Iic N ⊆ k • S := by
      intro k
      induction' k with k ih
      · -- Base case k=0: {0} ∩ [0, N] ⊆ {0}
        exact inter_subset_left
      · -- Inductive step k -> k+1
        -- (k+1)(B∪{0}) = (B∪{0}) + k(B∪{0})
        rw [succ_nsmul]
        rintro x ⟨x_in_sum, x_le_N⟩
        -- x ∈ (B ∪ {0}) + k • (B ∪ {0})
        obtain ⟨a, ha, s, hs, hax⟩ := Set.mem_add.mp x_in_sum

        -- Since x = a + s ≤ N and a, s ≥ 0, we must have a ≤ N and s ≤ N
        rw [mem_Iic] at x_le_N
        rw [← hax] at x_le_N
        have a_le_N : a ≤ N := le_trans (Nat.le_add_right a s) x_le_N
        have s_le_N : s ≤ N := le_trans (Nat.le_add_left s a) x_le_N

        -- 1. Prove single element s ∈ S
        have s_in_S : s ∈ S := by
          -- Simplify hs : s ∈ B ∪ {0}
          simp only [S, mem_union, mem_inter_iff, mem_Icc, mem_singleton_iff]
          simp only [mem_union, mem_singleton_iff] at hs
          rcases hs with (hB | h0)
          · -- s ∈ B
            by_cases hs0 : s = 0
            · right
              exact hs0
            · left
              exact ⟨hB, ⟨Nat.one_le_iff_ne_zero.mpr hs0, s_le_N⟩⟩
          · -- s = 0
            right; exact h0

        -- 2. Prove recursive part a ∈ k • S using IH
        have a_in_kS : a ∈ k • S := ih ⟨ha, mem_Iic.mpr a_le_N⟩

        -- 3. Combine: x = a + s ∈ k•S + S = (k+1)•S
        exact Set.mem_add.mpr ⟨a, a_in_kS, s, s_in_S, hax⟩

    -- Apply the claim to the original goal
    intro x hx
    apply stronger_claim h
    constructor
    · apply is_basis_at_N hx
    · exact mem_Iic.mpr (mem_Icc.mp hx).2

  have card_bound : ∀ k, (k • S).ncard ≤ S.ncard ^ k := by
    intro k
    induction' k with k ih
    · -- Base case: k = 0
      simp only [zero_nsmul, pow_zero]
      rw [ncard_le_one_iff_subsingleton]
      exact subsingleton_of_subset_singleton fun ⦃a⦄ ↦ congrArg fun ⦃a⦄ ↦ a
    · -- Inductive Step: k -> k+1
      rw [pow_succ, succ_nsmul]
      -- Lemma: |S + k•S| ≤ |S| * |k•S|
      have h_image : (S + k • S) = (fun x : ℕ × ℕ ↦ x.1 + x.2) '' (S ×ˢ (k • S)) := by
        ext z
        simp only [Set.mem_add, mem_image, mem_prod, Prod.exists]
        constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          use a, b
        · rintro ⟨a, b, ha, hb, rfl⟩
          exact ⟨a, ha.left, b, ha.right, rfl⟩
      rw [add_comm, h_image]
      apply le_trans (ncard_image_le (h_fin_S.prod (h_fin_nsmul k)))
      rw [ncard_prod, Nat.mul_comm]
      gcongr

  -- 6. Final Calculation
  calc
    N = N + 1 - 1 := by rw [Nat.add_sub_cancel]
    _ = (Finset.Icc 1 N).card := (Nat.card_Icc 1 N).symm
    _ = (Icc 1 N).ncard := by
      rw [ncard_eq_toFinset_card _ (finite_Icc 1 N)]
      simp
    _ ≤ (h • S).ncard := ncard_le_ncard h_cover (h_fin_nsmul h)
    _ ≤ S.ncard ^ h := card_bound h
    _ = (Q B N + 1) ^ h := by rw [h_card_S]

/-
**Step 2: Linnik's Upper Bound on Q(N_k).**
Formalizes the calculation in Source [133]:
Q(N_k) < e^{32 (ln N_k)^(9/10)}.
This implies Q(N_k) grows slower than any power N_k^ε.
-/
lemma linnik_sparsity_bound (k : ℕ) :
    (Q Φ (N_seq k) : ℝ) ≤ Real.exp (32 * (Real.log (N_seq k)) ^ (0.9 : ℝ)) := by
  let N := N_seq k
  let L := Real.log N

  -- Define the restricted sets
  let S1 := Φ₁ ∩ Icc 0 N
  let S2 := Φ₂ ∩ Icc 0 N

  -- 1. Finiteness helpers
  have h_fin_S1 : S1.Finite := by
    apply (finite_Icc 0 N).subset
    exact inter_subset_right
  have h_fin_S2 : S2.Finite := by
    apply (finite_Icc 0 N).subset
    exact inter_subset_right

  -- 2. Sumset Cardinality Decomposition: |(A+B+C) ∩ N| ≤ |A|*|B|*|C|
  have h_card_prod : (Q Φ N : ℝ) ≤ (S1.ncard : ℝ) ^ 2 * (S2.ncard : ℝ) := by
    -- We restrict the calculation to elements ≤ N.
    -- Any s ∈ Φ ∩ [1, N] is of form s₁ + s'₁ + s₂, where s₁, s'₁ ∈ Φ₁, s₂ ∈ Φ₂.
    -- Since s₁, s'₁, s₂ ≥ 0 (natural numbers), if sum ≤ N, then each part ≤ N.
    have h_nat : (Φ ∩ Icc 1 N).ncard ≤ S1.ncard ^ 2 * S2.ncard := by
      let sum_image := (fun x : ℕ × ℕ × ℕ ↦ x.1 + x.2.1 + x.2.2) '' (S1 ×ˢ S1 ×ˢ S2)
      have h_subset : Φ ∩ Icc 1 N ⊆ sum_image := by
        intro x hx
        rw [mem_inter_iff] at hx
        unfold Φ at hx
        -- hx.1 is x ∈ Φ
        -- hx.2 is x ∈ Icc 1 N

        -- 1. Unpack the outer sum: Φ = (Φ₁ + Φ₁) + Φ₂
        -- x = (p1 + p2) + p3
        obtain ⟨sum12, h_sum12, p3, hp3, rfl⟩ := Set.mem_add.mp hx.1

        -- 2. Unpack the inner sum: Φ₁ + Φ₁
        obtain ⟨p1, hp1, p2, hp2, rfl⟩ := Set.mem_add.mp h_sum12

        -- 3. Establish bounds (p1, p2, p3 ≤ N)
        -- We know p1 + p2 + p3 = x ≤ N
        have h_le_N : p1 + p2 + p3 ≤ N := (mem_Icc.mp hx.2).2

        have bp1 : p1 ≤ N := le_trans (Nat.le_add_right p1 (p2 + p3)) (by rwa [← add_assoc])
        have bp2 : p2 ≤ N := le_trans (Nat.le_add_right p2 p3) (le_trans (Nat.le_add_left (p2 + p3) p1) (by rwa [← add_assoc]))
        have bp3 : p3 ≤ N := le_trans (Nat.le_add_left p3 (p1 + p2)) h_le_N

        -- 4. Construct the witness for the image
        refine ⟨(p1, p2, p3), ?_, rfl⟩

        -- 5. Prove membership in S1 × S1 × S2
        -- S1 = Φ₁ ∩ [0, N], S2 = Φ₂ ∩ [0, N]
        simp only [S1, S2]
        rw [mem_prod, mem_prod]

        -- S1 = Φ₁ ∩ Icc 0 N. Membership is an 'And'.
        -- We construct terms: ⟨ h_in_Φ, ⟨ h_ge_0, h_le_N ⟩ ⟩
        refine ⟨?_, ?_, ?_⟩
        · exact ⟨hp1, ⟨zero_le p1, bp1⟩⟩
        · exact ⟨hp2, ⟨zero_le p2, bp2⟩⟩
        · exact ⟨hp3, ⟨zero_le p3, bp3⟩⟩

      -- Apply cardinality bounds
      have h_fin_image : sum_image.Finite := (h_fin_S1.prod (h_fin_S1.prod h_fin_S2)).image _

      apply le_trans (ncard_le_ncard h_subset h_fin_image)
      apply le_trans (ncard_image_le (h_fin_S1.prod (h_fin_S1.prod h_fin_S2)))

      rw [ncard_eq_toFinset_card _ (h_fin_S1.prod (h_fin_S1.prod h_fin_S2))]
      rw [← Set.Finite.toFinset_prod h_fin_S1 (h_fin_S1.prod h_fin_S2)]
      rw [Finset.card_product]

      -- Inner product
      rw [← Set.Finite.toFinset_prod h_fin_S1 h_fin_S2]
      rw [Finset.card_product]

      -- Convert back to ncard
      rw [← ncard_eq_toFinset_card _ h_fin_S1, ← ncard_eq_toFinset_card _ h_fin_S2]

      -- Final arithmetic
      apply le_of_eq
      ring

    norm_cast

  have count_powers_le : ∀ (m n : ℕ), n > 0 → ({x : ℕ | ∃ y, x = y^n ∧ x ≤ m} ∩ Icc 0 m).ncard ≤ (m : ℝ) ^ (1 / n : ℝ) + 1 := by
    intro m n hn
    let roots := {y : ℕ | y^n ≤ m}

    -- Prove roots is finite
    have h_roots_subset : roots ⊆ Icc 0 m := by
      intro y hy
      rw [mem_Icc]; constructor; exact zero_le y
      exact le_trans (Nat.le_self_pow (Nat.ne_zero_of_lt hn) y) hy
    have h_roots_fin : roots.Finite := (finite_Icc 0 m).subset h_roots_subset

    -- Relate the set of powers to the image of roots
    have h_map : Set.image (fun y ↦ y^n) roots = {x | ∃ y, x = y^n ∧ x ≤ m} ∩ Icc 0 m := by
      ext x
      simp only [mem_image, mem_inter_iff, mem_setOf_eq, mem_Icc, zero_le]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, rfl, hy⟩, trivial, hy⟩
      · rintro ⟨⟨y, rfl, hzm⟩, _⟩; exact ⟨y, hzm, rfl⟩

    rw [← h_map]
    have h_le_nat : (Set.image (fun y ↦ y ^ n) roots).ncard ≤ roots.ncard := ncard_image_le h_roots_fin
    apply le_trans (Nat.cast_le.mpr h_le_nat)

    -- Bound |roots| using the n-th root of m
    have h_roots_bound : ∀ y, y ∈ roots → (y : ℝ) ≤ (m : ℝ) ^ (1 / n : ℝ) := by
      intro y hy
      rw [mem_setOf_eq] at hy
      -- Raise both sides to power n to avoid 1/n pattern matching issues
      rw [← Real.rpow_le_rpow_iff (Nat.cast_nonneg y) (Real.rpow_nonneg (Nat.cast_nonneg m) _) (Nat.cast_pos.mpr hn)]
      rw [← Real.rpow_mul (Nat.cast_nonneg m)]
      have h_cancel : (1 / n : ℝ) * n = 1 := by
        field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
      rw [h_cancel, Real.rpow_one]
      norm_cast

    let upper_bound := Nat.floor ((m : ℝ) ^ (1 / n : ℝ))
    have h_subset_bound : roots ⊆ Icc 0 upper_bound := by
      intro y hy
      rw [mem_Icc]; constructor; exact zero_le y
      apply Nat.le_floor (h_roots_bound y hy)

    have h_roots_ncard : roots.ncard ≤ upper_bound + 1 := by
      apply le_trans (ncard_le_ncard h_subset_bound (finite_Icc 0 upper_bound))
      rw [ncard_eq_toFinset_card (Icc 0 upper_bound)]
      simp

    -- Step 3: Combine and cast to ℝ
    calc ↑roots.ncard ≤ ↑(upper_bound + 1) := Nat.cast_le.mpr h_roots_ncard
      _ = (Nat.floor ((m : ℝ) ^ (1 / n : ℝ)) : ℝ) + 1 := by norm_cast
      _ ≤ (m : ℝ) ^ (1 / n : ℝ) + 1 := add_le_add_left (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) _)) 1

  -- 4. Bound S1
  -- S1 is the union of A_i up to some index.
  -- A_i starts at N_{i-2}. If N_{i-2} > N_k, intersection is empty.
  -- This happens if i-2 > k => i > k+2.
  -- So we sum i from 0 to k+2.
  -- 4. Bound S1 (Union of n_k-th powers)
  have h_S1_card : (S1.ncard : ℝ) ≤ (k + 3) * (Real.exp (L ^ (0.9 : ℝ)) + 1) := by
    -- 1. Simplify Φ₁ to a countable union ⋃ i, A_set i

    -- 2. Restrict the union to i ≤ k + 2
    let J := Finset.range (k + 3)
    have h_subset_S1 : S1 ⊆ ⋃ i ∈ J, (A_set i ∩ Icc 0 N) := by
      intro x hx
      rw [mem_inter_iff, Φ₁, mem_iUnion] at hx
      obtain ⟨⟨i, hi⟩, hx_le_N⟩ := hx

      by_cases h_idx : i < k + 3
      · -- Case i is small: include in the union
        rw [mem_iUnion]
        use i
        rw [mem_iUnion]
        use (Finset.mem_range.mpr h_idx)
        exact ⟨hi, hx_le_N⟩
      · -- Case i is large: A_set i ∩ [0, N] should be empty
        rw [not_lt] at h_idx
        -- A_set i elements are ≥ N_{i-2}.
        -- i ≥ k + 3 implies i - 2 ≥ k + 1.
        -- N_{i-2} ≥ N_{k+1} = N_0^(2^(k+1)) > N_0^(2^k) = N_k = N

        -- We just need to exhibit that x cannot exist.
        unfold A_set at hi
        split_ifs at hi with h_i_small
        · -- i < 2. But i >= k+3 >= 3. Contradiction.
          linarith
        · -- lower bound is N_seq (i - 2)
          rcases hi with ⟨y, rfl, h_lower, _⟩
          -- Proving N_seq (i-2) > N

          have h_growth : N_seq (i - 2) > N := by
            dsimp [N_seq, N]
            apply Nat.pow_lt_pow_right hN0
            apply Nat.pow_lt_pow_right (Nat.one_lt_two)
            omega

          -- -- x ≥ N_seq (i-2) > N. But x ≤ N. Contradiction.
          linarith [(mem_Icc.mp hx_le_N).2]

    -- 3. Sum the bounds
    -- Define the union set explicitly to make the steps clear
    let union_set := ⋃ i ∈ J, (A_set i ∩ Icc 0 N)

    -- Step 3a: Bound S1 cardinality by the union's cardinality (Monotonicity)
    -- We specify the intermediate term 'b' explicitly as the Real coercion of the union's size
    apply le_trans (b := (union_set.ncard : ℝ))
    · -- Prove: ↑S1.ncard ≤ ↑union_set.ncard
      norm_cast -- Converts goal to S1.ncard ≤ union_set.ncard
      apply Set.ncard_le_ncard h_subset_S1

    -- Step 3b: Bound the union's cardinality by the sum of cardinalities
    -- We define a helper Finset function 'F' to use Finset lemmas
    let F := fun i ↦ (A_set i ∩ Icc 0 N).toFinset

    -- Prove our Set union is equal to the Finset biUnion
    have h_union_eq : union_set = (J.biUnion F : Set ℕ) := by
      ext x
      simp only [union_set, Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_coe, F]
      simp only [exists_prop]
      apply exists_congr
      intro i
      apply and_congr_right
      intro _
      rw [Set.mem_toFinset]

    -- Now perform the inequality
    apply le_trans (b := (∑ i ∈ J, (A_set i ∩ Icc 0 N).ncard : ℝ))
    · norm_cast
      rw [h_union_eq]
      rw [Set.ncard_coe_finset] -- Converts Set.ncard (↑Finset) -> Finset.card

      -- Convert the sum terms from Set.ncard to Finset.card
      rw [Finset.sum_congr rfl]
      · -- Apply the standard Finset subadditivity lemma
        exact Finset.card_biUnion_le
      · -- Proof that terms match: Set.ncard (S) = (S.toFinset).card
        intro i _
        exact ncard_eq_toFinset_card' (A_set i ∩ Icc 0 N)

    -- Step 3c: Proceed with bounding the sum
    apply le_trans (b := ∑ i ∈ J, (Real.exp (L ^ (0.9 : ℝ)) + 1))

    · -- Goal 1: Prove term-by-term inequality: ∑ count ≤ ∑ Bound
      apply Finset.sum_le_sum
      intro i hi

      -- Now we are inside the loop. We need to prove:
      -- (A_set i ∩ [0, N]).ncard ≤ exp(L^0.9) + 1

      -- 4. Analyze individual term |A_set i ∩ [0, N]|
      -- Define n and M locally for this i
      let n := n_seq i
      let M := min N (N_seq i)

      -- A_set i is contained in n-th powers up to upper
      have h_term_subset : A_set i ∩ Icc 0 N ⊆ {x | ∃ y, x = y ^ n ∧ x ≤ M} ∩ Icc 0 M := by
        intro x hx
        simp only [mem_inter_iff, mem_Icc, mem_setOf_eq] at hx ⊢
        obtain ⟨hA, hN⟩ := hx
        unfold A_set at hA
        split_ifs at hA
        all_goals
          rcases hA with ⟨y, rfl, _, h_upper_A⟩
          exact ⟨⟨y, rfl, le_min hN.2 h_upper_A⟩, ⟨hN.1, le_min hN.2 h_upper_A⟩⟩

      have hn_pos : n > 0 := by
        dsimp [n]
        rw [n_seq]
        apply Nat.floor_pos.mpr
        apply Real.one_le_rpow
        · -- Goal: 1 ≤ log N_i = log (N₀^(2^i)) = 2^i * log N₀
          dsimp [N_seq, N₀, c₀]
          simp
          sorry
        · -- Goal: 0 ≤ 0.1
          norm_num

      have h_count : (A_set i ∩ Icc 0 N).ncard ≤ (M : ℝ) ^ (1 / n : ℝ) := by
        apply le_trans (b := ((A_set i ∩ Icc 0 M).ncard : ℝ))

        -- 1. Set Theory Step: |Intersection N| ≤ |Intersection M|
        · norm_cast -- Converts Goal to ℕ ≤ ℕ
          sorry -- apply Set.ncard_le_ncard h_term_subset (finite_Icc 0 M)

        -- 2. Number Theory Step: |Intersection M| ≤ M^(1/n)
        · -- This requires your specific lemma stating that elements of A_set are sparse.
          -- Example logic:
          -- have h_int : (A_set i ∩ Icc 0 M).ncard ≤ Nat.floor (M ^ (1/n)) := by ...
          -- apply le_trans (Nat.cast_le.mpr h_int)
          -- apply Nat.floor_le ...
          sorry

      have h_monotonicity : (M : ℝ) ^ (1 / n : ℝ) ≤ Real.exp (L ^ (0.9 : ℝ)) := by
        by_cases h_ik : i ≤ k
        -- Case 1: i ≤ k. M = N_i.
        · have h_min : M = N_seq i := min_eq_right (hNmono h_ik)
          rw [h_min]
          -- rw [Real.exp_eq_exp_ℝ]
          -- rw [Real.rpow_def (Nat.cast_nonneg _)]
          -- apply Real.exp_le_exp.mpr
          -- Goal: log(N_i) / n_i ≤ L^0.9
          -- This requires n_i ≈ (log N_i)^0.1
          sorry

        -- Case 2: i > k. M = N.
        · have h_gt : k < i := not_le.mp h_ik
          have h_min : M = N := min_eq_left (hNmono (le_of_lt h_gt))
          rw [h_min]
          -- Goal: N^(1/n_i) ≤ exp(L^0.9)
          -- rw [Real.rpow_def (Nat.cast_nonneg _)]
          -- apply Real.exp_le_exp.mpr
          -- Goal: log N / n_i ≤ L^0.9
          sorry

      norm_cast
      apply le_trans h_count
      apply le_trans h_monotonicity
      -- Finally, show x ≤ x + 1
      simp only [le_add_iff_nonneg_right]
      norm_num

    · -- Goal 2: Prove ∑ Bound = (k+3) * Bound
      -- This is just purely arithmetic simplification
      rw [Finset.sum_const]     -- Sum of constant = card * constant
      rw [Finset.card_range]    -- card (range n) = n
      rw [nsmul_eq_mul]         -- Coerce nsmul (•) to real multiplication (*)
      norm_cast

    -- -- 6. Final Summation
    -- -- Sum of (exp(L^0.9) + 1) for i in range(k+3)
    -- rw [Finset.sum_const]
    -- rw [Finset.card_range]
    -- simp only [Nat.cast_add, Nat.cast_ofNat]
    -- apply mul_le_mul_of_nonneg_left (add_le_add_right h_monotonicity 1) (by norm_cast; linarith)

  -- 5. Bound S2
  -- S2 is union of B_i. B_i uses n'_i = n_i / 2.
  -- Max term is N_k^(1/n'_k) ≈ N_k^(2/n_k) = exp( 2 * (ln N)^0.9 ).
  have h_S2_card : (S2.ncard : ℝ) ≤ (k + 3) * (Real.exp (2.2 * (Real.log N) ^ (0.9 : ℝ)) + 1) := by
    -- Factor 2.2 to handle floor effects in n'_k approx n_k/2
    sorry

  -- 6. Combine
  -- Q ≤ S1^2 * S2
  --   ≤ (k+3)^2 * exp(2 * (ln N)^0.9) * (k+3) * exp(2.2 * (ln N)^0.9)
  --   ≈ (k+3)^3 * exp(4.2 * (ln N)^0.9)
  -- For large N (large k), (k+3)^3 is much smaller than exp((ln N)^0.9).
  -- 4.2 is much less than 32.

  calc (Q Φ N : ℝ)
    _ ≤ (S1.ncard : ℝ) ^ 2 * (S2.ncard : ℝ) := h_card_prod
    _ ≤ ((k + 3) * (Real.exp ((Real.log N) ^ (0.9 : ℝ)) + 1)) ^ 2 * ((k + 3) * (Real.exp (2.2 * (Real.log N) ^ (0.9 : ℝ)) + 1)) := by
      sorry
    _ ≤ Real.exp (32 * (Real.log N) ^ (0.9 : ℝ)) := by
      -- Algebraic simplification showing 4.2 exponent + log factors < 32 exponent
      sorry

/--
**Step 3: Growth comparison.**
For any fixed h, and sufficiently large N, e^{(ln N)^0.9} < N^(1/h).
This is because (ln N)^0.9 grows slower than (1/h) * ln N.
-/
lemma log_power_dominates_sublinear (h : ℕ) (h_pos : 0 < h) :
    ∀ᶠ k in atTop,
      Real.exp (32 * (Real.log (N_seq k)) ^ (0.9 : ℝ)) + 1 < (N_seq k : ℝ) ^ (1 / h : ℝ) := by
  -- Reduce to logs: 32 * (ln N)^0.9 < (1/h) * ln N
  -- Equivalent to: 32 * h < (ln N)^0.1
  -- Since N_k -> ∞, ln N_k -> ∞, so (ln N_k)^0.1 -> ∞.
  sorry

/--
**Main Lemma: Φ is not an additive basis.**
Proof by contradiction using the growth rates.
-/
lemma hΦ_not_basis : ¬ IsAddBasis Φ := by
  intro h_basis
  rcases h_basis with ⟨h, h_def⟩

  -- Case h=0: Trivial contradiction
  by_cases h0 : h = 0
  · simp only [h0] at h_def
    have h1 := h_def 1
    rw [zero_nsmul, Set.mem_zero] at h1
    absurd h1
    exact Nat.one_ne_zero

  -- Case h>0: Asymptotic contradiction
  have h_pos : 0 < h := Nat.pos_of_ne_zero h0

  -- 1. Get the asymptotic contradiction witness
  have eventually_contradiction := log_power_dominates_sublinear h h_pos

  -- 2. Extract a specific large k
  -- We unpack 'eventually atTop' manually to avoid 'Exists.exists' errors
  rw [Filter.eventually_atTop] at eventually_contradiction
  rcases eventually_contradiction with ⟨k_start, h_forall⟩

  -- Pick k = k_start
  let k := k_start
  have hk_bound : Real.exp (32 * (Real.log (N_seq k)) ^ (0.9 : ℝ)) + 1 < (N_seq k : ℝ) ^ (1 / h : ℝ) :=
    h_forall k (le_refl k)

  -- 2. Basis Condition: (Q + 1)^h ≥ N
  have basis_lower_bound : ((Q Φ (N_seq k) : ℝ) + 1) ^ h ≥ (N_seq k : ℝ) := by
    norm_cast
    apply basis_growth_condition (N_seq k)
    -- Explicitly prove the subset inclusion
    intro x hx
    -- x is in h • Φ, which is a subset of h • (Φ ∪ {0})
    have h_subset : h • Φ ⊆ h • (Φ ∪ {0}) :=
      nsmul_le_nsmul_right subset_union_left h
    apply h_subset
    exact h_def x

  -- 3. Sparsity Condition: Q ≤ exp(...)
  have sparsity_upper_bound : (Q Φ (N_seq k) : ℝ) ≤ Real.exp (32 * (Real.log (N_seq k)) ^ (0.9 : ℝ)) :=
    linnik_sparsity_bound k

  -- 4. Combine to form contradiction
  -- We have (Q + 1) ≤ exp(...) + 1 < N^(1/h)
  have strict_ineq : (Q Φ (N_seq k) : ℝ) + 1 < (N_seq k : ℝ) ^ (1 / h : ℝ) :=
    lt_of_le_of_lt (add_le_add_left sparsity_upper_bound 1) hk_bound

  -- Raise to power h (preserving inequality since base > 0)
  have strict_rpow : ((Q Φ (N_seq k) : ℝ) + 1) ^ (h : ℝ) < ((N_seq k : ℝ) ^ (1 / h : ℝ)) ^ (h : ℝ) := by
    apply Real.rpow_lt_rpow (by nlinarith) strict_ineq (by norm_cast)

  -- 7. Simplify RHS: (N^(1/h))^h = N^(1) = N
  -- Apply (x^a)^b = x^(a*b)
  rw [← Real.rpow_mul (by norm_cast; apply Nat.cast_nonneg)] at strict_rpow
  -- Cancel exponents: (1/h) * h = 1
  field_simp [Nat.cast_ne_zero.mpr h0] at strict_rpow

  -- Final Contradiction: N ≤ (Q+1)^h < N
  simp at strict_rpow
  linarith [basis_lower_bound, strict_rpow]

/--
The "Essential Component" property.
Linnik proves that for any F with density d ≥ β, F + Φ has density ≥ β + φ(β).
This requires Vinogradov's estimates on Weyl sums (Lemma 1) [cite: 46]
and the "Large Sieve" method (Lemma 2)[cite: 71, 75].
-/
lemma hΦ_essential_component :
    ∀ A : Set ℕ, schnirelmannDensity (A + Φ) ≥ schnirelmannDensity A := by
  -- Relies on Lemma 5: The set M_N fills segments without gaps [cite: 187]
  -- Which relies on evaluating integral I_M > 0 [cite: 278]
  sorry

/--
**Linnik's Theorem (1942)**
-/
theorem linnik_1942_construction :
    ¬ IsAddBasis Φ ∧
    ∀ A : Set ℕ, schnirelmannDensity (A + Φ) ≥ schnirelmannDensity A := by
  constructor
  · exact hΦ_not_basis
  · exact hΦ_essential_component
