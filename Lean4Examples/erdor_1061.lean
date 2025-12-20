import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

open Nat ArithmeticFunction Finset

-- =========================================================
-- 1. BASIC DEFINITIONS & LEMMAS (Recalled for context)
-- =========================================================

def σ (n : ℕ) : ℕ := sigma 1 n

def is_solution (a b : ℕ) : Prop :=
  σ a + σ b = σ (a + b)

lemma sigma_mul {m n : ℕ} (h : Coprime m n) : σ (m * n) = σ m * σ n := by
  apply isMultiplicative_sigma.map_mul_of_coprime h

-- =========================================================
-- 2. DESCALING LOGIC (The Reverse Direction)
-- =========================================================

/--
The "Descaling Lemma":
If (ka, kb) is a solution and k is coprime to the base terms,
then (a, b) must also be a solution.
-/
lemma solution_descaling (a b k : ℕ) (hk : k > 0)
    (h_coprime : Coprime k (a * b * (a + b)))
    (h_scaled_sol : is_solution (k * a) (k * b)) :
    is_solution a b := by
  unfold is_solution at *

  -- 1. Decompose coprimality
  rw [Nat.coprime_mul_iff_right] at h_coprime
  rcases h_coprime with ⟨h_kab_prod, h_kab_sum⟩
  rw [Nat.coprime_mul_iff_right] at h_kab_prod
  rcases h_kab_prod with ⟨h_ka, h_kb⟩

  -- 2. Expand the scaled equation using multiplicativity
  rw [sigma_mul h_ka, sigma_mul h_kb] at h_scaled_sol

  -- FIX: Correctly factor terms to match the patterns
  -- Current state: σ k * σ a + σ k * σ b = σ (k * a + k * b)

  -- Factor LHS: σ k * σ a + σ k * σ b -> σ k * (σ a + σ b)
  rw [← mul_add (σ k)] at h_scaled_sol

  -- Factor RHS argument: k * a + k * b -> k * (a + b)
  -- We specify arguments to target the sum inside the sigma function
  rw [← mul_add k a b] at h_scaled_sol

  -- Now the pattern σ (k * (a + b)) exists. Expand it.
  rw [sigma_mul h_kab_sum] at h_scaled_sol

  -- 3. Cancel σ(k) from both sides
  -- We know σ(k) ≥ 1 since k > 0.
  have h_sigma_k_pos : 0 < σ k := by
    rw [σ, sigma_apply]
    apply Finset.sum_pos
    · -- Show all terms (divisors) are positive
      intro x hx
      rw [mem_divisors] at hx
      rw [Nat.pow_one]
      exact Nat.pos_of_dvd_of_pos hx.1 hk
    · -- Show the sum is over a nonempty set (contains 1)
      use 1
      rw [mem_divisors]
      exact ⟨one_dvd k, hk.ne'⟩

  -- Use Nat cancellation: a * x = a * y -> x = y given a > 0
  exact Nat.eq_of_mul_eq_mul_left h_sigma_k_pos h_scaled_sol

-- =========================================================
-- 3. PRIMITIVITY & ANCESTRY PROOF
-- =========================================================

/--
Definition: A solution is primitive if it cannot be "descaled" further.
i.e., There is no k > 1 that divides it while respecting coprimality.
-/
def is_primitive (a b : ℕ) : Prop :=
  is_solution a b ∧
  ¬ ∃ (k : ℕ), k > 1 ∧
    k ∣ a ∧ k ∣ b ∧
    Coprime k ((a/k) * (b/k) * ((a/k + b/k)))

/--
Main Theorem: Existence of a Primitive Ancestor.
Every solution (a, b) comes from a primitive solution (a0, b0) scaled by some K.
-/
theorem exists_primitive_ancestor (a b : ℕ)
    (h_pos_a : a > 0) (h_pos_b : b > 0) (h_sol : is_solution a b) :
    ∃ (a0 b0 K : ℕ),
      is_primitive a0 b0 ∧
      a = K * a0 ∧
      b = K * b0 ∧
      Coprime K (a0 * b0 * (a0 + b0)) := by

  -- We proceed by strong induction on the sum S = a + b.
  -- This ensures that if we divide by k > 1, the new sum a' + b' is strictly smaller.
  generalize hS : a + b = S
  induction S using Nat.strong_induction_on generalizing a b with
  | h S ih =>

    -- Case 1: Is (a, b) primitive?
    by_cases h_prim : is_primitive a b
    · -- If yes, we are done. Let K = 1.
      use a, b, 1
      refine ⟨h_prim, ?_, ?_, ?_⟩
      · simp
      · simp
      · -- Coprime 1 ... is always true
        simp

    · -- Case 2: (a, b) is NOT primitive.
      -- Therefore, there exists a valid scaling factor k > 1.
      simp [is_primitive] at h_prim
      -- Since it's not primitive but IS a solution (h_sol), the second part of AND fails
      have h_exists := h_prim h_sol
      rcases h_exists with ⟨k, hk_gt_1, hk_dvd_a, hk_dvd_b, hk_coprime⟩

      -- Define the smaller ancestor (a', b')
      let a' := a / k
      let b' := b / k

      -- Properties of (a', b')
      have ha_eq : a = k * a' := (Nat.mul_div_cancel' hk_dvd_a).symm
      have hb_eq : b = k * b' := (Nat.mul_div_cancel' hk_dvd_b).symm

      have h_pos_a' : a' > 0 := Nat.div_pos (Nat.le_of_dvd h_pos_a hk_dvd_a) (by linarith)
      have h_pos_b' : b' > 0 := Nat.div_pos (Nat.le_of_dvd h_pos_b hk_dvd_b) (by linarith)

      -- 1. Prove (a', b') is a solution using the Descaling Lemma
      have h_sol_small : is_solution a' b' := by
        rw [ha_eq, hb_eq] at h_sol
        refine solution_descaling a' b' k (by linarith) hk_coprime h_sol

      -- 2. Check the induction metric (sum decreases)
      have h_sum_lt : a' + b' < S := by
        rw [← hS, ha_eq, hb_eq, ← mul_add]
        -- Goal: a' + b' < k * (a' + b')
        nth_rewrite 1 [← one_mul (a' + b')]
        apply Nat.mul_lt_mul_of_pos_right hk_gt_1
        -- Must prove (a' + b') > 0 for the inequality to hold
        apply Nat.add_pos_left h_pos_a' b'

      -- 3. Apply Induction Hypothesis to (a', b')
      rcases ih (a' + b') h_sum_lt a' b' h_pos_a' h_pos_b' h_sol_small rfl
        with ⟨a0, b0, k', h_prim_0, h_a'_eq, h_b'_eq, h_coprime_k'⟩

      -- 4. Construct the total scaling factor K = k * k'
      use a0, b0, (k * k')
      refine ⟨h_prim_0, ?_, ?_, ?_⟩

      · -- a = K * a0
        rw [ha_eq, h_a'_eq, mul_assoc]
      · -- b = K * b0
        rw [hb_eq, h_b'_eq, mul_assoc]

      · -- Prove Coprime (k * k') (a0 * b0 * (a0 + b0))
        -- We know:
        -- 1. Coprime k (a' * b' * (a' + b'))  [where a' = k'a0, b' = k'b0]
        -- 2. Coprime k' (a0 * b0 * (a0 + b0))

        rw [Nat.coprime_mul_iff_left]
        constructor
        · -- Show Coprime k ...
          -- The base for k is (a' * b' * (a'+b')).
          -- This base is a multiple of (a0 * b0 * (a0+b0)).
          -- If k is coprime to a multiple, it is coprime to the factor.
          have h_mult : (a0 * b0 * (a0 + b0)) ∣ (a' * b' * (a' + b')) := by
            -- Substitute a' = k'a0, b' = k'b0
            rw [h_a'_eq, h_b'_eq]

            -- Factor out k' from the sum term: (k'a0 + k'b0) -> k'(a0+b0)
            rw [← mul_add]

            -- Now use the Witness for Divisibility
            -- Target: k'a0 * k'b0 * (k'(a0+b0)) = (a0*b0*(a0+b0)) * (k'^3)
            use (k' * k' * k')
            ring

          exact Coprime.coprime_dvd_right h_mult hk_coprime

        · -- Show Coprime k' ...
          exact h_coprime_k'
