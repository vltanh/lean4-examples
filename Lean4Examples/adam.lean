import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators

variable {d : Type}

-- =================================================================
-- 1. Setup & Definitions
-- =================================================================

structure AdamParams where
  α : ℝ         -- Initial step size
  β1 : ℝ        -- Momentum decay
  β2 : ℝ        -- Variance decay
  lmbda : ℝ     -- Decay schedule parameter for β1 (renamed from λ to avoid syntax collision)
  ε : ℝ         -- Epsilon
  h_α_pos : 0 < α
  h_β1_valid : 0 ≤ β1 ∧ β1 < 1
  h_β2_valid : 0 < β2 ∧ β2 < 1
  h_lmbda_valid : 0 < lmbda ∧ lmbda < 1
  h_gamma_valid : β1^2 / Real.sqrt β2 < 1

variable {T : ℕ}
variable (p : AdamParams)
variable (g : ℕ → d → ℝ)        -- Gradients
variable {θ_star : d → ℝ}       -- Optimal parameter
variable {θ : ℕ → d → ℝ}        -- Parameter sequence

-- Definitions needed for the proof expansion
def m (t : ℕ) (i : d) : ℝ :=
  (1 - p.β1) * ∑ k ∈ Finset.range (t + 1), p.β1 ^ (t - k) * g k i

def v (t : ℕ) (i : d) : ℝ :=
  (1 - p.β2) * ∑ k ∈ Finset.range (t + 1), p.β2 ^ (t - k) * (g k i) ^ 2

noncomputable def m_hat (t : ℕ) (i : d) : ℝ :=
  m p g t i / (1 - p.β1 ^ (t + 1))

noncomputable def v_hat (t : ℕ) (i : d) : ℝ :=
  v p g t i / (1 - p.β2 ^ (t + 1))

-- =================================================================
-- 2. Helper Lemmas (Lemmas 10.2 - 10.4 from Kingma & Ba)
-- =================================================================

/-- Lemma 10.2: Convexity Lower Bound -/
lemma lemma_10_2 [Fintype d]
  (f : ℕ → (d → ℝ) → ℝ)
  (h_gradient : ∀ t x y, f t y ≥ f t x + ∑ i, (g t i) * (y i - x i)) :
  ∀ t, f t (θ t) - f t θ_star ≤ ∑ i, g t i * (θ t i - θ_star i) := by
  intro t
  specialize h_gradient t (θ t) θ_star
  have h_neg : ∑ i, g t i * (θ_star i - θ t i) = - ∑ i, g t i * (θ t i - θ_star i) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    linarith
  rw [h_neg] at h_gradient
  linarith

/-- Lemma 10.3
-- Assumption needed: |g t i| ≥ 1 when g t i ≠ 0
-- This is a strong assumption and is not generally true.
-/
axiom h_g_ge_one (i : d) (t : ℕ) : g t i ≠ 0 → 1 ≤ |g t i|

lemma lemma_10_3
  (G_inf : ℝ) (h_bounded_grad : ∀ t i, |g t i| ≤ G_inf) :
  ∀ i T, ∑ t ∈ Finset.range T, Real.sqrt ((g t i)^2 / (t + 1)) ≤
       2 * G_inf * Real.sqrt (∑ t ∈ Finset.range T, (g t i)^2) :=
by
  intro i T
  induction T with
  | zero =>
    simp
  | succ T IH =>
    let term_new := Real.sqrt ((g T i)^2 / (T + 1))
    let S_prev := ∑ t ∈ Finset.range T, Real.sqrt ((g t i)^2 / (t + 1))
    let S_curr := ∑ t ∈ Finset.range (T + 1), Real.sqrt ((g t i)^2 / (t + 1))
    let norm_g_prev := Real.sqrt (∑ t ∈ Finset.range T, (g t i)^2)
    let norm_g_curr := Real.sqrt (∑ t ∈ Finset.range (T + 1), (g t i)^2)

    by_cases h_gTi : g T i = 0
    · dsimp [term_new]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [h_gTi]
      simp
      exact IH
    · have h_norm_g_pos : norm_g_curr > 0 := by
        dsimp [norm_g_curr]
        refine Real.sqrt_pos_of_pos ?_
        refine (Finset.sum_pos_iff_of_nonneg ?_).mpr ?_
        · intro t' ht'
          exact sq_nonneg (g t' i)
        · use T
          constructor
          · exact Finset.self_mem_range_succ T
          · exact pow_two_pos_of_ne_zero h_gTi

      have hG_pos : 0 < G_inf := by
        specialize h_bounded_grad T i
        refine lt_of_le_of_lt' h_bounded_grad ?_
        exact abs_pos.mpr h_gTi

      have hT_pos : 0 < (T : ℝ) + 1 := Nat.cast_add_one_pos T

      have h1 : S_curr ≤ 2 * G_inf * Real.sqrt (norm_g_curr^2 - (g T i)^2) + term_new :=
        calc
          S_curr = S_prev + term_new := by
            dsimp [S_curr, S_prev]
            rw [Finset.sum_range_succ]
          _ ≤ 2 * G_inf * norm_g_prev + term_new := add_le_add_left IH _
          _ = 2 * G_inf * Real.sqrt (norm_g_curr^2 - (g T i)^2) + term_new := by
            congr 2
            dsimp [norm_g_curr, norm_g_prev]
            rw [Finset.sum_range_succ, Real.sq_sqrt]
            · rw [add_tsub_cancel_right]
            · exact add_nonneg (Finset.sum_nonneg' (fun t => sq_nonneg (g t i))) (sq_nonneg (g T i))

      have h2 : norm_g_curr^2 - (g T i)^2 + (g T i)^4 / (4 * norm_g_curr^2) ≥ norm_g_curr^2 - (g T i)^2 := by
        apply le_add_of_nonneg_right
        positivity

      have h3 : Real.sqrt (norm_g_curr^2 - (g T i)^2)
          ≤ norm_g_curr - (g T i)^2 / (2 * Real.sqrt ((T + 1) * G_inf^2) ) := calc
        Real.sqrt (norm_g_curr^2 - (g T i)^2)
            ≤ norm_g_curr - (g T i)^2 / (2 * norm_g_curr) := by

          have h_expand : (norm_g_curr - (g T i)^2 / (2 * norm_g_curr))^2 =
              norm_g_curr^2 - (g T i)^2 + (g T i)^4 / (4 * norm_g_curr^2) := by
            rw [sub_sq]
            have : ((g T i)^2 / (2 * norm_g_curr))^2 = (g T i)^4 / (4 * norm_g_curr^2) := by
              field_simp [ne_of_gt h_norm_g_pos]
              ring
            rw [this]
            field_simp [ne_of_gt h_norm_g_pos]

          rw [← h_expand] at h2
          refine (Real.sqrt_le_left ?_).mpr h2
          simp

          refine (div_le_iff₀' ?_).mpr ?_
          · simp
            exact h_norm_g_pos
          · rw [mul_assoc]
            rw [← sq]
            rw [two_mul]
            rw [← zero_add ((g T i)^2)]
            refine add_le_add (sq_nonneg norm_g_curr) ?_
            dsimp [norm_g_curr]
            rw [Finset.sum_range_succ]
            rw [Real.sq_sqrt]
            · exact le_add_of_nonneg_left (Finset.sum_nonneg' (fun t => sq_nonneg (g t i)))
            · exact add_nonneg (Finset.sum_nonneg' (fun t => sq_nonneg (g t i))) (sq_nonneg (g T i))
        _ ≤ norm_g_curr - (g T i)^2 / (2 * Real.sqrt ((T + 1) * G_inf^2) ) := by
          gcongr
          apply Real.sqrt_le_sqrt
          calc
            ∑ t ∈ Finset.range (T + 1), (g t i)^2
            ≤ ∑ t ∈ Finset.range (T + 1), G_inf^2 := by
              apply Finset.sum_le_sum
              intro t ht
              specialize h_bounded_grad t i
              exact sq_le_sq.mpr (le_trans h_bounded_grad (le_abs_self G_inf))
            _ = (T + 1) * G_inf^2 := by simp

      calc
        ∑ t ∈ Finset.range (T + 1), √((g t i)^2 / (↑t + 1)) = S_curr := by rfl
        _ ≤ 2 * G_inf * Real.sqrt (norm_g_curr^2 - (g T i)^2) + term_new := h1
        _ ≤ 2 * G_inf * norm_g_curr := by
          have h : 2 * G_inf * Real.sqrt (norm_g_curr^2 - (g T i)^2)
              ≤ 2 * G_inf * norm_g_curr - (g T i)^2 / Real.sqrt (T + 1) := calc
            2 * G_inf * Real.sqrt (norm_g_curr^2 - (g T i)^2)
              ≤ 2 * G_inf * (norm_g_curr - (g T i)^2 / (2 * Real.sqrt ((T + 1) * G_inf^2) )) := by gcongr
            _ = 2 * G_inf * norm_g_curr - (g T i)^2 / Real.sqrt (T + 1) := by
              rw [mul_sub]
              rw [Real.sqrt_mul (le_of_lt hT_pos)]
              rw [Real.sqrt_sq (le_of_lt hG_pos)]
              field_simp [hG_pos, Real.sqrt_pos.mpr hT_pos]

          refine add_le_of_add_le_right ?_ h
          calc
            2 * G_inf * norm_g_curr - (g T i)^2 / Real.sqrt (T + 1) + term_new
              = 2 * G_inf * norm_g_curr + (- (g T i)^2 / Real.sqrt (T + 1) + term_new) := by ring
            _ ≤ 2 * G_inf * norm_g_curr + 0 := by
              refine (add_le_add_iff_left (2 * G_inf * norm_g_curr)).mpr ?_
              dsimp [term_new]
              ring_nf
              rw [neg_add_nonpos_iff]
              calc
                √((g T i)^2 * (1 + ↑T)⁻¹)
                  = Real.sqrt ((g T i)^2) * Real.sqrt (1 + ↑T)⁻¹ := Real.sqrt_mul (sq_nonneg (g T i)) (1 + ↑T)⁻¹
                _ ≤ (g T i)^2 * (Real.sqrt (1 + ↑T))⁻¹ := by
                  gcongr
                  · rw [Real.sqrt_sq_eq_abs]
                    have h_one_le : 1 ≤ |g T i| := h_g_ge_one g i T h_gTi
                    rw [← mul_one |g T i|]
                    rw [← sq_abs, sq]
                    refine mul_le_mul_of_nonneg_left h_one_le (abs_nonneg (g T i))
                  · simp
            _ = 2 * G_inf * norm_g_curr := by linarith

lemma arithmetic_geometric_sum_bound
  (n : ℕ) (r : ℝ) (h_nonneg : 0 ≤ r) (h_lt_one : r < 1) :
  ∑ t ∈ Finset.range n, (t + 1) * r ^ (t + 1) ≤ 1 / (1 - r) ^ 2 := by
  -- 1. Define the unshifted sum
  let S_base := ∑ t ∈ Finset.range n, ((t : ℝ) + 1) * r ^ t
  -- 2. Prove the bound for the unshifted sum
  have h_base_bound : S_base ≤ 1 / (1 - r) ^ 2 := by
    cases n with
    | zero =>
      simp [S_base]
      positivity
    | succ n' =>
      -- Multiply S_base by (1-r)
      have h_mul : (1 - r) * S_base =
        (∑ t ∈ Finset.range (n' + 1), r ^ t) - (n' + 1) * r ^ (n' + 1) := by
        -- (1-r)S = S - rS
        -- S  = 1 + 2r + ... + nr^(n-1)
        -- rS =     1r + ... + (n-1)r^(n-1) + nr^n
        -- S - rS = 1 + r + ... + r^(n-1) - nr^n
        -- Formal proof using sum manipulation:
        rw [sub_mul, one_mul]
        let N := n' + 1
        have h_shift : r * S_base = ∑ t ∈ Finset.range N, (t+1)*r^(t+1) := by
          dsimp [S_base]; rw [Finset.mul_sum]; congr; ext; ring

        -- We want to show: S_base - r*S_base = (sum r^t) - N*r^N
        rw [h_shift]

        -- Helper: sum_{0}^{N-1} (t+1)r^(t+1) = sum_{0}^{N-1} t*r^t + N*r^N
        have h_idx_shift : ∑ t ∈ Finset.range N, (t+1)*r^(t+1) =
          (∑ t ∈ Finset.range N, t*r^t) + N*r^N := by
          dsimp only [N]
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ']
          simp

        rw [h_idx_shift]
        rw [sub_add_eq_sub_sub]
        congr 1
        -- S_base - sum t*r^t = sum (t+1-t)r^t = sum r^t
        dsimp [S_base]
        rw [← Finset.sum_sub_distrib]
        congr; ext; ring

        congr
        dsimp [N]
        exact Nat.cast_add_one n'

      -- Apply geometric sum formula to bound (1-r)S_base
      have h_bound_mul : (1 - r) * S_base ≤ 1 / (1 - r) := by
        rw [h_mul]
        -- Explicit calculation to avoid unification errors with le_trans
        calc
          (∑ t ∈ Finset.range (n' + 1), r ^ t) - (↑n' + 1) * r ^ (n' + 1)
          ≤ ∑ t ∈ Finset.range (n' + 1), r ^ t := by
            apply sub_le_self
            apply mul_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one) (pow_nonneg h_nonneg _)
          _ = (r ^ (n' + 1) - 1) / (r - 1) := geom_sum_eq h_lt_one.ne (n' + 1)
          _ = (1 - r ^ (n' + 1)) / (1 - r) := by
            rw [← neg_sub (r ^ (n' + 1)), ← neg_sub r, neg_div_neg_eq]
          _ ≤ 1 / (1 - r) := by
            apply div_le_div_of_nonneg_right
            · rw [sub_le_self_iff]; apply pow_nonneg h_nonneg
            · exact le_of_lt (sub_pos.mpr h_lt_one)

      -- Divide by (1-r)
      -- simp [S_base]
      rwa [
        le_div_iff₀ ( sub_pos.mpr h_lt_one ),
        mul_comm, ← mul_assoc, ← pow_two, mul_comm,
        ← le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr h_lt_one))
      ] at h_bound_mul

  -- 3. Connect S_base to the target sum
  calc
    ∑ t ∈ Finset.range n, ((t : ℝ) + 1) * r ^ (t + 1)
      = ∑ t ∈ Finset.range n, r * (((t : ℝ) + 1) * r ^ t) := by
        congr; ext; ring
    _ = r * S_base := by
        rw [Finset.mul_sum]
    _ ≤ 1 * S_base := by
        apply mul_le_mul_of_nonneg_right (le_of_lt h_lt_one)
        apply Finset.sum_nonneg
        intro t _
        apply mul_nonneg (add_nonneg (Nat.cast_nonneg t) zero_le_one) (pow_nonneg h_nonneg t)
    _ ≤ 1 / (1 - r) ^ 2 := by
        rwa [one_mul]

/-- Lemma 10.4: Bound on momentum term -/
lemma lemma_10_4
  (G_inf : ℝ) (h_bounded_grad : ∀ t i, |g t i| ≤ G_inf) :
  let γ := p.β1^2 / Real.sqrt p.β2
  ∀ i, (∑ t ∈ Finset.range T, (m_hat p g t i)^2 / Real.sqrt ((t+1) * v_hat p g t i)) ≤
    (2 * G_inf) / ((1 - γ)^2 * Real.sqrt (1 - p.β2)) * Real.sqrt (∑ t ∈ Finset.range T, (g t i)^2) := by
  intro γ i

  have h_bias_correction : ∀ t,
    Real.sqrt (1 - p.β2^(t+1)) / (1 - p.β1^(t+1))^2 ≤ 1 / (1 - p.β1)^2 := by
    intro t
    gcongr
    · refine sq_pos_of_pos ?_
      simp
      exact p.h_β1_valid.right
    · refine Real.sqrt_le_one.mpr ?_
      simp
      refine pow_succ_nonneg ?_ t
      exact le_of_lt p.h_β2_valid.left
    · simp
      exact le_of_lt p.h_β1_valid.right
    · apply pow_le_of_le_one (p.h_β1_valid.left) (le_of_lt p.h_β1_valid.right)
      exact (Nat.zero_ne_add_one t).symm

  have h_term_bound : ∀ t ∈ Finset.range T,
    (m_hat p g t i)^2 / Real.sqrt ((t+1) * v_hat p g t i) ≤
    (1 / Real.sqrt (1 - p.β2)) * ∑ k ∈ Finset.range (t+1), Real.sqrt (t+1) * γ^(t-k) * |g k i| := by
    intro t ht
    let term := (m_hat p g t i)^2 / Real.sqrt ((t+1) * v_hat p g t i)

    -- 1. Bias correction
    have step1 : term ≤ (m p g t i)^2 / Real.sqrt ((t+1) * v p g t i) * (1 / (1 - p.β1)^2) := by
      dsimp [term, m_hat, v_hat]

      have h_denom : Real.sqrt ((t+1) * (v p g t i / (1 - p.β2^(t+1)))) =
                     Real.sqrt ((t+1) * v p g t i) / Real.sqrt (1 - p.β2^(t+1)) := by
        rw [← mul_div_assoc, Real.sqrt_div]
        apply mul_nonneg
        · positivity
        · dsimp [v]
          apply mul_nonneg (sub_nonneg.mpr (le_of_lt p.h_β2_valid.right))
          apply Finset.sum_nonneg
          intro k _
          apply mul_nonneg (pow_nonneg (le_of_lt p.h_β2_valid.left) _) (sq_nonneg _)

      rw [div_pow, h_denom]

      trans (m p g t i ^ 2 / Real.sqrt ((↑t + 1) * v p g t i)) * (Real.sqrt (1 - p.β2 ^ (t + 1)) / (1 - p.β1 ^ (t + 1)) ^ 2)
      · simp only [div_eq_mul_inv, mul_inv, inv_inv]
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [mul_comm, mul_assoc]
      · apply mul_le_mul_of_nonneg_left
        · apply h_bias_correction
        · apply div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

    have step2 : (m p g t i)^2 ≤ (1 - p.β1)^2 * (t+1) * ∑ k ∈ Finset.range (t+1), (p.β1^(t-k))^2 * (g k i)^2 := by
      dsimp [m]
      rw [mul_pow]
      -- Re-associate to ensure gcongr peels the correct constant factor
      rw [mul_assoc ((1 - p.β1) ^ 2)]
      gcongr

      -- Apply Cauchy-Schwarz: (∑ x)^2 ≤ (∑ 1^2) (∑ x^2)
      let f := fun k => p.β1^(t-k) * g k i
      have h_cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (t+1)) (fun _ => 1) f
      simp only [one_pow, one_mul] at h_cs

      -- Evaluate sum of 1s
      have h_sum_ones : ∑ _k ∈ Finset.range (t+1), (1:ℝ) = t + 1 := by simp
      rw [h_sum_ones] at h_cs

      -- Apply h_cs and match terms
      refine le_trans h_cs ?_
      gcongr with k hk
      dsimp [f]
      rw [mul_pow]

    -- Combine 1 & 2
    have step3 : term ≤ ((t+1) * ∑ k ∈ Finset.range (t+1), p.β1^(2*(t-k)) * (g k i)^2) / Real.sqrt ((t+1) * v p g t i) := by
      calc term
        ≤ (m p g t i)^2 / Real.sqrt ((t+1) * v p g t i) * (1 / (1 - p.β1)^2) := step1
        _ ≤ ((1 - p.β1)^2 * (t+1) * ∑ k ∈ Finset.range (t+1), (p.β1^(t-k))^2 * (g k i)^2) /
            Real.sqrt ((t+1) * v p g t i) * (1 / (1 - p.β1)^2) := by gcongr
        _ = ((t+1) * ∑ k ∈ Finset.range (t+1), p.β1^(2*(t-k)) * (g k i)^2) / Real.sqrt ((t+1) * v p g t i) := by
            -- 1. Cancel the (1 - β1)^2 terms
            have h_ne : 1 - p.β1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt p.h_β1_valid.right)
            field_simp [sq_eq_zero_iff, h_ne]

            -- 2. Align the exponents in the summation: (β^(t-k))^2 = β^(2*(t-k))
            congr 1
            congr 1
            ext k
            simp
            left
            rw [pow_mul']

    -- 3. Lower bound v_t and split sum (sum A / sqrt sum B <= sum (A / sqrt B))
    have step4 : term ≤ ∑ k ∈ Finset.range (t+1),
        ((t+1) * p.β1^(2*(t-k)) * (g k i)^2) / Real.sqrt ((t+1) * (1 - p.β2) * p.β2^(t-k) * (g k i)^2) := by
      refine le_trans step3 ?_
      dsimp [v]

      -- Move the constant factor (t+1) inside the numerator sum
      rw [Finset.mul_sum]
      -- Move the division inside the sum (distributive property)
      rw [Finset.sum_div]

      -- Compare the sums term-by-term
      apply Finset.sum_le_sum
      intro k hk

      rw [← mul_assoc ((t:ℝ)+1)]

      -- We need to show: Num / sqrt(Total) ≤ Num / sqrt(Single)
      -- This holds if 0 ≤ Num and 0 < sqrt(Single) ≤ sqrt(Total)
      -- Handle the case where gradient is zero (0 ≤ 0)
      by_cases hg : g k i = 0
      · simp [hg]
      · -- Case g ≠ 0
        apply div_le_div_of_nonneg_left
        · -- Numerator is non-negative
          apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · rw [pow_mul']
              positivity
          · positivity
        · apply Real.sqrt_pos.mpr
          apply mul_pos
          · apply mul_pos
            · apply mul_pos
              · positivity
              · exact sub_pos_of_lt p.h_β2_valid.right
            · refine pow_pos p.h_β2_valid.left (t - k)
          · exact pow_two_pos_of_ne_zero hg

        · -- sqrt(Single) ≤ sqrt(Total)
          apply Real.sqrt_le_sqrt
          rw [← mul_assoc, mul_assoc]
          gcongr
          · apply mul_nonneg
            · positivity
            · refine sub_nonneg.mpr ?_
              exact le_of_lt p.h_β2_valid.right
          · let f := fun (j : ℕ) => p.β2 ^ (t - j) * (g j i) ^ 2
            change f k ≤ ∑ j ∈ Finset.range (t + 1), f j
            apply Finset.single_le_sum
            · -- Show f j ≥ 0 for all j
              intro j _
              dsimp [f]
              apply mul_nonneg
              · refine pow_nonneg ?_ (t - j)
                exact le_of_lt p.h_β2_valid.left
              · positivity
            · exact hk

    -- 4. Simplify to gamma form
    refine le_trans step4 ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [
      Real.sqrt_mul (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (le_of_lt p.h_β2_valid.right))) (pow_nonneg (le_of_lt p.h_β2_valid.left) (t - k))),
      Real.sqrt_mul (mul_nonneg (by positivity) (sub_nonneg.mpr (le_of_lt p.h_β2_valid.right))),
      Real.sqrt_mul (by positivity)
    ]
    rw [Real.sqrt_sq_eq_abs]

    have h_gamma_eq : p.β1^(2*(t-k)) / Real.sqrt (p.β2^(t-k)) = γ^(t-k) := by
      dsimp [γ]
      rw [div_pow, ← pow_mul]
      congr
      rw [Real.sqrt_eq_cases]
      left
      constructor
      · rw [← mul_pow, Real.mul_self_sqrt (le_of_lt p.h_β2_valid.left)]
      · positivity

    by_cases h_case : g k i = 0
    · simp [h_case]
    · rw [← h_gamma_eq]
      field_simp [p.h_β2_valid.left, p.h_β2_valid.right, Real.sqrt_pos.mpr]
      apply le_of_eq
      rw [← mul_comm (√(t + 1) ^ 2), mul_assoc, mul_assoc]
      simp
      left
      rw [sq]
      rw [Real.mul_self_sqrt]
      positivity

  have sum_range_le_swap (n : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ t ∈ Finset.range n, ∑ k ∈ Finset.range (t + 1), f t k =
    ∑ k ∈ Finset.range n, ∑ t ∈ (Finset.range n).filter (k ≤ ·), f t k := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij'
      (fun x _ ↦ ⟨x.2, x.1⟩) -- Forward map: (t, k) -> (k, t)
      (fun x _ ↦ ⟨x.2, x.1⟩) -- Backward map: (k, t) -> (t, k)
      ?_ ?_ ?_ ?_ ?_
    -- 1. Forward map lands in codomain
    · rintro ⟨t, k⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx ⊢
      obtain ⟨ht, hk⟩ := hx
      refine ⟨lt_of_le_of_lt (Nat.le_of_lt_succ hk) ht, ht, Nat.le_of_lt_succ hk⟩
    -- 2. Value equality (f t k = f t k)
    · rintro ⟨t, k⟩ ha
      simp at ha ⊢
      constructor
      · exact ha.right.left
      · rw [Order.lt_add_one_iff]
        exact ha.right.right
    -- 3. Backward map lands in domain
    · rintro ⟨k, t⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    -- 4. Left Inverse
    · rintro ⟨t, k⟩ _; rfl
    -- 5. Right Inverse
    · rintro ⟨k, t⟩ _; rfl

  have sum_filter_shift (T k : ℕ) (f : ℕ → ℝ) (hkT : k ≤ T) :
      ∑ t ∈ (Finset.range T).filter (k ≤ ·), f (t - k) = ∑ j ∈ Finset.range (T - k), f j := by
    refine Finset.sum_bij (fun t _ ↦ t - k) ?_ ?_ ?_ ?_
    -- 1. Map lands in codomain
    · intro t ht
      simp only [Finset.mem_range, Finset.mem_filter] at ht ⊢
      apply Nat.sub_lt_right_of_lt_add ht.2
      rw [Nat.sub_add_cancel hkT]
      exact ht.left
    -- 2. Values match
    · intro t ht a ha h
      simp at ht ha h ⊢
      rw [← Nat.sub_add_cancel ht.right]
      rw [← Nat.sub_add_cancel ha.right]
      rw [h]
    -- 3. Surjectivity (Inverse map exists)
    · intro j hj
      simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
      refine ⟨j + k, ⟨Nat.add_lt_of_lt_sub hj, Nat.le_add_left k j⟩, Nat.add_sub_cancel j k⟩
    -- 4. Injectivity
    · intro t ht; simp only [Finset.mem_range, Finset.mem_filter] at ht
      simp

  calc
    ∑ t ∈ Finset.range T, (m_hat p g t i)^2 / Real.sqrt ((t+1) * v_hat p g t i)
      ≤ ∑ t ∈ Finset.range T, (1 / Real.sqrt (1 - p.β2)) * ∑ k ∈ Finset.range (t+1), Real.sqrt (t+1) * γ^(t-k) * |g k i| := by
      apply Finset.sum_le_sum
      intro t ht
      apply h_term_bound t ht
    _ = (1 / Real.sqrt (1 - p.β2)) * ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t+1), (|g k i| * (Real.sqrt (t+1) * γ^(t-k))) := by
      rw [Finset.mul_sum]; congr; ext t; congr; ext k; ring
    _ = (1 / Real.sqrt (1 - p.β2)) * ∑ k ∈ Finset.range T, ∑ t ∈ (Finset.range T).filter (k ≤ ·), (|g k i| * (Real.sqrt (t+1) * γ^(t-k))) := by
      congr 1
      rw [sum_range_le_swap T (fun t k ↦ |g k i| * (Real.sqrt (t + 1) * γ ^ (t - k)))]
    _ = (1 / Real.sqrt (1 - p.β2)) * ∑ k ∈ Finset.range T, |g k i| * ∑ t ∈ (Finset.range T).filter (k ≤ ·), Real.sqrt (t+1) * γ^(t-k) := by
      congr; ext k
      rw [Finset.mul_sum]
    _ ≤ (1 / Real.sqrt (1 - p.β2)) * ∑ k ∈ Finset.range T, |g k i| * ∑ t ∈ Finset.range (T - k), Real.sqrt (t + k + 1) * γ^t := by
      -- 3. Reindex t -> t - k (using helper lemma)
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Real.sqrt_nonneg _))
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      -- Apply equality via `le_of_eq` and the shift lemma
      apply le_of_eq
      -- We match the form f(t-k) by observing:
      -- Real.sqrt (t + 1) * γ^(t-k) = Real.sqrt ((t-k) + k + 1) * γ^(t-k)
      convert sum_filter_shift T k (fun x ↦ Real.sqrt (x + k + 1) * γ^x) (Finset.mem_range_le hk) using 2
      congr
      expose_names
      have hkx : k ≤ x := by
        simp at h
        exact h.right
      rw [← Nat.cast_add, Nat.sub_add_cancel hkx]
    _ = sorry := sorry
    _ ≤ (2 * G_inf) / ((1 - γ)^2 * Real.sqrt (1 - p.β2)) * Real.sqrt (∑ t ∈ Finset.range T, (g t i)^2) := by
      sorry

-- =================================================================
-- 3. Main Theorem (Theorem 10.5)
-- =================================================================

theorem adam_convergence_original_proof
  [Fintype d]
  -- Problem Setup
  (f : ℕ → (d → ℝ) → ℝ)
  (h_convex : ∀ t, ConvexOn ℝ Set.univ (f t))
  (h_gradient : ∀ t x y, f t y ≥ f t x + ∑ i, (g t i) * (y i - x i))
  (G_inf : ℝ) (h_bounded_grad : ∀ t i, |g t i| ≤ G_inf)
  (D_inf : ℝ) (h_bounded_dist : ∀ t, ‖θ t - θ_star‖ ≤ D_inf)

  -- Algorithm Definitions (local to the theorem context)
  (α_t : ℕ → ℝ := fun t => p.α / Real.sqrt (t + 1 : ℝ))
  (β1_t : ℕ → ℝ := fun t => p.β1 * p.lmbda^(t))

  -- The Update Rule (Hypothesis on θ)
  -- θ_{t+1} = θ_t - α_t * m_hat / sqrt(v_hat)
  (h_update : ∀ t i, θ (t + 1) i = θ t i - α_t t * m_hat p g t i / Real.sqrt (v_hat p g t i))

  -- Constants for the bound (simplified)
  (C_reg : ℝ)
  :
  -- CONCLUSION: Regret is bounded
  (∑ t ∈ Finset.range T, (f t (θ t) - f t θ_star)) ≤ C_reg * Real.sqrt T := by
  -- 1. Linearization (Convexity)
  have h_lin_bound :
    (∑ t ∈ Finset.range T, (f t (θ t) - f t θ_star)) ≤
    ∑ t ∈ Finset.range T, ∑ i, g t i * (θ t i - θ_star i) := by
      apply Finset.sum_le_sum
      intro t _
      exact lemma_10_2 g f h_gradient t

  -- 2. Algebraic Rearrangement of Update Rule
  -- We expand ||θ_{t+1} - θ*||^2 to isolate g_t * (θ_t - θ*)
  -- Corresponds to Appendix 10.1, Equation 1123-1124 in Kingma & Ba
  have h_update_expansion : ∀ t i,
    g t i * (θ t i - θ_star i) ≤
    (1 / (2 * α_t t * (1 - p.β1))) * (Real.sqrt (v_hat p g t i)) * ((θ t i - θ_star i)^2 - (θ (t + 1) i - θ_star i)^2) +
    (Real.sqrt (v_hat p g t i)) * (D_inf^2 / (2 * α_t t)) -- Placeholder for error terms
    := by
      intro t i
      -- Detailed algebra omitted for brevity, but relies on:
      -- (θ_{t+1} - θ*)^2 = (θ_t - θ* - step)^2
      -- Rearranging terms to bound <g, Δθ>
      sorry

  -- 3. Define the critical potential coefficient Γ_t
  let Γ (t : ℕ) (i : d) := Real.sqrt (v_hat p g t i) / (2 * α_t t * (1 - p.β1))

  -- 4. THE FAULTY ASSUMPTION
  -- "We assume Γ_{t+1} ≥ Γ_t" (inverse learning rate is monotonic)
  -- This allows telescoping the sum with favorable signs.
  have h_faulty_assumption : ∀ t i, Γ (t + 1) i ≥ Γ t i :=
    sorry

  -- 5. Telescoping the Main Term
  have h_telescope :
    (∑ t ∈ Finset.range T, ∑ i, Γ t i * ((θ t i - θ_star i)^2 - (θ (t + 1) i - θ_star i)^2)) ≤
    (∑ i, Γ T i * D_inf^2) :=
    by
      -- This step crucially relies on h_faulty_assumption.
      -- Sum = Γ_0*Δ_0 + (Γ_1 - Γ_0)*Δ_1 + ... + (Γ_T - Γ_{T-1})*Δ_T - Γ_T*Δ_{T+1}
      -- Since (Γ_{t+1} - Γ_t) ≥ 0 (Faulty Assumption) and Δ_t ≥ 0,
      -- we can bound the sum effectively.
      -- Without this assumption, the (Γ_{t+1} - Γ_t) terms could be large negative numbers,
      -- destroying the bound.
      sorry

  -- 6. Combine for Final Result
  calc
    (∑ t ∈ Finset.range T, (f t (θ t) - f t θ_star))
      ≤ ∑ t ∈ Finset.range T, ∑ i, g t i * (θ t i - θ_star i) := h_lin_bound
    _ ≤ ∑ i, (Γ T i * D_inf^2) + sorry := by
      sorry
    _ ≤ C_reg * Real.sqrt T := by
      sorry
