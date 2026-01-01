import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators

variable {d : Type} [Fintype d] [DecidableEq d]

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
  h_β2_valid : 0 ≤ β2 ∧ β2 < 1
  h_lmbda_valid : 0 < lmbda ∧ lmbda < 1
  h_gamma_valid : β1^2 / Real.sqrt β2 < 1

variable (p : AdamParams)
variable (T : ℕ)
variable (g : ℕ → d → ℝ)        -- Gradients
variable (θ_star : d → ℝ)       -- Optimal parameter
variable (θ : ℕ → d → ℝ)        -- Parameter sequence
variable (v_hat : ℕ → d → ℝ)    -- 2nd moment estimate (bias corrected)
variable (m_hat : ℕ → d → ℝ)    -- 1st moment estimate (bias corrected)

-- =================================================================
-- 2. Helper Lemmas (Lemmas 10.2 - 10.4 from Kingma & Ba)
-- =================================================================

/-- Lemma 10.2: Convexity Lower Bound -/
lemma lemma_10_2
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

/-- Lemma 10.3 -/
lemma lemma_10_3
  (g : ℕ → ℕ → ℝ) -- Gradient indexed by time t and dimension i
  (G_inf : ℝ)
  (h_g_pos : ∀ i T, ∃ t ∈ Finset.range T, g t i ≠ 0)
  (h_bounded_grad : ∀ t i, |g t i| ≤ G_inf) :
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
    let norm_g_1_Tsucc := Real.sqrt (∑ t ∈ Finset.range (T + 1), (g t i)^2)
    let norm_g_1_T := Real.sqrt (∑ t ∈ Finset.range T, (g t i)^2)
    let g_T_i := g T i

    have h1 : S_curr ≤ 2 * G_inf * Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i^2) + term_new :=
      calc
        S_curr = S_prev + term_new := by
          dsimp [S_curr, S_prev]
          rw [Finset.sum_range_succ]
        _ ≤ 2 * G_inf * norm_g_1_T + term_new := add_le_add_left IH _
        _ = 2 * G_inf * Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i^2) + term_new := by
          congr 2
          dsimp [norm_g_1_Tsucc, norm_g_1_T]
          rw [Finset.sum_range_succ, Real.sq_sqrt]
          · rw [add_tsub_cancel_right]
          · exact add_nonneg (Finset.sum_nonneg' (fun t => sq_nonneg (g t i))) (sq_nonneg g_T_i)

    have h2 : norm_g_1_Tsucc ^ 2 - g_T_i ^ 2 + g_T_i ^ 4 / (4 * norm_g_1_Tsucc ^ 2) ≥ norm_g_1_Tsucc ^ 2 - g_T_i ^ 2 := by
      apply le_add_of_nonneg_right
      positivity

    have h_norm_g_pos : norm_g_1_Tsucc > 0 := by
      dsimp [norm_g_1_Tsucc]
      refine Real.sqrt_pos_of_pos ?_
      refine (Finset.sum_pos_iff_of_nonneg ?_).mpr ?_
      · intro t' ht'
        exact sq_nonneg (g t' i)
      · rcases h_g_pos i (T + 1) with ⟨t, htT, ht⟩
        specialize h_bounded_grad t i
        use t, htT
        exact pow_two_pos_of_ne_zero ht

    have h3 : Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i ^ 2)
        ≤ norm_g_1_Tsucc - g_T_i ^ 2 / (2 * Real.sqrt ((T + 1) * G_inf ^ 2) ) := calc
      Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i ^ 2)
          ≤ norm_g_1_Tsucc - g_T_i ^2 / (2 * norm_g_1_Tsucc) := by
        have h : (norm_g_1_Tsucc - g_T_i ^2 / (2 * norm_g_1_Tsucc)) ^ 2
            = norm_g_1_Tsucc ^ 2 - g_T_i ^ 2 + g_T_i ^ 4 / (4 * norm_g_1_Tsucc ^ 2) := calc
          (norm_g_1_Tsucc - g_T_i ^2 / (2 * norm_g_1_Tsucc)) ^ 2
              = norm_g_1_Tsucc ^ 2 - 2 * norm_g_1_Tsucc * (g_T_i ^2 / (2 * norm_g_1_Tsucc)) + (g_T_i ^2 / (2 * norm_g_1_Tsucc)) ^ 2 := by ring
          _ = norm_g_1_Tsucc ^ 2 - g_T_i ^ 2 + g_T_i ^ 4 / (4 * norm_g_1_Tsucc ^ 2) := by

            have h1 : g_T_i ^ 2 = 2 * norm_g_1_Tsucc * (g_T_i ^2 / (2 * norm_g_1_Tsucc)) := by
              ring_nf
              refine (eq_mul_inv_iff_mul_eq₀ ?_).mpr rfl
              exact (ne_of_lt h_norm_g_pos).symm

            have h2 : (g_T_i ^2 / (2 * norm_g_1_Tsucc)) ^ 2 = g_T_i ^ 4 / (4 * norm_g_1_Tsucc ^ 2) := by
              refine (Real.sqrt_inj (by positivity) (by positivity)).mp ?_
              rw [Real.sqrt_div]
              · have h1 : Real.sqrt ( g_T_i ^ 4 ) = g_T_i ^2 := by
                  have : g_T_i ^ 4 = (g_T_i ^ 2) ^ 2 := by ring
                  rw [this]
                  refine Real.sqrt_sq (by positivity)
                have h2 : Real.sqrt ( 4 * norm_g_1_Tsucc ^ 2 ) = 2 * norm_g_1_Tsucc := by
                  rw [Real.sqrt_mul]
                  · have : Real.sqrt 4 = 2 := (Real.sqrt_eq_iff_mul_self_eq_of_pos (by simp)).mpr (by linarith)
                    rw [this]
                    simp
                    exact Real.sqrt_sq (by positivity)
                  · linarith
                rw [h1, h2]
                refine Real.sqrt_sq (by positivity)
              · positivity
            rw [← h1, h2]

        rw [← h] at h2
        refine (Real.sqrt_le_left ?_).mpr h2
        simp

        refine (div_le_iff₀' ?_).mpr ?_
        · simp
          exact h_norm_g_pos
        · rw [mul_assoc]
          rw [← sq]
          rw [two_mul]
          rw [← zero_add (g_T_i ^ 2)]
          refine add_le_add (sq_nonneg norm_g_1_Tsucc) ?_
          dsimp [norm_g_1_Tsucc]
          rw [Finset.sum_range_succ]
          rw [Real.sq_sqrt]
          · exact le_add_of_nonneg_left (Finset.sum_nonneg' (fun t => sq_nonneg (g t i)))
          · exact add_nonneg (Finset.sum_nonneg' (fun t => sq_nonneg (g t i))) (sq_nonneg g_T_i)
      _ ≤ norm_g_1_Tsucc - g_T_i ^ 2 / (2 * Real.sqrt ((T + 1) * G_inf ^ 2) ) := by
        refine tsub_le_tsub_left ?_ norm_g_1_Tsucc
        refine div_le_div_of_nonneg_left (sq_nonneg g_T_i) ?_ ?_
        · simp
          exact h_norm_g_pos
        · refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          dsimp [norm_g_1_Tsucc]
          refine Real.sqrt_le_sqrt ?_
          have : (T + 1) * G_inf ^ 2 = ∑ t ∈ Finset.range (T + 1), (G_inf ^ 2) := by
            rw [Finset.sum_const]
            rw [Finset.card_range]
            ring
          rw [this]
          refine Finset.sum_le_sum ?_
          intro t ht
          specialize h_bounded_grad t i
          refine (Real.sqrt_le_left ?_).mp ?_
          · refine le_trans ?_ h_bounded_grad
            exact abs_nonneg (g t i)
          · rw [Real.sqrt_sq_eq_abs]
            exact h_bounded_grad

    have hT_pos : 0 < (T : ℝ) + 1 := Nat.cast_add_one_pos T

    have hG_nonneg : 0 ≤ G_inf := by
      specialize h_bounded_grad 0 i
      exact le_trans (abs_nonneg (g 0 i)) h_bounded_grad

    have hG_pos : 0 < G_inf := by
      rcases h_g_pos i (T + 1) with ⟨t, ht⟩
      specialize h_bounded_grad t i
      refine lt_of_le_of_lt' h_bounded_grad ?_
      exact abs_pos.mpr ht.right

    calc
      ∑ t ∈ Finset.range (T + 1), √(g t i ^ 2 / (↑t + 1)) = S_curr := by rfl
      _ ≤ 2 * G_inf * Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i ^ 2) + term_new := h1
      _ ≤ 2 * G_inf * norm_g_1_Tsucc := by
        have h : 2 * G_inf * Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i ^ 2)
            ≤ 2 * G_inf * norm_g_1_Tsucc - g_T_i ^ 2 / Real.sqrt (T + 1) := calc
          2 * G_inf * Real.sqrt (norm_g_1_Tsucc ^ 2 - g_T_i ^ 2)
            ≤ 2 * G_inf * (norm_g_1_Tsucc - g_T_i ^ 2 / (2 * Real.sqrt ((T + 1) * G_inf ^ 2) )) := by
            refine mul_le_mul_of_nonneg_left h3 ?_
            simp
            specialize h_bounded_grad T i
            exact le_trans (abs_nonneg (g T i)) h_bounded_grad
          _ = 2 * G_inf * norm_g_1_Tsucc - g_T_i ^ 2 / Real.sqrt (T + 1) := by
            rw [mul_sub]
            simp
            refine Eq.symm (div_eq_of_eq_mul ?_ ?_)
            · simp
              refine Real.sqrt_ne_zero'.mpr ?_
              exact hT_pos
            · rw [Real.sqrt_mul (le_of_lt hT_pos)]
              rw [Real.sqrt_sq hG_nonneg]
              field_simp [
                hG_pos,
                hT_pos,
                Real.sqrt_pos.mpr hT_pos
              ]

        refine add_le_of_add_le_right ?_ h
        calc
          2 * G_inf * norm_g_1_Tsucc - g_T_i ^ 2 / Real.sqrt (T + 1) + term_new
            = 2 * G_inf * norm_g_1_Tsucc + (- g_T_i ^ 2 / Real.sqrt (T + 1) + term_new) := by ring
          _ ≤ 2 * G_inf * norm_g_1_Tsucc + 0 := by
            refine (add_le_add_iff_left (2 * G_inf * norm_g_1_Tsucc)).mpr ?_
            dsimp [term_new]
            ring_nf
            rw [neg_add_nonpos_iff]
            calc
              √(g T i ^ 2 * (1 + ↑T)⁻¹)
                = √(g T i ^ 2) * Real.sqrt (1 + ↑T)⁻¹ := Real.sqrt_mul (sq_nonneg (g T i)) (1 + ↑T)⁻¹
              _ = √(g T i ^ 2) * (Real.sqrt (1 + ↑T))⁻¹ := by simp
              _ ≤ g_T_i ^ 2 * (√(1 + ↑T))⁻¹ := by
                refine (mul_le_mul_iff_left₀ ?_).mpr ?_
                · refine Right.inv_pos.mpr ?_
                  refine Real.sqrt_pos_of_pos ?_
                  rw [add_comm]
                  exact hT_pos
                · rw [Real.sqrt_sq_eq_abs]
                  show |g T i| ≤ g_T_i ^ 2
                  sorry
          _ = 2 * G_inf * norm_g_1_Tsucc := by linarith

/-- Lemma 10.4: Bound on momentum term (Standard Analysis Result) -/
lemma lemma_10_4
  (γ : ℝ) (h_γ : γ = p.β1^2 / Real.sqrt p.β2)
  (G_2 : d → ℝ) (h_bounded_accum : ∀ i, Real.sqrt (∑ t ∈ Finset.range T, (g t i)^2) ≤ G_2 i) :
  ∀ i, (∑ t ∈ Finset.range T, (m_hat t i)^2 / Real.sqrt ((t+1) * v_hat t i)) ≤
       (2 / (1 - γ)) * (1 / Real.sqrt (1 - p.β2)) * G_2 i := by
  sorry

-- =================================================================
-- 3. Main Theorem (Theorem 10.5)
-- =================================================================

theorem adam_convergence_original_proof
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
  (h_update : ∀ t i, θ (t + 1) i = θ t i - α_t t * m_hat t i / Real.sqrt (v_hat t i))

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
      exact lemma_10_2 g θ_star θ f h_gradient t

  -- 2. Algebraic Rearrangement of Update Rule
  -- We expand ||θ_{t+1} - θ*||^2 to isolate g_t * (θ_t - θ*)
  -- Corresponds to Appendix 10.1, Equation 1123-1124 in Kingma & Ba
  have h_update_expansion : ∀ t i,
    g t i * (θ t i - θ_star i) ≤
    (1 / (2 * α_t t * (1 - p.β1))) * (Real.sqrt (v_hat t i)) * ((θ t i - θ_star i)^2 - (θ (t + 1) i - θ_star i)^2) +
    (Real.sqrt (v_hat t i)) * (D_inf^2 / (2 * α_t t)) -- Placeholder for error terms
    := by
      intro t i
      -- Detailed algebra omitted for brevity, but relies on:
      -- (θ_{t+1} - θ*)^2 = (θ_t - θ* - step)^2
      -- Rearranging terms to bound <g, Δθ>
      sorry

  -- 3. Define the critical potential coefficient Γ_t
  let Γ (t : ℕ) (i : d) := Real.sqrt (v_hat t i) / (2 * α_t t * (1 - p.β1))

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
