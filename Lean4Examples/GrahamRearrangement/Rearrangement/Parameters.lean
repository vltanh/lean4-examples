import Lean4Examples.GrahamRearrangement.Rearrangement.IntervalLemmas

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: constants and parameter package
-/

noncomputable section

/-- A fixed positive constant C_k witnessing Corollary 4.2. -/
def chainConstant (k : ℕ) : ℝ := by
  classical
  by_cases hk : 0 < k
  · exact Classical.choose (corollary42 k hk)
  · exact 1

theorem chainConstant_pos (k : ℕ) : 0 < chainConstant k := by
  classical
  unfold chainConstant
  split
  · rename_i hk
    exact (Classical.choose_spec (corollary42 k hk)).1
  · norm_num

theorem chainConstant_spec (k : ℕ) (hk : 0 < k) :
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : Fin k → ℕ), IsChainSizeTuple S.card m →
      ∀ z : Fin k → ZMod p,
        chainMass S m z ≤
          chainUpperBound p S.card (chainConstant k) m := by
  classical
  unfold chainConstant
  simp only [dif_pos hk]
  exact (Classical.choose_spec (corollary42 k hk)).2

def section5D (α : ℝ) : ℕ :=
  Nat.ceil (3 / α)

theorem section5D_ge_seven {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    7 ≤ section5D α :=
  External.ceil_three_div_ge_seven hα0 hαh

theorem section5D_pos {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    0 < section5D α :=
  lt_of_lt_of_le (by norm_num) (section5D_ge_seven hα0 hαh)

theorem alpha_mul_section5D_ge_three {α : ℝ}
    (hα0 : 0 < α) :
    3 ≤ α * section5D α := by
  have hceil :
      3 / α ≤ (section5D α : ℝ) := by
    exact_mod_cast Nat.le_ceil (3 / α)
  have := mul_le_mul_of_nonneg_left hceil (le_of_lt hα0)
  field_simp at this
  nlinarith

structure Section5Parameters (α : ℝ) where
  D : ℕ
  D_eq : D = section5D α
  Cα : ℝ
  Cα_pos : 0 < Cα
  Cα_first :
    ((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α) ≤ Cα
  Cα_second :
    (D + 1 : ℝ) * (2 : ℝ) ^ D *
      (D : ℝ) ^ (14 * D ^ 2) ≤ Cα
  Cα_fiftyD : (50 * D : ℝ) ≤ Cα
  second_ge_100 :
    (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
      (D + 1 : ℝ) * (2 : ℝ) ^ D *
        (D : ℝ) ^ (14 * D ^ 2)
  hundred_ge_40 :
    (40 * D : ℝ) ^ D ≤
      (100 : ℝ) * (5 * D : ℝ) ^ (2 * D)
  asymptotic :
    ∀ n : ℕ, Cα ≤ n →
      4 * max (chainConstant D) (chainConstant 1) *
          Real.sqrt (Real.log (n : ℝ)) /
            Real.sqrt (n : ℝ) ≤
        (n : ℝ) ^ (-α)

theorem exists_section5Parameters {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    ∃ P : Section5Parameters α, True := by
  let D := section5D α
  have hD7 : 7 ≤ D := section5D_ge_seven hα0 hαh
  have hK :
      0 ≤ 4 * max (chainConstant D) (chainConstant 1) := by
    positivity
  obtain ⟨N, hN2, hNasym⟩ :=
    External.exists_sqrt_log_power_threshold
      (α := α)
      (K := 4 * max (chainConstant D) (chainConstant 1))
      hα0 hαh hK
  let A : ℝ :=
    ((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α)
  let B : ℝ :=
    (D + 1 : ℝ) * (2 : ℝ) ^ D *
      (D : ℝ) ^ (14 * D ^ 2)
  let Cα : ℝ := max A (max B (max (50 * D : ℝ) N))
  have hCpos : 0 < Cα := by
    dsimp [Cα]
    positivity
  rcases External.section5_power_inequalities D hD7 with
    ⟨hB100, h10040⟩
  refine ⟨{
    D := D
    D_eq := rfl
    Cα := Cα
    Cα_pos := hCpos
    Cα_first := ?_
    Cα_second := ?_
    Cα_fiftyD := ?_
    second_ge_100 := hB100
    hundred_ge_40 := h10040
    asymptotic := ?_
  }, trivial⟩
  · exact le_max_left _ _
  · exact le_trans (le_max_left B (max (50 * D : ℝ) N))
      (le_max_right A _)
  · exact le_trans
      (le_trans (le_max_left (50 * D : ℝ) N)
        (le_max_right B _))
      (le_max_right A _)
  · intro n hn
    have hNn : N ≤ n := by
      have hNC : (N : ℝ) ≤ Cα := by
        exact le_trans
          (le_trans (le_max_right (50 * D : ℝ) N)
            (le_max_right B _))
          (le_max_right A _)
      exact_mod_cast le_trans hNC hn
    exact hNasym n hNn

theorem section5Parameters_D_pos {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α) :
    0 < P.D := by
  rw [P.D_eq]
  exact section5D_pos hα0 hαh

theorem section5Parameters_alphaD {α : ℝ}
    (hα0 : 0 < α) (P : Section5Parameters α) :
    3 ≤ α * P.D := by
  rw [P.D_eq]
  exact alpha_mul_section5D_ge_three hα0

/-- The first lower bound on Cα in the power form actually used by union bounds. -/
theorem section5_Calpha_power {α : ℝ}
    (hα0 : 0 < α) (P : Section5Parameters α) :
    (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) ≤ P.Cα ^ α := by
  have hbase :=
    External.section5_rpow_threshold (D := P.D) hα0
  have hmono :=
    Real.rpow_le_rpow (by positivity) P.Cα_first (le_of_lt hα0)
  exact le_trans hbase hmono

end

end GrahamRearrangement
