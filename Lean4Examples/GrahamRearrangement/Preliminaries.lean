import Lean4Examples.GrahamRearrangement.Introduction
import Lean4Examples.GrahamRearrangement.External
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.Taylor

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 2: Preliminaries

This module follows Section 2 of the paper.  The only axiomatized ingredients used
here are the standard external tools isolated in `External.lean`: finite
Cauchy--Schwarz/Taylor facts and Cauchy--Davenport.
-/

noncomputable section

/-- The paper's distance `‖y‖_ℤ` to the nearest integer. -/
def distToInt (y : ℝ) : ℝ :=
  min (Int.fract y) (1 - Int.fract y)

theorem distToInt_eq_abs_sub_round (y : ℝ) :
    distToInt y = |y - (round y : ℝ)| := by
  symm
  simpa [distToInt] using (abs_sub_round_eq_min y)

theorem distToInt_nonneg (y : ℝ) : 0 ≤ distToInt y := by
  rw [distToInt_eq_abs_sub_round]
  exact abs_nonneg _

theorem distToInt_le_half (y : ℝ) : distToInt y ≤ 1 / 2 := by
  rw [distToInt_eq_abs_sub_round]
  simpa using (abs_sub_round y)

theorem distToInt_le_abs_sub_int (y : ℝ) (z : ℤ) :
    distToInt y ≤ |y - (z : ℝ)| := by
  rw [distToInt_eq_abs_sub_round]
  exact round_le y z

theorem distToInt_add_int (y : ℝ) (z : ℤ) :
    distToInt (y + z) = distToInt y := by
  rw [distToInt_eq_abs_sub_round, distToInt_eq_abs_sub_round,
    round_add_intCast]
  congr 1
  ring

theorem abs_list_sum_le_sum_abs (xs : List ℝ) :
    |xs.sum| ≤ (xs.map |·|).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons]
      exact le_trans (abs_add x xs.sum)
        (add_le_add_left ih |x|)

theorem cauchySchwarz_list (xs : List ℝ) :
    xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => x ^ 2).sum := by
  have h :=
    Multiset.sq_sum_le_card_mul_sum_sq
      (s := (↑xs : Multiset ℝ))
  simpa using h

/-- The nearest-integer triangle step in the proof of Fact 2.1. -/
theorem distToInt_sum_le (ys : List ℝ) :
    distToInt ys.sum ≤ (ys.map distToInt).sum := by
  let z : ℤ := (ys.map round).sum
  have hround :
      distToInt ys.sum ≤ |ys.sum - (z : ℝ)| :=
    distToInt_le_abs_sub_int ys.sum z
  have hrewrite :
      ys.sum - (z : ℝ) =
        (ys.map fun y => y - (round y : ℝ)).sum := by
    induction ys with
    | nil => simp [z]
    | cons y ys ih =>
        simp [z, ih]
        ring
  rw [hrewrite] at hround
  have habs :=
    abs_list_sum_le_sum_abs
      (ys.map fun y => y - (round y : ℝ))
  have hterm :
      ((ys.map fun y => y - (round y : ℝ)).map |·|) =
        ys.map distToInt := by
    apply List.map_congr_left
    intro y hy
    simp [distToInt_eq_abs_sub_round]
  rw [hterm] at habs
  exact le_trans hround habs

/-- Fact 2.1, following the paper: choose nearest integers, use the triangle
inequality, and then Cauchy--Schwarz. -/
theorem fact2_1 (ys : List ℝ) :
    distToInt ys.sum ^ 2 ≤
      (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
  have htri := distToInt_sum_le ys
  have hnonneg : 0 ≤ (ys.map distToInt).sum := by
    exact List.sum_nonneg fun y hy => distToInt_nonneg y
  have hsq :
      distToInt ys.sum ^ 2 ≤ ((ys.map distToInt).sum) ^ 2 := by
    nlinarith [distToInt_nonneg ys.sum]
  exact le_trans hsq
    (by
      simpa [List.map_map, Function.comp_def] using
        cauchySchwarz_list (ys.map distToInt))

/-- The exact third-order Lagrange remainder formula used for the lower
inequality in Fact 2.2. -/
theorem cos_two_pi_taylor3 {y : ℝ} (hy0 : 0 ≤ y) :
    ∃ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.cos (2 * Real.pi * y) =
        1 - ((2 * Real.pi) ^ 2 / 2) * y ^ 2 +
          ((2 * Real.pi) ^ 3 * Real.sin (2 * Real.pi * ξ) / 6) * y ^ 3 := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hf :
      ContDiffOn ℝ (3 : ℕ∞)
        (fun u : ℝ => Real.cos (2 * Real.pi * u))
        (Set.uIcc 0 y) := by
    fun_prop
  obtain ⟨ξ,hξ,hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun u : ℝ => Real.cos (2 * Real.pi * u))
      (x := y) (x₀ := 0) (n := 2) hy.symm hf
  refine ⟨ξ, ?_, ?_⟩
  · simpa [Set.uIoo_of_le hy0] using hξ
  · have hξ' : ξ ∈ Set.Icc (0 : ℝ) y := by
      simpa [Set.uIoo_of_le hy0] using hξ
    -- Simplifying the Taylor polynomial and the third iterated derivative
    -- gives exactly the formula displayed in the paper.
    simpa [taylorWithinEval, taylorWithin, taylorCoeffWithin,
      iteratedDerivWithin, hξ', Nat.factorial] using hTaylor

/-- The fourth-order Lagrange remainder formula used for the upper inequality
in Fact 2.2. -/
theorem cos_two_pi_taylor4 {y : ℝ} (hy0 : 0 ≤ y) :
    ∃ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.cos (2 * Real.pi * y) =
        1 - ((2 * Real.pi) ^ 2 / 2) * y ^ 2 +
          ((2 * Real.pi) ^ 4 * Real.cos (2 * Real.pi * ξ) / 24) * y ^ 4 := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hf :
      ContDiffOn ℝ (4 : ℕ∞)
        (fun u : ℝ => Real.cos (2 * Real.pi * u))
        (Set.uIcc 0 y) := by
    fun_prop
  obtain ⟨ξ,hξ,hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun u : ℝ => Real.cos (2 * Real.pi * u))
      (x := y) (x₀ := 0) (n := 3) hy.symm hf
  refine ⟨ξ, ?_, ?_⟩
  · simpa [Set.uIoo_of_le hy0] using hξ
  · have hξ' : ξ ∈ Set.Icc (0 : ℝ) y := by
      simpa [Set.uIoo_of_le hy0] using hξ
    simpa [taylorWithinEval, taylorWithin, taylorCoeffWithin,
      iteratedDerivWithin, hξ', Nat.factorial] using hTaylor

theorem cos_nearest_integer_reduction (y : ℝ) :
    Real.cos (2 * Real.pi * y) =
      Real.cos (2 * Real.pi * distToInt y) := by
  let z := round y
  have hperiod :
      Real.cos (2 * Real.pi * y) =
        Real.cos (2 * Real.pi * (y - (z : ℝ))) := by
    have h :=
      Real.cos_add_int_mul_two_pi
        (2 * Real.pi * (y - (z : ℝ))) z
    convert h.symm using 1 <;> ring
  rw [hperiod, distToInt_eq_abs_sub_round]
  have habs :
      |2 * Real.pi * (y - (z : ℝ))| =
        2 * Real.pi * |y - (z : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.two_pos,
      abs_of_pos Real.pi_pos]
  rw [← Real.cos_abs (2 * Real.pi * (y - (z : ℝ))), habs]

/-- Fact 2.2. The proof follows the two Taylor expansions in the paper. -/
theorem fact2_2 (y : ℝ) :
    1 - 20 * distToInt y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * distToInt y ^ 2 := by
  let d := distToInt y
  have hd0 : 0 ≤ d := distToInt_nonneg y
  have hdh : d ≤ 1 / 2 := distToInt_le_half y
  rw [cos_nearest_integer_reduction]
  constructor
  · obtain ⟨ξ,hξ,hTaylor⟩ := cos_two_pi_taylor3 hd0
    have hsin : 0 ≤ Real.sin (2 * Real.pi * ξ) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · have hξle := hξ.2
        nlinarith [Real.pi_pos]
    have hpi : (2 * Real.pi) ^ 2 / 2 ≤ 20 := by
      have hpib := Real.pi_le_four
      nlinarith [Real.pi_pos]
    rw [hTaylor]
    nlinarith
  · obtain ⟨ξ,hξ,hTaylor⟩ := cos_two_pi_taylor4 hd0
    have hcos : Real.cos (2 * Real.pi * ξ) ≤ 1 :=
      Real.cos_le_one _
    have hpib := Real.pi_le_four
    rw [hTaylor]
    have hquart :
        ((2 * Real.pi) ^ 4 / 24) * d ^ 4
          ≤ (((2 * Real.pi) ^ 4 / 24) * (1 / 2) ^ 2) * d ^ 2 := by
      have hd2 : d ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
      positivity
    have hnum :
        -((2 * Real.pi) ^ 2 / 2) +
          ((2 * Real.pi) ^ 4 / 24) * (1 / 2 : ℝ) ^ 2 ≤ -2 := by
      nlinarith [Real.two_le_pi, Real.pi_le_four]
    nlinarith

/-- The paper's `‖x‖ₚ`, written using the canonical representative. -/
def zmodNorm {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  distToInt ((x.val : ℝ) / (p : ℝ))

theorem zmodNorm_nonneg {p : ℕ} [NeZero p] (x : ZMod p) :
    0 ≤ zmodNorm x := distToInt_nonneg _

theorem zmodNorm_le_half {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm x ≤ 1 / 2 := distToInt_le_half _

theorem zmodNorm_neg {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm (-x) = zmodNorm x := by
  unfold zmodNorm
  have hrepr :
      ∃ z : ℤ,
        ((((-x).val : ℝ) / p)) =
          -((x.val : ℝ) / p) + z := by
    have hcast :
        ((((-x).val : ℤ) : ZMod p)) = -x := by simp
    have hcastx :
        (((x.val : ℤ) : ZMod p)) = x := by simp
    have hmod :
        ∃ q : ℤ,
          ((-x).val : ℤ) = -(x.val : ℤ) + (p : ℤ) * q := by
      have hz :=
        (ZMod.intCast_eq_iff p ((-x).val : ℤ) (-x)).1 hcast
      rcases hz with ⟨q,hq⟩
      refine ⟨q,?_⟩
      linarith
    rcases hmod with ⟨q,hq⟩
    refine ⟨q,?_⟩
    have hp : (0 : ℝ) < p := by
      exact_mod_cast (NeZero.pos p)
    field_simp
    exact_mod_cast hq
  rcases hrepr with ⟨z,hz⟩
  rw [hz, distToInt_add_int]
  rw [distToInt_eq_abs_sub_round, distToInt_eq_abs_sub_round]
  have hround := round_neg ((x.val : ℝ) / p)
  simp [hround, abs_neg]

theorem representative_sum_shift {p : ℕ} [NeZero p]
    (xs : List (ZMod p)) :
    ∃ q : ℤ,
      (xs.map fun x => (x.val : ℤ)).sum =
        ((xs.sum).val : ℤ) + (p : ℤ) * q := by
  have hcast :
      (((xs.map fun x => (x.val : ℤ)).sum : ℤ) : ZMod p) = xs.sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp [ih]
  exact (ZMod.intCast_eq_iff p
    ((xs.map fun x => (x.val : ℤ)).sum) xs.sum).1 hcast

theorem distToInt_rep_sum_eq_zmodNorm {p : ℕ} [NeZero p]
    (xs : List (ZMod p)) :
    distToInt
        ((xs.map fun x => (x.val : ℝ) / (p : ℝ)).sum) =
      zmodNorm xs.sum := by
  rcases representative_sum_shift xs with ⟨q,hq⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast (NeZero.pos p)
  have hreal :
      (xs.map fun x => (x.val : ℝ) / (p : ℝ)).sum =
        ((xs.sum).val : ℝ) / p + q := by
    have hcast :
        (((xs.map fun x => (x.val : ℤ)).sum : ℤ) : ℝ) =
          ((xs.map fun x => (x.val : ℝ)).sum) := by simp
    field_simp
    exact_mod_cast hq
  rw [hreal, distToInt_add_int]
  rfl

/-- Fact 2.3, following the representative argument in the paper. -/
theorem fact2_3_general {p : ℕ} [NeZero p] (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum := by
  let ys := xs.map fun x => (x.val : ℝ) / (p : ℝ)
  have h := fact2_1 ys
  have hsum :
      distToInt ys.sum = zmodNorm xs.sum :=
    distToInt_rep_sum_eq_zmodNorm xs
  have hterm :
      ys.map (fun y => distToInt y ^ 2) =
        xs.map fun x => zmodNorm x ^ 2 := by
    simp [ys,zmodNorm,List.map_map,Function.comp_def]
  simpa [ys,hsum,hterm] using h

/-- Fact 2.3. -/
theorem fact2_3 {p : ℕ} [NeZero p] (hp : p.Prime) (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum :=
  fact2_3_general xs

/-- The `k`-fold sumset `kA` from Fact 2.4. -/
def kfoldSumset {p : ℕ} (A : Finset (ZMod p)) : ℕ → Finset (ZMod p)
  | 0 => {0}
  | k + 1 => kfoldSumset A k + A

@[simp] theorem kfoldSumset_zero {p : ℕ} (A : Finset (ZMod p)) :
    kfoldSumset A 0 = {0} := rfl

@[simp] theorem kfoldSumset_succ {p k : ℕ} (A : Finset (ZMod p)) :
    kfoldSumset A (k + 1) = kfoldSumset A k + A := rfl

/-- Membership in the k-fold sumset is equivalent to a sum of a length-k list
whose entries all lie in A. -/
theorem mem_kfoldSumset {p k : ℕ} [NeZero p]
    (A : Finset (ZMod p)) (x : ZMod p) :
    x ∈ kfoldSumset A k ↔
      ∃ xs : List (ZMod p),
        xs.length = k ∧ (∀ y ∈ xs, y ∈ A) ∧ xs.sum = x := by
  induction k with
  | zero =>
      simp [kfoldSumset]
  | succ k ih =>
      constructor
      · intro hx
        rw [kfoldSumset_succ] at hx
        rcases Finset.mem_add.1 hx with ⟨u, hu, a, ha, rfl⟩
        rcases (ih u).1 hu with ⟨xs, hlen, hmem, hsum⟩
        refine ⟨xs ++ [a], by simp [hlen], ?_, by simp [hsum]⟩
        intro y hy
        simp at hy
        rcases hy with hy | rfl
        · exact hmem y hy
        · exact ha
      · rintro ⟨xs, hlen, hmem, rfl⟩
        obtain ⟨ys, a, rfl⟩ :=
          List.exists_eq_append_cons_of_length_succ hlen
        rw [List.sum_append, List.sum_singleton, kfoldSumset_succ]
        exact Finset.mem_add.2
          ⟨ys.sum,
            (ih ys.sum).2
              ⟨ys, by simpa using hlen, by
                intro y hy
                exact hmem y (by simp [hy]), rfl⟩,
            a, hmem a (by simp), rfl⟩

theorem kfoldSumset_empty {p k : ℕ}
    (hk : 0 < k) :
    kfoldSumset (∅ : Finset (ZMod p)) k = ∅ := by
  cases k with
  | zero => omega
  | succ k => simp [kfoldSumset]

theorem univ_add_nonempty {p : ℕ} [NeZero p]
    {A : Finset (ZMod p)} (hA : A.Nonempty) :
    (Finset.univ : Finset (ZMod p)) + A = Finset.univ := by
  ext x
  simp only [Finset.mem_add, Finset.mem_univ, iff_true]
  rcases hA with ⟨a, ha⟩
  exact ⟨x - a, Finset.mem_univ _, a, ha, by simp⟩

/-- A proper k-fold sumset has every positive prefix proper. -/
theorem kfoldSumset_prefix_proper {p k : ℕ} [NeZero p]
    {A : Finset (ZMod p)} (hA : A.Nonempty)
    (hproper : kfoldSumset A (k + 1) ≠ Finset.univ) :
    kfoldSumset A k ≠ Finset.univ := by
  intro hk
  apply hproper
  rw [kfoldSumset_succ, hk, univ_add_nonempty hA]

/-- Fact 2.4, exactly as in the paper. The only external input is the ordinary
two-set Cauchy--Davenport theorem. -/
theorem fact2_4 {p k : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) (hk : 0 < k)
    (hproper : kfoldSumset A k ≠ Finset.univ) :
    (1 : ℤ) + (k : ℤ) * ((A.card : ℤ) - 1) ≤
      ((kfoldSumset A k).card : ℤ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hA : A.Nonempty
  · induction k with
    | zero => omega
    | succ k ih =>
        by_cases hk0 : k = 0
        · subst k
          simpa [kfoldSumset] using
            (show (1 : ℤ) + ((A.card : ℤ) - 1) ≤ A.card by omega)
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hprev :
              kfoldSumset A k ≠ Finset.univ :=
            kfoldSumset_prefix_proper hA hproper
          have hih := ih hkpos hprev
          letI : Fact p.Prime := ⟨hp⟩
          have hraw := ZMod.cauchy_davenport (kfoldSumset A k) A
          have hcd :
              ((kfoldSumset A k).card : ℤ) + (A.card : ℤ) - 1 ≤
                ((kfoldSumset A k + A).card : ℤ) := by
            have hcardp : (kfoldSumset A k + A).card < p := by
              simpa [Finset.card_lt_iff_ne_univ] using hproper
            exact_mod_cast (by
              have := hraw
              omega)
          rw [kfoldSumset_succ]
          rw [kfoldSumset_succ] at hproper
          linarith
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [kfoldSumset_empty hk]
    simp
    omega

/-- The paper's character `eₚ(x)=exp(2πix/p)`. -/
def ep (p : ℕ) [NeZero p] (x : ZMod p) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ))

theorem ep_eq_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    ep p x = ZMod.stdAddChar x := by
  have h := ZMod.stdAddChar_coe (N := p) (x.val : ℤ)
  simpa [ep, Complex.div_re, Complex.ofReal_natCast, mul_assoc,
    ZMod.natCast_zmod_val] using h.symm

/-- Fact 2.5. -/
theorem fact2_5 {p : ℕ} [NeZero p] (hp : p.Prime) (x : ZMod p) :
    (ep p x).re ≤ 1 - 2 * zmodNorm x ^ 2 := by
  rw [ep_eq_stdAddChar]
  have hre :
      (ZMod.stdAddChar x).re =
        Real.cos (2 * Real.pi * ((x.val : ℝ) / (p : ℝ))) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp]
    simp [Circle.exp, mul_assoc]
  rw [hre]
  simpa [zmodNorm] using
    (fact2_2 ((x.val : ℝ) / (p : ℝ))).2

/-- Finite-index form of Fact 2.3 used later. -/
theorem fact2_3_finset {p : ℕ} [NeZero p] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → ZMod p) :
    zmodNorm (∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, zmodNorm (f i) ^ 2 := by
  let xs := s.attach.toList.map fun i => f i.1
  have h := fact2_3_general xs
  simpa [xs] using h

end

end GrahamRearrangement
