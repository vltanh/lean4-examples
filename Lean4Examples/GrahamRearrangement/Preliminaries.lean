import Lean4Examples.GrahamRearrangement.Introduction
import Lean4Examples.GrahamRearrangement.External

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

theorem distToInt_nonneg (y : ℝ) : 0 ≤ distToInt y :=
  (External.fract_min_mem_half y).1

theorem distToInt_le_half (y : ℝ) : distToInt y ≤ 1 / 2 :=
  (External.fract_min_mem_half y).2

/-- Fact 2.1. -/
theorem fact2_1 (ys : List ℝ) :
    distToInt ys.sum ^ 2 ≤
      (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
  have htri : distToInt ys.sum ≤ (ys.map distToInt).sum := by
    simpa [distToInt] using External.distToInt_triangle ys
  have hsum : 0 ≤ (ys.map distToInt).sum := by
    exact List.sum_nonneg fun y hy => distToInt_nonneg y
  have hsq :
      distToInt ys.sum ^ 2 ≤ ((ys.map distToInt).sum) ^ 2 := by
    nlinarith [distToInt_nonneg ys.sum]
  calc
    distToInt ys.sum ^ 2 ≤ ((ys.map distToInt).sum) ^ 2 := hsq
    _ ≤ (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
      simpa [List.map_map, Function.comp_def] using
        External.cauchySchwarz_sq (ys.map distToInt)

/-- Fact 2.2. -/
theorem fact2_2 (y : ℝ) :
    1 - 20 * distToInt y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * distToInt y ^ 2 := by
  have hd0 : 0 ≤ distToInt y := distToInt_nonneg y
  have hdh : distToInt y ≤ 1 / 2 := distToInt_le_half y
  have hcos := External.cosine_nearest_integer_reduction y
  constructor
  · rw [hcos]
    exact External.cosine_taylor_lower hd0 hdh
  · rw [hcos]
    exact External.cosine_taylor_upper hd0 hdh

/-- The paper's `‖x‖ₚ`, written using the canonical representative. -/
def zmodNorm {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  distToInt ((x.val : ℝ) / (p : ℝ))

/-- Intrinsic version of the same norm, via `ℝ/ℤ`. -/
def cyclicDistance {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  ‖ZMod.toAddCircle x‖

theorem cyclicDistance_eq_zmodNorm {p : ℕ} [NeZero p] (x : ZMod p) :
    cyclicDistance x = zmodNorm x := by
  simpa [cyclicDistance, zmodNorm, distToInt] using
    External.zmod_addCircle_norm_eq x

theorem zmodNorm_nonneg {p : ℕ} [NeZero p] (x : ZMod p) :
    0 ≤ zmodNorm x := by
  rw [← cyclicDistance_eq_zmodNorm]
  exact norm_nonneg _

theorem zmodNorm_le_half {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm x ≤ 1 / 2 := by
  simpa [zmodNorm] using
    distToInt_le_half ((x.val : ℝ) / (p : ℝ))

/-- The norm inequality underlying Fact 2.3 does not require primality. -/
theorem fact2_3_general {p : ℕ} [NeZero p] (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum := by
  have h :=
    External.norm_list_sum_sq (xs.map fun x => ZMod.toAddCircle x)
  simpa [cyclicDistance_eq_zmodNorm, cyclicDistance, List.map_map,
    Function.comp_def] using h

/-- Fact 2.3. -/
theorem fact2_3 {p : ℕ} [NeZero p] (hp : p.Prime) (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum :=
  fact2_3_general xs

theorem zmodNorm_neg {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm (-x) = zmodNorm x := by
  rw [← cyclicDistance_eq_zmodNorm, ← cyclicDistance_eq_zmodNorm]
  simp [cyclicDistance]

/-- The `k`-fold sumset `kA` from Fact 2.4. -/
def kfoldSumset {p : ℕ} (A : Finset (ZMod p)) (k : ℕ) : Finset (ZMod p) :=
  (List.replicate k A).foldl (· + ·) {0}

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
      simp only [kfoldSumset, List.replicate_succ, List.foldl_cons]
      constructor
      · intro hx
        rcases Finset.mem_add.1 hx with ⟨u, hu, a, ha, rfl⟩
        rcases (ih u).1 hu with ⟨xs, hlen, hmem, hsum⟩
        refine ⟨xs ++ [a], by simp [hlen], ?_, by simp [hsum]⟩
        intro y hy
        simp at hy
        rcases hy with hy | rfl
        · exact hmem y hy
        · exact ha
      · rintro ⟨xs, hlen, hmem, rfl⟩
        have hne : xs ≠ [] := by simpa [hlen]
        obtain ⟨ys, a, rfl⟩ := List.exists_eq_append_cons_of_ne_nil hne
        have hyslen : ys.length = k := by simpa using hlen
        have hys : ys.sum ∈ kfoldSumset A k :=
          (ih ys.sum).2 ⟨ys, hyslen, by
            intro y hy
            exact hmem y (by simp [hy]), rfl⟩
        have ha : a ∈ A := hmem a (by simp)
        exact Finset.mem_add.2 ⟨ys.sum, hys, a, ha, by simp⟩

/-- Fact 2.4, stated in integer cardinalities so that the paper's formula also has
its literal meaning in the empty-set edge case. -/
theorem fact2_4 {p k : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) (hk : 0 < k)
    (hproper : kfoldSumset A k ≠ Finset.univ) :
    (1 : ℤ) + (k : ℤ) * ((A.card : ℤ) - 1) ≤
      ((kfoldSumset A k).card : ℤ) := by
  have h :=
    External.iteratedCauchyDavenportProper hp (List.replicate k A)
      (by simpa [kfoldSumset] using hproper)
  simp [kfoldSumset] at h
  linarith

/-- The paper's character `eₚ(x)=exp(2πix/p)`. -/
def ep (p : ℕ) [NeZero p] (x : ZMod p) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ))

theorem ep_eq_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    ep p x = ZMod.stdAddChar x :=
  External.zmod_exp_character_eq x

/-- Fact 2.5. -/
theorem fact2_5 {p : ℕ} [NeZero p] (hp : p.Prime) (x : ZMod p) :
    (ep p x).re ≤ 1 - 2 * zmodNorm x ^ 2 := by
  rw [ep_eq_stdAddChar, External.zmod_stdAddChar_re]
  simpa [zmodNorm] using
    (fact2_2 ((x.val : ℝ) / (p : ℝ))).2

/-- Intrinsic finite-index form of Fact 2.1, useful later. -/
theorem fact2_1_finset
    {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ)) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  simpa using
    Finset.sq_norm_sum_le_card_mul_sum_sq_norm s f

/-- Intrinsic finite-index form of Fact 2.3. -/
theorem fact2_3_finset {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod p) :
    zmodNorm (∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, zmodNorm (f i) ^ 2 := by
  rw [← cyclicDistance_eq_zmodNorm]
  have h := fact2_1_finset s (fun i => ZMod.toAddCircle (f i))
  simpa [cyclicDistance, cyclicDistance_eq_zmodNorm] using h

end

end GrahamRearrangement
