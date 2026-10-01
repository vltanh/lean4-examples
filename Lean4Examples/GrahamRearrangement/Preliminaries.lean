import Lean4Examples.GrahamRearrangement.Introduction

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 2: Preliminaries

Facts 2.1--2.5 and the elementary/intrinsic formulations already present in the
formalization are colocated here.
-/

section Preliminaries

/-- Distance from a real number to the nearest integer.

For a real number with fractional part in `[0,1)`, the nearest integer is either
its floor or its ceiling, hence this minimum.
-/
noncomputable def distToInt (y : ℝ) : ℝ :=
  min (Int.fract y) (1 - Int.fract y)

/-- The paper's `‖x‖ₚ`, using the canonical representative of `x : ZMod p`. -/
noncomputable def zmodNorm {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  distToInt ((x.val : ℝ) / (p : ℝ))

/-- The additive character `eₚ(x) = exp(2π i x / p)`. -/
noncomputable def ep (p : ℕ) [NeZero p] (x : ZMod p) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ))

/-- Fact 2.1. -/
theorem fact2_1 (ys : List ℝ) :
    distToInt ys.sum ^ 2 ≤
      (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
  sorry

/-- Fact 2.2. -/
theorem fact2_2 (y : ℝ) :
    1 - 20 * distToInt y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * distToInt y ^ 2 := by
  sorry

/-- Fact 2.3. -/
theorem fact2_3 {p : ℕ} [NeZero p] (hp : p.Prime) (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum := by
  sorry

/-- The `k`-fold sumset used in Fact 2.4. -/
def kfoldSumset {p : ℕ} (A : Finset (ZMod p)) : ℕ → Finset (ZMod p)
  | 0 => {0}
  | k + 1 => kfoldSumset A k + A

/-- Fact 2.4, the repeated Cauchy--Davenport consequence. -/
theorem fact2_4 {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : 0 < k)
    {A : Finset (ZMod p)} (hA : A.Nonempty)
    (hproper : kfoldSumset A k ≠ Finset.univ) :
    1 + k * (A.card - 1) ≤ (kfoldSumset A k).card := by
  sorry

/-- Fact 2.5. -/
theorem fact2_5 {p : ℕ} [NeZero p] (hp : p.Prime) (x : ZMod p) :
    (ep p x).re ≤ 1 - 2 * zmodNorm x ^ 2 := by
  sorry

end Preliminaries

-- Intrinsic/mathlib-oriented formulations and elementary estimates.
section ElementaryEstimates

/-- The square-of-the-triangle-inequality estimate used in Fact 2.1. -/
theorem norm_sum_sq_le_card_mul_sum_sq
    {E ι : Type*} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have htri : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
    norm_sum_le _ _
  have hleft : 0 ≤ ‖∑ i ∈ s, f i‖ := norm_nonneg _
  have hright : 0 ≤ ∑ i ∈ s, ‖f i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      nlinarith
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
      simpa using
        (Finset.sq_sum_le_card_mul_sum_sq
          (s := s) (f := fun i => ‖f i‖))

/-- Distance to the nearest integer, implemented as the norm on `ℝ / ℤ`. -/
noncomputable def integerDistance (y : ℝ) : ℝ :=
  ‖(y : AddCircle (1 : ℝ))‖

theorem integerDistance_nonneg (y : ℝ) : 0 ≤ integerDistance y :=
  norm_nonneg _

theorem integerDistance_le_half (y : ℝ) : integerDistance y ≤ 1 / 2 := by
  simpa [integerDistance] using
    (AddCircle.norm_le_half_period (1 : ℝ) (by norm_num)
      (x := (y : AddCircle (1 : ℝ))))

/-- Fact 2.1 in the intrinsic `ℝ / ℤ` formulation. -/
theorem fact_2_1
    {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ)) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
  norm_sum_sq_le_card_mul_sum_sq s f

/-- The exact polynomial cosine estimate stated as Fact 2.2. -/
def Fact22Statement : Prop :=
  ∀ y : ℝ,
    1 - 20 * integerDistance y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * integerDistance y ^ 2

/-- Distance on `ℤ/pℤ` used by the paper, via the canonical embedding into `ℝ/ℤ`. -/
noncomputable def cyclicDistance {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  ‖ZMod.toAddCircle x‖

theorem cyclicDistance_nonneg {p : ℕ} [NeZero p] (x : ZMod p) :
    0 ≤ cyclicDistance x :=
  norm_nonneg _

/-- Fact 2.3, obtained by applying Fact 2.1 after `ZMod.toAddCircle`. -/
theorem fact_2_3 {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod p) :
    cyclicDistance (∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, cyclicDistance (f i) ^ 2 := by
  simpa [cyclicDistance, map_sum] using
    (norm_sum_sq_le_card_mul_sum_sq s (fun i => ZMod.toAddCircle (f i)))

/-- The two-set Cauchy--Davenport theorem already available in mathlib. -/
theorem cauchyDavenport {p : ℕ} (hp : p.Prime)
    {A B : Finset (ZMod p)} (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card :=
  ZMod.cauchy_davenport hp hA hB

/-- Iterated sumset notation for Fact 2.4. `kFoldSumset k A` is the set of
sums of `k` (not necessarily distinct) elements of `A`. -/
def kFoldSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] :
    ℕ → Finset G → Finset G
  | 0, _ => {0}
  | k + 1, A => kFoldSumset k A + A

/-- Fact 2.4, the iterated Cauchy--Davenport consequence used in the paper.

The paper only uses nonempty sets; that hypothesis also avoids the degenerate empty-set
corner case in the cardinality expression.
-/
def Fact24Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime),
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ (k : ℕ), 0 < k →
      ∀ A : Finset (ZMod p), A.Nonempty →
        kFoldSumset k A ≠ Finset.univ →
          1 + k * (A.card - 1) ≤ (kFoldSumset k A).card

/-- Fact 2.5, stated using mathlib's standard additive character on `ZMod p`. -/
def Fact25Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime),
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ x : ZMod p,
      (ZMod.stdAddChar x).re ≤ 1 - 2 * cyclicDistance x ^ 2

end ElementaryEstimates

end GrahamRearrangement
