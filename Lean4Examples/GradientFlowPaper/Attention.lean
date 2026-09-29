import Lean4Examples.GradientFlowPaper.MatrixFactorization

/-! ## Source module: GradientFlowPaper/Attention.lean -/


/-!
Proposition 18 and Appendix G.1: grouped-query attention, including MHSA when
k=1. Inputs quantify over ALL positive sequence lengths, as in Theorem 27.
No identifiability statement for one fixed sequence length is substituted.
-/

noncomputable section
open Set Function
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix

namespace GradientFlowPaper
namespace Attention


inductive Slot (k : ℕ)
  | query (i : Fin k)
  | key
  | value
  | output (i : Fin k)
  deriving DecidableEq, Fintype

abbrev Index (nG k D dh : ℕ) := Fin nG × Slot k × Fin D × Fin dh
abbrev Param (nG k D dh : ℕ) := Vec (Index nG k D dh)
abbrev Tokens (D : ℕ) := Σ L : ℕ+, Mat (L : ℕ) D

variable {nG k D dh : ℕ}

def Q (p : Param nG k D dh) (j : Fin nG) (i : Fin k) : Mat D dh :=
  fun a b => p (j, Slot.query i, a, b)

def K (p : Param nG k D dh) (j : Fin nG) : Mat D dh :=
  fun a b => p (j, Slot.key, a, b)

def V (p : Param nG k D dh) (j : Fin nG) : Mat D dh :=
  fun a b => p (j, Slot.value, a, b)

def O (p : Param nG k D dh) (j : Fin nG) (i : Fin k) : Mat D dh :=
  fun a b => p (j, Slot.output i, a, b)

def score (p : Param nG k D dh) (j : Fin nG) (i : Fin k) : Mat D D :=
  Q p j i * (K p j)ᵀ

def weight (p : Param nG k D dh) (j : Fin nG) (i : Fin k) : Mat D D :=
  V p j * (O p j i)ᵀ

/-- Row-wise softmax; this is not a softmax over the entire matrix. -/
def rowSoftmax {L : ℕ} (A : Mat L L) : Mat L L :=
  fun i j => Real.exp (A i j) / ∑ a, Real.exp (A i a)

def run {L : ℕ} (p : Param nG k D dh) (X : Mat L D) : Mat L D :=
  ∑ j, ∑ i,
    rowSoftmax (X * ((Real.sqrt (dh : ℝ))⁻¹ • score p j i) * Xᵀ) * X * weight p j i

/-- The output remembers its sequence length, allowing arbitrary losses on
variable-length outputs without assigning a fictitious norm to a sigma type. -/
def model (p : Param nG k D dh) (X : Tokens D) : Tokens D :=
  ⟨X.1, run p X.2⟩

def regular : Set (Param nG k D dh) :=
  {p | (∀ j i, FullColumnRank (Q p j i) ∧ FullColumnRank (K p j) ∧
      FullColumnRank (V p j) ∧ FullColumnRank (O p j i)) ∧
    Function.Injective (fun a : Fin nG × Fin k => score p a.1 a.2)}

/-- The two independent GL(dh) gauge factors in each group. -/
def gauge (s t : Fin nG → GL dh) (p : Param nG k D dh) : Param nG k D dh :=
  WithLp.toLp 2 (fun a =>
    match a.2.1 with
    | Slot.query i => (Q p a.1 i * (s a.1 : Mat dh dh)) a.2.2.1 a.2.2.2
    | Slot.key => (K p a.1 * ((s a.1)⁻¹ : GL dh).valᵀ) a.2.2.1 a.2.2.2
    | Slot.value => (V p a.1 * (t a.1 : Mat dh dh)) a.2.2.1 a.2.2.2
    | Slot.output i => (O p a.1 i * ((t a.1)⁻¹ : GL dh).valᵀ) a.2.2.1 a.2.2.2)

@[simp] lemma score_gauge (s t : Fin nG → GL dh) (p : Param nG k D dh)
    (j : Fin nG) (i : Fin k) : score (gauge s t p) j i = score p j i := by
  exact mul_invTranspose_invariant (Q p j i) (K p j) (s j)

@[simp] lemma weight_gauge (s t : Fin nG → GL dh) (p : Param nG k D dh)
    (j : Fin nG) (i : Fin k) : weight (gauge s t p) j i = weight p j i := by
  exact mul_invTranspose_invariant (V p j) (O p j i) (t j)

@[simp] theorem run_gauge {L : ℕ} (s t : Fin nG → GL dh)
    (p : Param nG k D dh) (X : Mat L D) : run (gauge s t p) X = run p X := by
  simp only [run, score_gauge, weight_gauge]

theorem gauge_functional (s t : Fin nG → GL dh) (p : Param nG k D dh) :
    FunctionalEquiv model (gauge s t p) p := by
  intro X
  simp only [model, run_gauge]


/-- The scalar bilinear form represented by a square matrix. -/
def bilinearValue {D : ℕ} (M : Mat D D)
    (u v : Fin D → ℝ) : ℝ :=
  ⟪Matrix.vecMul u M, v⟫_ℝ

lemma bilinearValue_sub {D : ℕ} (M N : Mat D D)
    (u v : Fin D → ℝ) :
    bilinearValue (M - N) u v =
      bilinearValue M u v - bilinearValue N u v := by
  simp [bilinearValue, Matrix.vecMul_sub, inner_sub_left]

/-- A nonzero matrix has a proper left-kernel: some row vector detects it. -/
lemma ker_vecMulLinear_ne_top {D : ℕ} {M : Mat D D} (hM : M ≠ 0) :
    LinearMap.ker (Matrix.vecMulLinear M) ≠ ⊤ := by
  intro htop
  apply hM
  ext i j
  have hi :
      (Pi.single i (1 : ℝ) : Fin D → ℝ) ∈
        LinearMap.ker (Matrix.vecMulLinear M) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hi
  have hij := congrFun hi j
  simpa [Matrix.vecMulLinear_apply, Matrix.vecMul, Pi.single_apply] using hij

/-- A nonzero vector defines a proper orthogonality hyperplane. -/
lemma ker_innerSL_ne_top {D : ℕ} {u : Fin D → ℝ} (hu : u ≠ 0) :
    LinearMap.ker (innerSL ℝ u).toLinearMap ≠ ⊤ := by
  intro htop
  have hu_mem :
      u ∈ LinearMap.ker (innerSL ℝ u).toLinearMap := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hu_mem
  have hz : ⟪u, u⟫_ℝ = 0 := by
    simpa using hu_mem
  rw [real_inner_self_eq_norm_sq] at hz
  exact hu (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Finite simultaneous separation for distinct bilinear forms.  This is
the bilinear specialization of Tran et al.'s Appendix Lemma A.3.  The proof
avoids algebraic-geometry machinery: first choose a row vector outside the
finitely many left kernels of `A i - A j`, then choose a column vector
outside the finitely many orthogonality hyperplanes of the resulting rows. -/
lemma exists_bilinear_separator
    {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (A : I → Mat D D) (hA : Function.Injective A) :
    ∃ u v : Fin D → ℝ,
      Function.Injective (fun i => bilinearValue (A i) u v) := by
  classical
  let P := {ij : I × I // ij.1 ≠ ij.2}
  let Krow : P → Submodule ℝ (Fin D → ℝ) := fun ij =>
    LinearMap.ker (Matrix.vecMulLinear (A ij.1.1 - A ij.1.2))
  have hKrow : ∀ ij : P, Krow ij ≠ ⊤ := by
    intro ij
    apply ker_vecMulLinear_ne_top
    exact sub_ne_zero.mpr (hA.ne ij.2)
  obtain ⟨u, hu⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top Krow hKrow
  have hrow :
      ∀ ij : P, Matrix.vecMul u (A ij.1.1 - A ij.1.2) ≠ 0 := by
    intro ij hzero
    apply hu ij
    rw [LinearMap.mem_ker]
    simpa [Krow, Matrix.vecMulLinear_apply] using hzero
  let Kcol : P → Submodule ℝ (Fin D → ℝ) := fun ij =>
    LinearMap.ker
      (innerSL ℝ (Matrix.vecMul u (A ij.1.1 - A ij.1.2))).toLinearMap
  have hKcol : ∀ ij : P, Kcol ij ≠ ⊤ := by
    intro ij
    exact ker_innerSL_ne_top (hrow ij)
  obtain ⟨v, hv⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top Kcol hKcol
  refine ⟨u, v, ?_⟩
  intro i j hij
  by_contra hne
  let ij : P := ⟨(i,j), hne⟩
  have hnonzero :
      bilinearValue (A i - A j) u v ≠ 0 := by
    have hnot := hv ij
    rw [LinearMap.mem_ker] at hnot
    simpa [Kcol, bilinearValue, ij] using hnot
  have hzero :
      bilinearValue (A i - A j) u v = 0 := by
    rw [bilinearValue_sub, sub_eq_zero]
    exact hij
  exact hnonzero hzero


/-- Common-denominator polynomial for a linear combination of the functions
`L ↦ 1 / (a i + L)`. -/
noncomputable def reciprocalCombinationPolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (a c : I → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (c i) *
    ∏ j in Finset.univ.erase i, (Polynomial.X + Polynomial.C (a j))

lemma eval_reciprocalCombinationPolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (a c : I → ℝ) (x : ℝ) :
    (reciprocalCombinationPolynomial a c).eval x =
      ∑ i, c i * ∏ j in Finset.univ.erase i, (x + a j) := by
  simp [reciprocalCombinationPolynomial]

/-- Distinct positive poles give linearly independent reciprocal functions
when sampled at all positive integer offsets.  This is the algebraic core
needed from Tran et al.'s Appendix Lemma A.4. -/
lemma reciprocal_functions_independent
    {I : Type*} [Fintype I] [DecidableEq I]
    (a c : I → ℝ) (ha : Function.Injective a)
    (hapos : ∀ i, 0 < a i)
    (hzero : ∀ L : ℕ+,
      ∑ i, c i / (a i + (L : ℕ : ℝ)) = 0) :
    ∀ i, c i = 0 := by
  classical
  let P : Polynomial ℝ := reciprocalCombinationPolynomial a c
  have hroot :
      ∀ n : ℕ, P.eval (n + 1 : ℝ) = 0 := by
    intro n
    let L : ℕ+ := ⟨n + 1, by omega⟩
    have hL := hzero L
    have hden : ∀ i : I, a i + (L : ℕ : ℝ) ≠ 0 := by
      intro i
      positivity
    have hmul := congrArg
      (fun z : ℝ => z * ∏ i : I, (a i + (L : ℕ : ℝ))) hL
    rw [zero_mul] at hmul
    have hcleared :
        (∑ i, c i * ∏ j in Finset.univ.erase i,
          ((L : ℕ : ℝ) + a j)) = 0 := by
      calc
        (∑ i, c i * ∏ j in Finset.univ.erase i,
            ((L : ℕ : ℝ) + a j))
            =
          (∑ i, c i / (a i + (L : ℕ : ℝ))) *
            ∏ i : I, (a i + (L : ℕ : ℝ)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.prod_eq_mul_prod_diff_singleton
                (Finset.mem_univ i)]
              field_simp [hden i]
              ring
        _ = 0 := hmul
    simpa [P, eval_reciprocalCombinationPolynomial, L, add_comm] using hcleared
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf :
        Set.Infinite (Set.range (fun n : ℕ => (n + 1 : ℝ))) :=
      Set.infinite_range_of_injective
        (fun _ _ h => by exact_mod_cast (add_left_cancel h))
    apply hinf.mono
    rintro x ⟨n, rfl⟩
    simpa [Polynomial.IsRoot, hroot n]
  intro k
  have heval := congrArg (fun Q : Polynomial ℝ => Q.eval (-a k)) hPzero
  have hprod_nonzero :
      ∏ j in Finset.univ.erase k, (-a k + a j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    exact sub_ne_zero.mpr (ha.ne hjk).symm
  have hisolate :
      P.eval (-a k) =
        c k * ∏ j in Finset.univ.erase k, (-a k + a j) := by
    rw [show P.eval (-a k) =
      ∑ i, c i * ∏ j in Finset.univ.erase i, (-a k + a j) by
        simp [P, eval_reciprocalCombinationPolynomial]]
    rw [Finset.sum_eq_single k]
    · rfl
    · intro i hi hik
      have hki : k ∈ Finset.univ.erase i := by
        simp [hik]
      rw [Finset.prod_eq_zero hki]
      simp
    · simp
  rw [hisolate, Polynomial.eval_zero] at heval
  exact (mul_eq_zero.mp heval).resolve_right hprod_nonzero


/-- Tran et al.'s special input: the first token is `x`, and the remaining
`L` tokens are all `x-z`. -/
def tranTestInput {D : ℕ} (L : ℕ+) (x z : Fin D → ℝ) :
    Mat ((L : ℕ) + 1) D :=
  fun i a => if i = 0 then x a else x a - z a

@[simp] lemma tranTestInput_zero {D : ℕ} (L : ℕ+)
    (x z : Fin D → ℝ) :
    tranTestInput L x z 0 = x := by
  ext a
  simp [tranTestInput]

@[simp] lemma tranTestInput_succ {D : ℕ} (L : ℕ+)
    (x z : Fin D → ℝ) (i : Fin (L : ℕ)) :
    tranTestInput L x z i.succ = x - z := by
  ext a
  simp [tranTestInput]

lemma tranTest_score_zero_zero {D : ℕ} (L : ℕ+)
    (A : Mat D D) (x z : Fin D → ℝ) :
    (tranTestInput L x z * A * (tranTestInput L x z)ᵀ) 0 0 =
      bilinearValue A x x := by
  simp [tranTestInput, bilinearValue, inner, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.vecMul]

lemma tranTest_score_zero_succ {D : ℕ} (L : ℕ+)
    (A : Mat D D) (x z : Fin D → ℝ) (i : Fin (L : ℕ)) :
    (tranTestInput L x z * A * (tranTestInput L x z)ᵀ) 0 i.succ =
      bilinearValue A x (x - z) := by
  simp [tranTestInput, bilinearValue, inner, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.vecMul]

lemma bilinearValue_sub_right {D : ℕ} (A : Mat D D)
    (x z : Fin D → ℝ) :
    bilinearValue A x (x - z) =
      bilinearValue A x x - bilinearValue A x z := by
  simp [bilinearValue, inner_sub_right]

/-- First row of one attention head on `tranTestInput`.  After factoring
the common exponential, the coefficient of the displacement `z` is
`exp(xAz)/(exp(xAz)+L)`. -/
lemma tranTest_head_firstRow
    {D : ℕ} (L : ℕ+) (A B : Mat D D)
    (x z : Fin D → ℝ) (b : Fin D) :
    (rowSoftmax
        (tranTestInput L x z * A * (tranTestInput L x z)ᵀ) *
      tranTestInput L x z * B) 0 b
      =
    (Matrix.vecMul (x - z) B) b +
      (Real.exp (bilinearValue A x z) /
        (Real.exp (bilinearValue A x z) + (L : ℕ : ℝ))) *
        (Matrix.vecMul z B) b := by
  let X := tranTestInput L x z
  let q := bilinearValue A x x
  let d := bilinearValue A x z
  have hden :
      (∑ a : Fin ((L : ℕ) + 1),
        Real.exp ((X * A * Xᵀ) 0 a))
        =
      Real.exp (q - d) *
        (Real.exp d + (L : ℕ : ℝ)) := by
    rw [Fin.sum_univ_succ]
    simp only [X, tranTest_score_zero_zero, tranTest_score_zero_succ]
    rw [bilinearValue_sub_right]
    simp [q, d, Real.exp_sub, Finset.sum_const, Nat.smul_one_eq_cast]
    field_simp [Real.exp_ne_zero]
    ring
  have hden_ne :
      Real.exp d + (L : ℕ : ℝ) ≠ 0 := by
    positivity
  rw [show
      (rowSoftmax (X * A * Xᵀ) * X * B) 0 b =
        ∑ i : Fin ((L : ℕ) + 1),
          rowSoftmax (X * A * Xᵀ) 0 i * (X * B) i b by
      simp [Matrix.mul_apply, Matrix.mul_assoc]]
  rw [Fin.sum_univ_succ]
  simp only [X, tranTestInput_zero, tranTestInput_succ]
  rw [show (X * B) 0 b = Matrix.vecMul x B b by
    simp [X, Matrix.mul_apply, Matrix.vecMul]]
  have hsucc :
      ∀ i : Fin (L : ℕ),
        rowSoftmax (X * A * Xᵀ) 0 i.succ =
          1 / (Real.exp d + (L : ℕ : ℝ)) := by
    intro i
    rw [rowSoftmax, hden]
    rw [tranTest_score_zero_succ]
    rw [bilinearValue_sub_right]
    simp [q, d, Real.exp_sub]
    field_simp [Real.exp_ne_zero, hden_ne]
  have hzeroWeight :
      rowSoftmax (X * A * Xᵀ) 0 0 =
        Real.exp d / (Real.exp d + (L : ℕ : ℝ)) := by
    rw [rowSoftmax, hden, tranTest_score_zero_zero]
    simp [q, d, Real.exp_sub]
    field_simp [Real.exp_ne_zero, hden_ne]
  rw [hzeroWeight]
  simp_rw [hsucc]
  have hXB :
      ∀ i : Fin (L : ℕ),
        (X * B) i.succ b = Matrix.vecMul (x - z) B b := by
    intro i
    simp [X, Matrix.mul_apply, Matrix.vecMul]
  simp_rw [hXB]
  simp [Finset.sum_const, Nat.smul_eq_mul]
  have hvec :
      Matrix.vecMul x B b =
        Matrix.vecMul (x - z) B b + Matrix.vecMul z B b := by
    simp [Matrix.vecMul, sub_add_cancel]
  rw [hvec]
  field_simp [hden_ne]
  ring

/-- Sequence length one forces the sum of all value matrices to vanish. -/
lemma sum_valueMatrices_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (B : I → Mat D D)
    (hzero : ∀ (L : ℕ+) (X : Mat (L : ℕ) D),
      (∑ i, rowSoftmax (X * (0 : Mat D D) * Xᵀ) * X * B i) = 0) :
    ∑ i, B i = 0 := by
  ext a b
  let X : Mat 1 D := fun _ j => if j = a then 1 else 0
  have h := congrFun₂ (hzero 1 X) 0 b
  simp [rowSoftmax, X, Matrix.mul_apply, Finset.sum_apply] at h
  simpa using h

/-- Tran et al. (2025a), Theorem 3.1, restated as Theorem 27 by
Nguyen--Montúfar.  It is explicitly external during Stage 1. -/
class HasTranAttentionIdentifiability : Prop where
  identifiability :
    ∀ {H D : ℕ}, 0 < D →
      ∀ (A B : Fin H → Mat D D), Function.Injective A →
      (∀ (L : ℕ+) (X : Mat (L : ℕ) D),
        (∑ i, rowSoftmax (X * A i * Xᵀ) * X * B i) = 0) →
      ∀ i, B i = 0

/-- Theorem 27 (the externally cited attention-head identifiability theorem). -/
theorem theorem27 [HasTranAttentionIdentifiability]
    {H D : ℕ} (hD : 0 < D)
    (A B : Fin H → Mat D D) (hdistinct : Function.Injective A)
    (hzero : ∀ (L : ℕ+) (X : Mat (L : ℕ) D),
      (∑ i, rowSoftmax (X * A i * Xᵀ) * X * B i) = 0) :
    ∀ i, B i = 0 :=
  HasTranAttentionIdentifiability.identifiability hD A B hdistinct hzero

/-- Reindex Theorem 27 by an arbitrary finite head type. -/
theorem theorem27_fintype [HasTranAttentionIdentifiability]
    {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ} (hD : 0 < D)
    (A B : I → Mat D D) (hdistinct : Function.Injective A)
    (hzero : ∀ (L : ℕ+) (X : Mat (L : ℕ) D),
      (∑ i, rowSoftmax (X * A i * Xᵀ) * X * B i) = 0) :
    ∀ i, B i = 0 := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfin := theorem27 hD (fun i => A (e i)) (fun i => B (e i))
    (hdistinct.comp e.injective) (by
      intro L X
      simpa [e, Equiv.sum_comp] using hzero L X)
  intro i
  simpa using hfin (e.symm i)

/-- Grouping lemma used in Appendix G.1, Step 1.  It is the finite
"combine equal attention matrices" step that is implicit in the prose proof. -/
theorem theorem27_matching [HasTranAttentionIdentifiability]
    {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ} (hD : 0 < D)
    (A B A' B' : I → Mat D D)
    (hA : Function.Injective A) (hA' : Function.Injective A')
    (hcross : ∀ i j, A i = A' j → i = j)
    (hB : ∀ i, B i ≠ 0) (hB' : ∀ i, B' i ≠ 0)
    (hzero : ∀ (L : ℕ+) (X : Mat (L : ℕ) D),
      (∑ i, rowSoftmax (X * A i * Xᵀ) * X * B i) -
        (∑ i, rowSoftmax (X * A' i * Xᵀ) * X * B' i) = 0) :
    ∀ i, A i = A' i ∧ B i = B' i := by
  classical
  let values : Finset (Mat D D) :=
    Finset.univ.image A ∪ Finset.univ.image A'
  let J := {M : Mat D D // M ∈ values}
  let C : J → Mat D D := fun M =>
    (∑ i with A i = M.1, B i) - (∑ i with A' i = M.1, B' i)
  have hgroup : ∀ (L : ℕ+) (X : Mat (L : ℕ) D),
      (∑ M : J, rowSoftmax (X * M.1 * Xᵀ) * X * C M) = 0 := by
    intro L X
    have hleft :
        (∑ M : J, rowSoftmax (X * M.1 * Xᵀ) * X *
          (∑ i with A i = M.1, B i)) =
          ∑ i, rowSoftmax (X * A i * Xᵀ) * X * B i := by
      classical
      simp [J, values, Finset.mul_sum, Finset.sum_filter, Finset.sum_sigma']
    have hright :
        (∑ M : J, rowSoftmax (X * M.1 * Xᵀ) * X *
          (∑ i with A' i = M.1, B' i)) =
          ∑ i, rowSoftmax (X * A' i * Xᵀ) * X * B' i := by
      classical
      simp [J, values, Finset.mul_sum, Finset.sum_filter, Finset.sum_sigma']
    rw [show (∑ M : J, rowSoftmax (X * M.1 * Xᵀ) * X * C M) =
      (∑ M : J, rowSoftmax (X * M.1 * Xᵀ) * X *
        (∑ i with A i = M.1, B i)) -
      (∑ M : J, rowSoftmax (X * M.1 * Xᵀ) * X *
        (∑ i with A' i = M.1, B' i)) by
          simp [C, Matrix.mul_sub, Finset.sum_sub_distrib]]
    simpa [hleft, hright] using hzero L X
  have hC : ∀ M : J, C M = 0 :=
    theorem27_fintype hD (fun M : J => M.1) C
      (fun M N h => Subtype.ext h) hgroup
  intro i
  have hmatch : A i = A' i := by
    by_contra hne
    let M : J := ⟨A i, by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hfirst : (∑ j with A j = M.1, B j) = B i := by
      rw [Finset.sum_eq_single i]
      · simp [M]
      · intro j _ hj hji
        exact (hj (hA (by simpa [M] using hji))).elim
      · simp
    have hsecond : (∑ j with A' j = M.1, B' j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i = j := hcross i j (by simpa [M] using hj)
      subst j
      exact (hne (by simpa [M] using hj)).elim
    have := hC M
    rw [C, hfirst, hsecond, sub_zero] at this
    exact hB i this
  refine ⟨hmatch, ?_⟩
  let M : J := ⟨A i, by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hfirst : (∑ j with A j = M.1, B j) = B i := by
    rw [Finset.sum_eq_single i]
    · simp [M]
    · intro j _ hj hji
      exact (hj (hA (by simpa [M] using hji))).elim
    · simp
  have hsecond : (∑ j with A' j = M.1, B' j) = B' i := by
    rw [Finset.sum_eq_single i]
    · simp [M, hmatch]
    · intro j _ hj hji
      have hij := hcross i j (by simpa [M] using hji.symm)
      exact (hj hij.symm).elim
    · simp
  have := hC M
  rw [C, hfirst, hsecond, sub_eq_zero] at this
  exact this

abbrev Head (nG k : ℕ) := Fin nG × Fin k

def scoreHead (p : Param nG k D dh) (a : Head nG k) : Mat D D :=
  score p a.1 a.2

def weightHead (p : Param nG k D dh) (a : Head nG k) : Mat D D :=
  weight p a.1 a.2

lemma fullColumnRank_open_preimage_Q (j : Fin nG) (i : Fin k) :
    IsOpen {p : Param nG k D dh | FullColumnRank (Q p j i)} := by
  have heq :
      {p : Param nG k D dh | FullColumnRank (Q p j i)} =
        {p | Matrix.det ((Q p j i)ᵀ * Q p j i) ≠ 0} := by
    ext p
    constructor
    · intro hp
      exact (Matrix.isUnit_iff_isUnit_det _).mp hp.gram_isUnit |>
        (isUnit_iff_ne_zero.mp)
    · intro hp
      have hgram : IsUnit ((Q p j i)ᵀ * Q p j i) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp)
      have hinjGram : Function.Injective (((Q p j i)ᵀ * Q p j i).mulVec) :=
        Matrix.mulVec_injective_of_isUnit hgram
      apply (Matrix.mulVec_injective_iff).mp
      intro x y hxy
      apply hinjGram
      simp [Matrix.mulVec_mulVec, hxy]
  rw [heq]
  exact isOpen_compl_singleton.preimage (by fun_prop)

lemma fullColumnRank_open_preimage_K (j : Fin nG) :
    IsOpen {p : Param nG k D dh | FullColumnRank (K p j)} := by
  simpa [K] using
    (fullColumnRank_open_preimage_Q (nG := nG) (k := 1) (D := D) (dh := dh)
      j (0 : Fin 1))

lemma fullColumnRank_open_preimage_V (j : Fin nG) :
    IsOpen {p : Param nG k D dh | FullColumnRank (V p j)} := by
  change IsOpen {p : Param nG k D dh |
    FullColumnRank (fun a b => p (j, Slot.value, a, b))}
  simpa only [] using
    (isOpen_ne_fun
      (by fun_prop : Continuous (fun p : Param nG k D dh =>
        Matrix.det (((V p j)ᵀ * V p j))))
      continuous_const)

lemma fullColumnRank_open_preimage_O (j : Fin nG) (i : Fin k) :
    IsOpen {p : Param nG k D dh | FullColumnRank (O p j i)} := by
  change IsOpen {p : Param nG k D dh |
    FullColumnRank (fun a b => p (j, Slot.output i, a, b))}
  simpa only [] using
    (isOpen_ne_fun
      (by fun_prop : Continuous (fun p : Param nG k D dh =>
        Matrix.det (((O p j i)ᵀ * O p j i))))
      continuous_const)

lemma weightHead_ne_zero (hh : 0 < dh) {p : Param nG k D dh}
    (hp : p ∈ regular) (a : Head nG k) : weightHead p a ≠ 0 := by
  intro hz
  have hV := (hp.1 a.1 a.2).2.2.1
  have hO := (hp.1 a.1 a.2).2.2.2
  have hgram := hO.gram_isUnit
  have hzero :
      V p a.1 * ((O p a.1 a.2)ᵀ * O p a.1 a.2) = 0 := by
    simpa [weightHead, weight, Matrix.mul_assoc] using
      congrArg (fun M => M * O p a.1 a.2) hz
  have hVzero : V p a.1 = 0 := by
    calc
      V p a.1 = V p a.1 * 1 := by simp
      _ = V p a.1 *
          (((O p a.1 a.2)ᵀ * O p a.1 a.2) *
            (((O p a.1 a.2)ᵀ * O p a.1 a.2)⁻¹)) := by
              simp [hgram]
      _ = 0 := by
        rw [← Matrix.mul_assoc, hzero, zero_mul]
  have hne := hV.ne_zero ⟨0, hh⟩
  simpa [hVzero] using hne


/-- A local neighborhood excludes head permutations by keeping distinct
score matrices in pairwise-disjoint balls (Appendix G.1, Step 1). -/
theorem local_product_identifiability [HasTranAttentionIdentifiability]
    (hg : 0 < nG) (hk : 0 < k)
    (hh : 0 < dh) (hd : dh ≤ D)
    {p₀ : Param nG k D dh} (hp₀ : p₀ ∈ regular) :
    ∃ U : Set (Param nG k D dh), IsOpen U ∧ p₀ ∈ U ∧ U ⊆ regular ∧
      ∀ p ∈ U, ∀ q ∈ U,
        FunctionalEquiv model p q ↔
          (∀ j i, score p j i = score q j i ∧ weight p j i = weight q j i) := by
  classical
  let U : Set (Param nG k D dh) :=
    regular ∩
      ⋂ a : Head nG k, ⋂ b : Head nG k,
        if h : a = b then Set.univ else
          {p | dist (scoreHead p a) (scoreHead p₀ a) <
            dist (scoreHead p₀ a) (scoreHead p₀ b) / 3}
  have hUopen : IsOpen U := by
    apply (by
      have hregopen : IsOpen (regular : Set (Param nG k D dh)) := by
        unfold regular
        apply IsOpen.and
        · apply isOpen_iInter_of_finite
          intro j
          apply isOpen_iInter_of_finite
          intro i
          exact (((fullColumnRank_open_preimage_Q (nG:=nG) (k:=k) (D:=D) (dh:=dh) j i)
            .inter (fullColumnRank_open_preimage_K (nG:=nG) (k:=k) (D:=D) (dh:=dh) j))
            .inter (fullColumnRank_open_preimage_V (nG:=nG) (k:=k) (D:=D) (dh:=dh) j))
            .inter (fullColumnRank_open_preimage_O (nG:=nG) (k:=k) (D:=D) (dh:=dh) j i)
        · apply isOpen_iInter_of_finite
          intro a
          apply isOpen_iInter_of_finite
          intro b
          by_cases hab : a = b
          · simp [hab]
          · exact isOpen_ne_fun (by fun_prop) (by fun_prop)
      exact hregopen.inter <|
        isOpen_iInter_of_finite fun a =>
          isOpen_iInter_of_finite fun b => by
            split_ifs with hab
            · exact isOpen_univ
            · exact isOpen_lt
                (continuous_dist.comp
                  ((by fun_prop).prod_mk continuous_const))
                continuous_const)
  have hpU : p₀ ∈ U := by
    refine ⟨hp₀, ?_⟩
    intro a
    intro b
    by_cases hab : a = b
    · simp [hab]
    · simp [hab]
      have hne : scoreHead p₀ a ≠ scoreHead p₀ b :=
        hp₀.2 hab
      have hpos : 0 < dist (scoreHead p₀ a) (scoreHead p₀ b) :=
        dist_pos.mpr hne
      linarith
  refine ⟨U, hUopen, hpU, fun p hp => hp.1, ?_⟩
  intro p hp q hq
  have hcross : ∀ a b : Head nG k,
      scoreHead p a = scoreHead q b → a = b := by
    intro a b he
    by_contra hab
    have hpa := hp.2 a b
    have hqb := hq.2 b a
    simp [hab] at hpa
    have hba : b ≠ a := Ne.symm hab
    simp [hba] at hqb
    have htri :
        dist (scoreHead p₀ a) (scoreHead p₀ b) ≤
          dist (scoreHead p₀ a) (scoreHead p a) +
          dist (scoreHead q b) (scoreHead p₀ b) := by
      simpa [he, dist_comm] using
        dist_triangle (scoreHead p₀ a) (scoreHead p a) (scoreHead p₀ b)
    linarith
  constructor
  · intro heq
    let scale : ℝ := (Real.sqrt (dh : ℝ))⁻¹
    have hscale : scale ≠ 0 := by
      exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity))
    have hD : 0 < D := lt_of_lt_of_le hh hd
    have hzero : ∀ (L : ℕ+) (X : Mat (L : ℕ) D),
        (∑ a : Head nG k,
          rowSoftmax (X * (scale • scoreHead p a) * Xᵀ) * X * weightHead p a) -
        (∑ a : Head nG k,
          rowSoftmax (X * (scale • scoreHead q a) * Xᵀ) * X * weightHead q a) = 0 := by
      intro L X
      have hout := congrArg Sigma.snd
        (heq ⟨(L : ℕ), X⟩)
      simpa [model, run, scoreHead, weightHead, scale,
        Finset.sum_product, sub_eq_zero] using hout
    have hpInj : Function.Injective (fun a : Head nG k => scale • scoreHead p a) := by
      intro a b h
      apply hp.1.2
      apply hscale.smul_left_cancel
      exact h
    have hqInj : Function.Injective (fun a : Head nG k => scale • scoreHead q a) := by
      intro a b h
      apply hq.1.2
      apply hscale.smul_left_cancel
      exact h
    have hcrossScaled : ∀ a b : Head nG k,
        scale • scoreHead p a = scale • scoreHead q b → a = b := by
      intro a b h
      apply hcross a b
      exact hscale.smul_left_cancel h
    have hm := theorem27_matching hD
      (fun a : Head nG k => scale • scoreHead p a) (weightHead p)
      (fun a : Head nG k => scale • scoreHead q a) (weightHead q)
      hpInj hqInj hcrossScaled
      (weightHead_ne_zero hh hp.1) (weightHead_ne_zero hh hq.1) hzero
    intro j i
    have hi := hm (j, i)
    refine ⟨?_, hi.2⟩
    exact hscale.smul_left_cancel hi.1
  · intro hprod X
    rcases X with ⟨L, X⟩
    apply Sigma.ext rfl
    simp only [model]
    congr 1
    simp only [run]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [(hprod j i).1, (hprod j i).2]

/-- Shared full-rank K and V force the per-head changes of basis to agree. -/
theorem gauge_of_equal_products (hk : 0 < k)
    {p q : Param nG k D dh} (hp : p ∈ regular) (hq : q ∈ regular)
    (he : ∀ j i, score p j i = score q j i ∧ weight p j i = weight q j i) :
    ∃ s t : Fin nG → GL dh, q = gauge s t p := by
  let i₀ : Fin k := ⟨0, hk⟩
  have hQK : ∀ j i, ∃ s : GL dh,
      Q q j i = Q p j i * (s : Mat dh dh) ∧
      K q j = K p j * ((s⁻¹ : GL dh) : Mat dh dh)ᵀ := by
    intro j i
    let pp : Factorization.Param D D dh :=
      Factorization.pack (Q p j i) (K p j)
    let qq : Factorization.Param D D dh :=
      Factorization.pack (Q q j i) (K q j)
    have hpp : pp ∈ Factorization.regular :=
      ⟨(hp.1 j i).1, (hp.1 j i).2.1⟩
    have hqq : qq ∈ Factorization.regular :=
      ⟨(hq.1 j i).1, (hq.1 j i).2.1⟩
    have hobs : Factorization.observation pp = Factorization.observation qq := by
      simpa [pp, qq, Factorization.observation, score] using (he j i).1
    obtain ⟨s, hs⟩ := (Factorization.fullRank_fiber hpp hqq).mp hobs
    refine ⟨s, ?_, ?_⟩
    · have := congrArg Factorization.U hs
      simpa [pp, qq, Factorization.gauge] using this
    · have := congrArg Factorization.V hs
      simpa [pp, qq, Factorization.gauge] using this
  have hVO : ∀ j i, ∃ t : GL dh,
      V q j = V p j * (t : Mat dh dh) ∧
      O q j i = O p j i * ((t⁻¹ : GL dh) : Mat dh dh)ᵀ := by
    intro j i
    let pp : Factorization.Param D D dh :=
      Factorization.pack (V p j) (O p j i)
    let qq : Factorization.Param D D dh :=
      Factorization.pack (V q j) (O q j i)
    have hpp : pp ∈ Factorization.regular :=
      ⟨(hp.1 j i).2.2.1, (hp.1 j i).2.2.2⟩
    have hqq : qq ∈ Factorization.regular :=
      ⟨(hq.1 j i).2.2.1, (hq.1 j i).2.2.2⟩
    have hobs : Factorization.observation pp = Factorization.observation qq := by
      simpa [pp, qq, Factorization.observation, weight] using (he j i).2
    obtain ⟨t, ht⟩ := (Factorization.fullRank_fiber hpp hqq).mp hobs
    refine ⟨t, ?_, ?_⟩
    · have := congrArg Factorization.U ht
      simpa [pp, qq, Factorization.gauge] using this
    · have := congrArg Factorization.V ht
      simpa [pp, qq, Factorization.gauge] using this
  choose s hsQ hsK using fun j => hQK j i₀
  choose t htV htO using fun j => hVO j i₀
  have hs_all : ∀ j i,
      Q q j i = Q p j i * (s j : Mat dh dh) ∧
      K q j = K p j * (((s j)⁻¹ : GL dh) : Mat dh dh)ᵀ := by
    intro j i
    obtain ⟨s', hQ', hK'⟩ := hQK j i
    have hcancel :
        (((s'⁻¹ : GL dh) : Mat dh dh)ᵀ) =
          (((s j)⁻¹ : GL dh) : Mat dh dh)ᵀ :=
      (hp.1 j i).2.1.mul_right_cancel (hK'.symm.trans (hsK j))
    have hs' : s' = s j := by
      apply inv_injective
      apply Units.ext
      have := congrArg Matrix.transpose hcancel
      simpa using this
    subst s'
    exact ⟨hQ', hK'⟩
  have ht_all : ∀ j i,
      V q j = V p j * (t j : Mat dh dh) ∧
      O q j i = O p j i * (((t j)⁻¹ : GL dh) : Mat dh dh)ᵀ := by
    intro j i
    obtain ⟨t', hV', hO'⟩ := hVO j i
    have hcancel : (t' : Mat dh dh) = (t j : Mat dh dh) :=
      (hp.1 j i).2.2.1.mul_right_cancel (hV'.symm.trans (htV j))
    have ht' : t' = t j := Units.ext hcancel
    subst t'
    exact ⟨hV', hO'⟩
  refine ⟨s, t, ?_⟩
  ext a
  rcases a with ⟨j, slot, x, y⟩
  cases slot with
  | query i =>
      simpa [gauge, Q] using congrFun₂ (hs_all j i).1 x y
  | key =>
      simpa [gauge, K] using congrFun₂ (hsK j) x y
  | value =>
      simpa [gauge, V] using congrFun₂ (htV j) x y
  | output i =>
      simpa [gauge, O] using congrFun₂ (ht_all j i).2 x y

/-- Proposition 18, the full local functional-equivalence characterization. -/
theorem proposition18_symmetries [HasTranAttentionIdentifiability]
    (hg : 0 < nG) (hk : 0 < k)
    (hh : 0 < dh) (hd : dh ≤ D)
    {p₀ : Param nG k D dh} (hp₀ : p₀ ∈ regular) :
    ∃ U : Set (Param nG k D dh), IsOpen U ∧ p₀ ∈ U ∧ U ⊆ regular ∧
      ∀ p ∈ U, ∀ q ∈ U,
        FunctionalEquiv model p q ↔ ∃ s t : Fin nG → GL dh, q = gauge s t p := by
  obtain ⟨U, hU, hpU, hsub, hident⟩ := local_product_identifiability hg hk hh hd hp₀
  refine ⟨U, hU, hpU, hsub, ?_⟩
  intro p hp q hq
  constructor
  · intro he
    exact gauge_of_equal_products hk (hsub hp) (hsub hq) ((hident p hp q hq).mp he)
  · rintro ⟨s, t, rfl⟩
    intro X
    exact (gauge_functional s t p X).symm

/-- The matrices in Proposition 18, retaining the sharing multiplicities. -/
def balanceQK (p : Param nG k D dh) (j : Fin nG) : Mat dh dh :=
  (∑ i, (Q p j i)ᵀ * Q p j i) - (K p j)ᵀ * K p j

def balanceVO (p : Param nG k D dh) (j : Fin nG) : Mat dh dh :=
  (V p j)ᵀ * V p j - ∑ i, (O p j i)ᵀ * O p j i

abbrev LawIndex (nG dh : ℕ) := Fin nG × Bool × Upper dh

def law (a : LawIndex nG dh) (p : Param nG k D dh) : ℝ :=
  if a.2.1 then balanceVO p a.1 a.2.2.1.1 a.2.2.1.2
  else balanceQK p a.1 a.2.2.1.1 a.2.2.1.2

/-- Stacking preserves the Euclidean/Frobenius metric and gives exactly the
Gram matrices used in the paper, with no averaging by the number of heads. -/
def stackedQ (p : Param nG k D dh) (j : Fin nG) :
    Matrix (Fin k × Fin D) (Fin dh) ℝ := fun a b => Q p j a.1 a.2 b

def stackedO (p : Param nG k D dh) (j : Fin nG) :
    Matrix (Fin k × Fin D) (Fin dh) ℝ := fun a b => O p j a.1 a.2 b

lemma stackedQ_gram (p : Param nG k D dh) (j : Fin nG) :
    (stackedQ p j)ᵀ * stackedQ p j = ∑ i, (Q p j i)ᵀ * Q p j i := by
  ext a b
  simp [stackedQ, Matrix.mul_apply, Fintype.sum_prod_type]

lemma stackedO_gram (p : Param nG k D dh) (j : Fin nG) :
    (stackedO p j)ᵀ * stackedO p j = ∑ i, (O p j i)ᵀ * O p j i := by
  ext a b
  simp [stackedO, Matrix.mul_apply, Fintype.sum_prod_type]

/-! ### Orthogonal regrouping into the 2*nG factorization blocks of Appendix G.1 -/

abbrev FactorBlock (nG : ℕ) := Fin nG × Bool

def factorIndex (k D dh : ℕ) : FactorBlock nG → Type
  | (_, false) => Factorization.Index (k * D) D dh
  | (_, true) => Factorization.Index D (k * D) dh

def attentionIndexEquiv :
    Index nG k D dh ≃ Sigma (factorIndex (nG := nG) k D dh) where
  toFun a :=
    match a.2.1 with
    | Slot.query i =>
        ⟨(a.1, false), Sum.inl (finProdFinEquiv (i, a.2.2.1), a.2.2.2)⟩
    | Slot.key =>
        ⟨(a.1, false), Sum.inr (a.2.2.1, a.2.2.2)⟩
    | Slot.value =>
        ⟨(a.1, true), Sum.inl (a.2.2.1, a.2.2.2)⟩
    | Slot.output i =>
        ⟨(a.1, true), Sum.inr (finProdFinEquiv (i, a.2.2.1), a.2.2.2)⟩
  invFun z :=
    match z.1.2, z.2 with
    | false, Sum.inl rb =>
        let ia := finProdFinEquiv.symm rb.1
        (z.1.1, Slot.query ia.1, ia.2, rb.2)
    | false, Sum.inr rb =>
        (z.1.1, Slot.key, rb.1, rb.2)
    | true, Sum.inl rb =>
        (z.1.1, Slot.value, rb.1, rb.2)
    | true, Sum.inr rb =>
        let ia := finProdFinEquiv.symm rb.1
        (z.1.1, Slot.output ia.1, ia.2, rb.2)
  left_inv := by
    rintro ⟨j, s, a, b⟩
    cases s <;> simp [factorIndex]
  right_inv := by
    rintro ⟨⟨j, b⟩, z⟩
    cases b <;> cases z <;>
      simp [factorIndex]

def reblockEquiv :
    Param nG k D dh ≃ₗᵢ[ℝ]
      Blocks.Total (factorIndex (nG := nG) k D dh) :=
  LinearIsometryEquiv.piLpCongrLeft
    (p := 2) (𝕜 := ℝ) (E := ℝ)
    (attentionIndexEquiv (nG := nG) (k := k) (D := D) (dh := dh))

def stackedQFin (p : Param nG k D dh) (j : Fin nG) : Mat (k * D) dh :=
  fun a b =>
    let ia := finProdFinEquiv.symm a
    Q p j ia.1 ia.2 b

def stackedOFin (p : Param nG k D dh) (j : Fin nG) : Mat (k * D) dh :=
  fun a b =>
    let ia := finProdFinEquiv.symm a
    O p j ia.1 ia.2 b

def qkBlock (p : Param nG k D dh) (j : Fin nG) :
    Factorization.Param (k * D) D dh :=
  Blocks.block (factorIndex (nG := nG) k D dh) (j, false)
    (reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh) p)

def voBlock (p : Param nG k D dh) (j : Fin nG) :
    Factorization.Param D (k * D) dh :=
  Blocks.block (factorIndex (nG := nG) k D dh) (j, true)
    (reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh) p)

@[simp] lemma qkBlock_U (p : Param nG k D dh) (j : Fin nG) :
    Factorization.U (qkBlock p j) = stackedQFin p j := by
  ext a b
  simp [qkBlock, reblockEquiv, stackedQFin, Blocks.block,
    attentionIndexEquiv, factorIndex]

@[simp] lemma qkBlock_V (p : Param nG k D dh) (j : Fin nG) :
    Factorization.V (qkBlock p j) = K p j := by
  ext a b
  simp [qkBlock, reblockEquiv, Blocks.block, attentionIndexEquiv, factorIndex, K]

@[simp] lemma voBlock_U (p : Param nG k D dh) (j : Fin nG) :
    Factorization.U (voBlock p j) = V p j := by
  ext a b
  simp [voBlock, reblockEquiv, Blocks.block, attentionIndexEquiv, factorIndex, V]

@[simp] lemma voBlock_V (p : Param nG k D dh) (j : Fin nG) :
    Factorization.V (voBlock p j) = stackedOFin p j := by
  ext a b
  simp [voBlock, reblockEquiv, stackedOFin, Blocks.block,
    attentionIndexEquiv, factorIndex]

def scoreStackFin (p : Param nG k D dh) (j : Fin nG) : Mat (k * D) D :=
  fun a b =>
    let ia := finProdFinEquiv.symm a
    score p j ia.1 ia.2 b

def weightStackFin (p : Param nG k D dh) (j : Fin nG) : Mat D (k * D) :=
  fun a b =>
    let ib := finProdFinEquiv.symm b
    weight p j ib.1 a ib.2

lemma qkBlock_observation (p : Param nG k D dh) (j : Fin nG) :
    Factorization.observation (qkBlock p j) = scoreStackFin p j := by
  ext a b
  let ia := finProdFinEquiv.symm a
  simp [Factorization.observation, qkBlock_U, qkBlock_V,
    stackedQFin, scoreStackFin, score, ia, Matrix.mul_apply]

lemma voBlock_observation (p : Param nG k D dh) (j : Fin nG) :
    Factorization.observation (voBlock p j) = weightStackFin p j := by
  ext a b
  let ib := finProdFinEquiv.symm b
  simp [Factorization.observation, voBlock_U, voBlock_V,
    stackedOFin, weightStackFin, weight, ib, Matrix.mul_apply]

lemma scoreStackFin_eq_iff (p q : Param nG k D dh) (j : Fin nG) :
    scoreStackFin p j = scoreStackFin q j ↔
      ∀ i, score p j i = score q j i := by
  constructor
  · intro h i
    ext a b
    have hab := congrFun₂ h (finProdFinEquiv (i,a)) b
    simpa [scoreStackFin] using hab
  · intro h
    ext a b
    let ia := finProdFinEquiv.symm a
    simpa [scoreStackFin, ia] using congrFun₂ (h ia.1) ia.2 b

lemma weightStackFin_eq_iff (p q : Param nG k D dh) (j : Fin nG) :
    weightStackFin p j = weightStackFin q j ↔
      ∀ i, weight p j i = weight q j i := by
  constructor
  · intro h i
    ext a b
    have hab := congrFun₂ h a (finProdFinEquiv (i,b))
    simpa [weightStackFin] using hab
  · intro h
    ext a b
    let ib := finProdFinEquiv.symm b
    simpa [weightStackFin, ib] using congrFun₂ (h ib.1) a ib.2


lemma stackedQFin_gram (p : Param nG k D dh) (j : Fin nG) :
    (stackedQFin p j)ᵀ * stackedQFin p j =
      ∑ i, (Q p j i)ᵀ * Q p j i := by
  ext a b
  simpa [stackedQFin, Matrix.mul_apply, finProdFinEquiv,
    Fintype.sum_prod_type] using congrFun₂ (stackedQ_gram p j) a b

lemma stackedOFin_gram (p : Param nG k D dh) (j : Fin nG) :
    (stackedOFin p j)ᵀ * stackedOFin p j =
      ∑ i, (O p j i)ᵀ * O p j i := by
  ext a b
  simpa [stackedOFin, Matrix.mul_apply, finProdFinEquiv,
    Fintype.sum_prod_type] using congrFun₂ (stackedO_gram p j) a b

lemma stackedQFin_fullColumnRank (hk : 0 < k) {p : Param nG k D dh}
    (hp : p ∈ regular) (j : Fin nG) :
    FullColumnRank (stackedQFin p j) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  let i0 : Fin k := ⟨0, hk⟩
  have hrow := congrArg
    (fun v : Fin (k * D) → ℝ => fun a : Fin D =>
      v (finProdFinEquiv (i0, a))) hc
  have hQ : (∑ x, c x • fun a : Fin D => Q p j i0 a x) = 0 := by
    ext a
    simpa [stackedQFin, Finset.sum_apply] using congrFun hrow a
  exact (Fintype.linearIndependent_iff.mp (hp.1 j i0).1 c hQ) b

lemma stackedOFin_fullColumnRank (hk : 0 < k) {p : Param nG k D dh}
    (hp : p ∈ regular) (j : Fin nG) :
    FullColumnRank (stackedOFin p j) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  let i0 : Fin k := ⟨0, hk⟩
  have hrow := congrArg
    (fun v : Fin (k * D) → ℝ => fun a : Fin D =>
      v (finProdFinEquiv (i0, a))) hc
  have hO : (∑ x, c x • fun a : Fin D => O p j i0 a x) = 0 := by
    ext a
    simpa [stackedOFin, Finset.sum_apply] using congrFun hrow a
  exact (Fintype.linearIndependent_iff.mp (hp.1 j i0).2.2.2 c hO) b

lemma qkBlock_regular (hk : 0 < k) {p : Param nG k D dh}
    (hp : p ∈ regular) (j : Fin nG) :
    qkBlock p j ∈ Factorization.regular :=
  ⟨stackedQFin_fullColumnRank hk hp j, (hp.1 j ⟨0, hk⟩).2.1⟩

lemma voBlock_regular (hk : 0 < k) {p : Param nG k D dh}
    (hp : p ∈ regular) (j : Fin nG) :
    voBlock p j ∈ Factorization.regular :=
  ⟨(hp.1 j ⟨0, hk⟩).2.2.1, stackedOFin_fullColumnRank hk hp j⟩

def blockModel :
    ∀ b : FactorBlock nG,
      Vec (factorIndex (nG := nG) k D dh b) → Unit →
        (match b.2 with
         | false => Mat (k * D) D
         | true => Mat D (k * D))
  | (_, false) => Factorization.model
  | (_, true) => Factorization.model

def blockLoss :
    ∀ b : FactorBlock nG,
      (match b.2 with
       | false => Mat (k * D) D
       | true => Mat D (k * D)) →
      (match b.2 with
       | false => Mat (k * D) D
       | true => Mat D (k * D)) → ℝ
  | (_, false) => Factorization.entrySquaredLoss
  | (_, true) => Factorization.entrySquaredLoss

lemma blockFunctionalEquiv_reblock
    (p q : Param nG k D dh) (b : FactorBlock nG) :
    FunctionalEquiv
      (blockModel (nG := nG) (k := k) (D := D) (dh := dh) b)
      (Blocks.block (factorIndex (nG := nG) k D dh) b
        (reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh) p))
      (Blocks.block (factorIndex (nG := nG) k D dh) b
        (reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh) q))
      ↔
      if b.2 then
        ∀ i, weight p b.1 i = weight q b.1 i
      else
        ∀ i, score p b.1 i = score q b.1 i := by
  rcases b with ⟨j,b⟩
  cases b
  · simp [blockModel, FunctionalEquiv, Factorization.model,
      qkBlock, qkBlock_observation, scoreStackFin_eq_iff]
  · simp [blockModel, FunctionalEquiv, Factorization.model,
      voBlock, voBlock_observation, weightStackFin_eq_iff]


def blockLaw :
    ∀ b : FactorBlock nG, Upper dh →
      Vec (factorIndex (nG := nG) k D dh b) → ℝ
  | (_, false) => Factorization.law
  | (_, true) => Factorization.law

def blockRegular :
    ∀ b : FactorBlock nG,
      Set (Vec (factorIndex (nG := nG) k D dh b))
  | (_, false) => Factorization.regular
  | (_, true) => Factorization.regular

lemma blockLoss_separates (b : FactorBlock nG) :
    SeparatesPredictions
      (blockLoss (nG := nG) (k := k) (D := D) (dh := dh) b) := by
  rcases b with ⟨j,b⟩
  cases b <;> exact Factorization.separates_entrySquaredLoss

lemma blockLoss_regular (b : FactorBlock nG) :
    RegularLossOn
      (blockRegular (nG := nG) (k := k) (D := D) (dh := dh) b)
      (sampleLoss
        (blockModel (nG := nG) (k := k) (D := D) (dh := dh) b)
        (blockLoss (nG := nG) (k := k) (D := D) (dh := dh) b)) := by
  rcases b with ⟨j,b⟩
  cases b <;> exact Factorization.squaredLoss_regular

lemma reblock_mem_blockRegular (hk : 0 < k)
    {p : Param nG k D dh} (hp : p ∈ regular)
    (b : FactorBlock nG) :
    Blocks.block (factorIndex (nG := nG) k D dh) b
      (reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh) p)
      ∈ blockRegular (nG := nG) (k := k) (D := D) (dh := dh) b := by
  rcases b with ⟨j,b⟩
  cases b
  · simpa [blockRegular, qkBlock] using qkBlock_regular hk hp j
  · simpa [blockRegular, voBlock] using voBlock_regular hk hp j

def lawIndexEquiv :
    LawIndex nG dh ≃ Sigma (fun _ : FactorBlock nG => Upper dh) where
  toFun a := ⟨(a.1, a.2.1), a.2.2⟩
  invFun a := (a.1.1, a.1.2, a.2)
  left_inv := by rintro ⟨j,b,a⟩; rfl
  right_inv := by rintro ⟨⟨j,b⟩,a⟩; rfl

lemma blockLaw_reblock (b : FactorBlock nG) (a : Upper dh)
    (p : Param nG k D dh) :
    blockLaw (nG := nG) (k := k) (D := D) (dh := dh) b a
      (Blocks.block (factorIndex (nG := nG) k D dh) b
        (reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh) p))
      =
    law (b.1, b.2, a) p := by
  rcases b with ⟨j, b⟩
  cases b <;>
    simp [blockLaw, law, Factorization.law, Factorization.balance,
      qkBlock, voBlock, qkBlock_U, qkBlock_V, voBlock_U, voBlock_V,
      stackedQFin_gram, stackedOFin_gram, balanceQK, balanceVO]


/-- The Step 2--3 reduction is isolated from the head-identifiability theorem.
It is an orthogonal regrouping/stacking argument, not an assumption that the
listed laws are already complete. -/
theorem completeness_from_product_identifiability
    (hg : 0 < nG) (hk : 0 < k) (hh : 0 < dh) (hd : dh ≤ D)
    {Y : Type*} (ell : Tokens D → Y → ℝ) (hsep : SeparatesPredictions ell)
    {U : Set (Param nG k D dh)} (hU : IsOpen U) (hUr : U ⊆ regular)
    (hL : RegularLossOn U (sampleLoss model ell))
    (hident : ∀ p ∈ U, ∀ q ∈ U, FunctionalEquiv model p q ↔
      (∀ j i, score p j i = score q j i ∧ weight p j i = weight q j i))
    {p₀ : Param nG k D dh} (hp₀ : p₀ ∈ U) :
    ∃ V : Set (Param nG k D dh), IsOpen V ∧ p₀ ∈ V ∧ V ⊆ U ∧
      CompleteLawsOn V (sampleLoss model ell) (law (k := k) (D := D)) := by
  classical
  let ι := factorIndex (nG := nG) k D dh
  let e := reblockEquiv (nG := nG) (k := k) (D := D) (dh := dh)
  let pB := e p₀

  /- Step 3 of Appendix G.1: apply Lemma 28 to every Q/K and V/O
     factorization block. -/
  have hlocal :
      ∀ b : FactorBlock nG,
        ∃ Ωb : Set (Vec (ι b)),
          IsOpen Ωb ∧ Blocks.block ι b pB ∈ Ωb ∧
          Ωb ⊆ blockRegular (nG := nG) (k := k) (D := D) (dh := dh) b ∧
          CompleteLawsOn Ωb
            (sampleLoss
              (blockModel (nG := nG) (k := k) (D := D) (dh := dh) b)
              (blockLoss (nG := nG) (k := k) (D := D) (dh := dh) b))
            (blockLaw (nG := nG) (k := k) (D := D) (dh := dh) b) := by
    intro b
    rcases b with ⟨j,b⟩
    cases b
    · have hpblock : qkBlock p₀ j ∈ Factorization.regular :=
        qkBlock_regular hk (hUr hp₀) j
      simpa [ι, pB, blockRegular, blockModel, blockLoss, blockLaw, qkBlock]
        using Factorization.lemma28
          (m := k * D) (n := D) (r := dh) hh
          (Factorization.entrySquaredLoss : Mat (k * D) D → Mat (k * D) D → ℝ)
          Factorization.separates_entrySquaredLoss
          Factorization.squaredLoss_regular hpblock
    · have hpblock : voBlock p₀ j ∈ Factorization.regular :=
        voBlock_regular hk (hUr hp₀) j
      simpa [ι, pB, blockRegular, blockModel, blockLoss, blockLaw, voBlock]
        using Factorization.lemma28
          (m := D) (n := k * D) (r := dh) hh
          (Factorization.entrySquaredLoss : Mat D (k * D) → Mat D (k * D) → ℝ)
          Factorization.separates_entrySquaredLoss
          Factorization.squaredLoss_regular hpblock
  choose Ωb hΩb hpΩb hΩbreg hcomplete using hlocal

  /- Shrink to a genuine product neighborhood which also lies inside the
     original attention neighborhood U. -/
  have heU : IsOpen (e '' U) :=
    e.toHomeomorph.isOpenMap U hU
  have hpBeU : pB ∈ e '' U := ⟨p₀, hp₀, rfl⟩
  obtain ⟨Box, hBoxOpen, hpBox, hBoxSub⟩ :=
    Blocks.exists_product_box ι heU hpBeU

  let W : ∀ b : FactorBlock nG, Set (Vec (ι b)) :=
    fun b => Ωb b ∩ Box b
  have hWopen : ∀ b, IsOpen (W b) :=
    fun b => (hΩb b).inter (hBoxOpen b)
  have hpW : ∀ b, Blocks.block ι b pB ∈ W b :=
    fun b => ⟨hpΩb b, hpBox b⟩
  have hWreg : ∀ b, W b ⊆
      blockRegular (nG := nG) (k := k) (D := D) (dh := dh) b :=
    fun b _ hx => hΩbreg b hx.1
  have hcompW : ∀ b,
      CompleteLawsOn (W b)
        (sampleLoss
          (blockModel (nG := nG) (k := k) (D := D) (dh := dh) b)
          (blockLoss (nG := nG) (k := k) (D := D) (dh := dh) b))
        (blockLaw (nG := nG) (k := k) (D := D) (dh := dh) b) :=
    fun b => (hcomplete b).mono (hWopen b) inter_subset_left
  have hregW : ∀ b,
      RegularLossOn (W b)
        (sampleLoss
          (blockModel (nG := nG) (k := k) (D := D) (dh := dh) b)
          (blockLoss (nG := nG) (k := k) (D := D) (dh := dh) b)) :=
    fun b => (blockLoss_regular (nG := nG) (k := k) (D := D) (dh := dh) b).mono
      (hWopen b) (hWreg b)
  have hsepW : ∀ b,
      SeparatesPredictions
        (blockLoss (nG := nG) (k := k) (D := D) (dh := dh) b) :=
    blockLoss_separates

  have hdomain_eU : Blocks.domain ι W ⊆ e '' U := by
    intro q hq
    apply hBoxSub
    intro b
    exact (hq b).2
  have hdomain_U : ∀ q ∈ Blocks.domain ι W, e.symm q ∈ U := by
    intro q hq
    rcases hdomain_eU hq with ⟨p,hp,rfl⟩
    simpa using hp

  let Gblk : Blocks.Total ι → Tokens D → Tokens D :=
    fun q x => model (e.symm q) x

  /- Step 2: the product identities from Step 1 are exactly compositional
     identifiability for the 2*nG factor blocks. -/
  have hCI :
      CompositionallyIdentifiable (U := W)
        (blockModel (nG := nG) (k := k) (D := D) (dh := dh)) Gblk := by
    intro q hq r hr
    let p := e.symm q
    let p' := e.symm r
    have hpU : p ∈ U := hdomain_U q hq
    have hp'U : p' ∈ U := hdomain_U r hr
    have hbase :
        FunctionalEquiv Gblk q r ↔ FunctionalEquiv model p p' := by
      rfl
    rw [hbase, hident p hpU p' hp'U]
    constructor
    · intro hprod b
      have hb :=
        blockFunctionalEquiv_reblock
          (nG := nG) (k := k) (D := D) (dh := dh) p p' b
      have hblockq :
          Blocks.block ι b q =
            Blocks.block ι b (e p) := by simp [p,e]
      have hblockr :
          Blocks.block ι b r =
            Blocks.block ι b (e p') := by simp [p',e]
      rw [hblockq, hblockr]
      apply hb.mpr
      by_cases hbool : b.2
      · simp [hbool]
        intro i
        exact (hprod b.1 i).2
      · simp [hbool]
        intro i
        exact (hprod b.1 i).1
    · intro hblocks j i
      have hqk := hblocks (j,false)
      have hvo := hblocks (j,true)
      have hqk' :=
        (blockFunctionalEquiv_reblock
          (nG := nG) (k := k) (D := D) (dh := dh) p p' (j,false)).mp <| by
            simpa [p,p',e] using hqk
      have hvo' :=
        (blockFunctionalEquiv_reblock
          (nG := nG) (k := k) (D := D) (dh := dh) p p' (j,true)).mp <| by
            simpa [p,p',e] using hvo
      exact ⟨by simpa using hqk' i, by simpa using hvo' i⟩

  have hLGblk :
      RegularLossOn (Blocks.domain ι W) (sampleLoss Gblk ell) := by
    have ht := hL.precomp_linearIsometryEquiv e
      (Blocks.open_domain ι hWopen) hdomain_U
    simpa [Gblk, sampleLoss] using ht

  have hblocksComplete :
      CompleteLawsOn (Blocks.domain ι W) (sampleLoss Gblk ell)
        (fun a : Sigma (fun _ : FactorBlock nG => Upper dh) =>
          Blocks.extendLaw ι a.1
            (blockLaw (nG := nG) (k := k) (D := D) (dh := dh) a.1 a.2)) :=
    theorem17_laws
      (U := W) hWopen
      (blockModel (nG := nG) (k := k) (D := D) (dh := dh))
      (blockLoss (nG := nG) (k := k) (D := D) (dh := dh))
      Gblk ell hregW hsepW hCI hLGblk hsep
      (blockLaw (nG := nG) (k := k) (D := D) (dh := dh)) hcompW

  /- Transport the block theorem back through the coordinate permutation and
     reindex Sigma((j,kind),a) as the paper's (j,kind,a). -/
  let Vset : Set (Param nG k D dh) := e.symm '' Blocks.domain ι W
  have hVopen : IsOpen Vset :=
    e.symm.toHomeomorph.isOpenMap _ (Blocks.open_domain ι hWopen)
  have hpV : p₀ ∈ Vset := by
    refine ⟨pB, ?_, by simp [pB,e]⟩
    exact hpW
  have hVU : Vset ⊆ U := by
    rintro p ⟨q,hq,rfl⟩
    exact hdomain_U q hq

  have hpull :=
    CompleteLawsOn.pullback_linearIsometryEquiv e hblocksComplete
  have hreindexed :=
    CompleteLawsOn.reindex
      (lawIndexEquiv (nG := nG) (dh := dh)) hpull
  refine ⟨Vset, hVopen, hpV, hVU, ?_⟩
  simpa [Vset, Gblk, Blocks.extendLaw, lawIndexEquiv,
    blockLaw_reblock, Function.comp_def] using hreindexed

/-- Proposition 18, completeness of the stated conservation laws. -/
theorem proposition18_laws
    [HasTranAttentionIdentifiability]
    (hg : 0 < nG) (hk : 0 < k)
    (hh : 0 < dh) (hd : dh ≤ D)
    {Y : Type*} (ell : Tokens D → Y → ℝ) (hsep : SeparatesPredictions ell)
    (hL : RegularLossOn (regular : Set (Param nG k D dh)) (sampleLoss model ell))
    {p₀ : Param nG k D dh} (hp₀ : p₀ ∈ regular) :
    ∃ U : Set (Param nG k D dh), IsOpen U ∧ p₀ ∈ U ∧ U ⊆ regular ∧      CompleteLawsOn U (sampleLoss model ell) (law (k := k) (D := D)) := by
  obtain ⟨U, hU, hpU, hsub, hident⟩ := local_product_identifiability hg hk hh hd hp₀
  obtain ⟨V, hV, hpV, hVU, hcomplete⟩ := completeness_from_product_identifiability
    hg hk hh hd ell hsep hU hsub (hL.mono hU hsub) hident hpU
  exact ⟨V, hV, hpV, fun _ hx => hsub (hVU hx), hcomplete⟩

/-- MHSA is precisely the one-query-per-group specialization. -/
abbrev mhsaModel {nH D dh : ℕ} : Param nH 1 D dh → Tokens D → Tokens D := model

end Attention
end GradientFlowPaper

end -- noncomputable section
