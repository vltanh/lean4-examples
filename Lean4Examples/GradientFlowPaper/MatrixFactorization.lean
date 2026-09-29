import Lean4Examples.GradientFlowPaper.Inheritance

/-! ## Source module: GradientFlowPaper/MatrixFactorization.lean -/


/-!
Matrix factorization background (Lemma 28), the Section 2.3 example, and
algebra used for attention and deep linear networks.

IMPORTANT CONVENTION: (U,V) ↦ (U S, V S^{-T}) is a RIGHT action of GL(r),
or equivalently a left action of its opposite group. The paper writes it
as a left action. We keep its formulas and state the correct composition order.
-/

noncomputable section
open Set Function
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix

namespace GradientFlowPaper

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev GL (n : ℕ) := (Mat n n)ˣ
abbrev Upper (r : ℕ) := {a : Fin r × Fin r // a.1 ≤ a.2}

/-- Full column rank, with no determinant shortcut for rectangular matrices. -/
def FullColumnRank {m r : ℕ} (A : Mat m r) : Prop :=
  LinearIndependent ℝ (fun j : Fin r => fun i : Fin m => A i j)

/-- A full-column-rank matrix is left cancellable for matrix multiplication.
This elementary lemma is used repeatedly when shared K/V factors force the
per-head changes of basis in Appendix G.1 to coincide. -/
lemma FullColumnRank.mul_right_cancel {m r n : ℕ} {A : Mat m r}
    (hA : FullColumnRank A) {B C : Mat r n} (h : A * B = A * C) : B = C := by
  ext i j
  have hcol : (fun k : Fin r => B k j - C k j) = 0 := by
    apply Fintype.linearIndependent_iff.mp hA
    ext a
    have ha := congrFun₂ h a j
    simp [Matrix.mul_apply] at ha ⊢
    linarith
  have hij := congrFun hcol i
  simpa using hij

lemma FullColumnRank.mulVec_injective {m r : ℕ} {A : Mat m r}
    (hA : FullColumnRank A) : Function.Injective A.mulVec := by
  exact (Matrix.mulVec_injective_iff).2 (by simpa [FullColumnRank] using hA)

lemma FullColumnRank.gram_isUnit {m r : ℕ} {A : Mat m r}
    (hA : FullColumnRank A) : IsUnit (Aᵀ * A) := by
  have hkerA : LinearMap.ker A.mulVecLin = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    simpa using hA.mulVec_injective
  have hkerGram : LinearMap.ker (Aᵀ * A).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self A, hkerA]
  have hinjGram : Function.Injective (Aᵀ * A).mulVec := by
    have hlinj : Function.Injective (Aᵀ * A).mulVecLin :=
      LinearMap.ker_eq_bot.mp hkerGram
    simpa using hlinj
  exact Matrix.linearIndependent_cols_iff_isUnit.mp
    ((Matrix.mulVec_injective_iff).mp hinjGram)

lemma fullColumnRank_iff_gram_isUnit {m r : ℕ} {A : Mat m r} :
    FullColumnRank A ↔ IsUnit (Aᵀ * A) := by
  constructor
  · exact FullColumnRank.gram_isUnit
  · intro hgram
    apply (Matrix.mulVec_injective_iff).mp
    intro x y hxy
    have hgramInj : Function.Injective (Aᵀ * A).mulVec :=
      Matrix.mulVec_injective_of_isUnit hgram
    apply hgramInj
    simpa [Matrix.mulVec_mulVec, hxy]

lemma isOpen_fullColumnRank {m r : ℕ} :
    IsOpen {A : Mat m r | FullColumnRank A} := by
  rw [show {A : Mat m r | FullColumnRank A} =
    {A | Matrix.det (Aᵀ * A) ≠ 0} by
      ext A
      rw [fullColumnRank_iff_gram_isUnit,
        Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]]
  exact isOpen_ne_fun (by fun_prop) continuous_const

lemma mul_invTranspose_invariant {m n r : ℕ}
    (U : Mat m r) (V : Mat n r) (s : GL r) :
    (U * (s : Mat r r)) * (V * ((s⁻¹ : GL r) : Mat r r)ᵀ)ᵀ = U * Vᵀ := by
  have hs : (s : Mat r r) * ((s⁻¹ : GL r) : Mat r r) = 1 :=
    Units.val_mul_val_inv s
  calc
    (U * (s : Mat r r)) * (V * ((s⁻¹ : GL r) : Mat r r)ᵀ)ᵀ
        = ((U * (s : Mat r r)) * ((s⁻¹ : GL r) : Mat r r)) * Vᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
    _ = U * Vᵀ := by simp [Matrix.mul_assoc, hs]

namespace Factorization

abbrev Index (m n r : ℕ) := (Fin m × Fin r) ⊕ (Fin n × Fin r)
abbrev Param (m n r : ℕ) := Vec (Index m n r)

def U {m n r : ℕ} (p : Param m n r) : Mat m r :=
  fun i a => p (Sum.inl (i, a))

def V {m n r : ℕ} (p : Param m n r) : Mat n r :=
  fun i a => p (Sum.inr (i, a))

def pack {m n r : ℕ} (u : Mat m r) (v : Mat n r) : Param m n r :=
  WithLp.toLp 2 (Sum.elim (fun a => u a.1 a.2) (fun a => v a.1 a.2))

@[simp] lemma U_pack {m n r : ℕ} (u : Mat m r) (v : Mat n r) :
    U (pack u v) = u := rfl
@[simp] lemma V_pack {m n r : ℕ} (u : Mat m r) (v : Mat n r) :
    V (pack u v) = v := rfl

@[simp] lemma pack_U_V {m n r : ℕ} (p : Param m n r) : pack (U p) (V p) = p := by
  ext a
  cases a <;> rfl

def observation {m n r : ℕ} (p : Param m n r) : Mat m n := U p * (V p)ᵀ

def model {m n r : ℕ} (p : Param m n r) (_ : Unit) : Mat m n := observation p

def regular {m n r : ℕ} : Set (Param m n r) :=
  {p | FullColumnRank (U p) ∧ FullColumnRank (V p)}

theorem regular_isOpen {m n r : ℕ} :
    IsOpen (regular : Set (Param m n r)) := by
  unfold regular
  exact (isOpen_fullColumnRank.preimage (by fun_prop)).and
    (isOpen_fullColumnRank.preimage (by fun_prop))

def entrySquaredLoss {m n : ℕ} (z y : Mat m n) : ℝ :=
  ∑ i, ∑ j, (z i j - y i j)^2

theorem separates_entrySquaredLoss {m n : ℕ} :
    SeparatesPredictions (entrySquaredLoss : Mat m n → Mat m n → ℝ) := by
  intro z z'
  constructor
  · intro h
    ext i j
    have hz := h z' 
    have hnonneg : ∀ a b, 0 ≤ (z a b - z' a b)^2 := by
      intro a b
      positivity
    have hsum : (∑ a, ∑ b, (z a b - z' a b)^2) = 0 := by
      simpa [entrySquaredLoss] using hz
    have hij : (z i j - z' i j)^2 = 0 := by
      exact Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => Finset.sum_nonneg fun b _ => hnonneg a b) |>.mp hsum i
        (Finset.mem_univ i) |>
        Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg i b) |>.mp · j (Finset.mem_univ j)
    nlinarith
  · rintro rfl y
    simp [entrySquaredLoss]

theorem squaredLoss_regular {m n r : ℕ} :
    RegularLossOn (regular : Set (Param m n r))
      (sampleLoss model (entrySquaredLoss : Mat m n → Mat m n → ℝ)) := by
  apply SmoothLossOn.regular
  refine ⟨regular_isOpen, ?_⟩
  rintro ⟨u,y⟩
  unfold sampleLoss model observation entrySquaredLoss U V
  fun_prop

def gauge {m n r : ℕ} (s : GL r) (p : Param m n r) : Param m n r :=
  pack (U p * (s : Mat r r)) (V p * ((s⁻¹ : GL r) : Mat r r)ᵀ)

@[simp] theorem observation_gauge {m n r : ℕ} (s : GL r) (p : Param m n r) :
    observation (gauge s p) = observation p := by
  exact mul_invTranspose_invariant (U p) (V p) s

/-- Right-action convention; note the order of s and t. -/
theorem gauge_mul {m n r : ℕ} (s t : GL r) (p : Param m n r) :
    gauge t (gauge s p) = gauge (s * t) p := by
  ext a
  cases a <;>
    simp [gauge, pack, U, V, Matrix.mul_assoc, Matrix.transpose_mul, mul_inv_rev]

@[simp] theorem gauge_one {m n r : ℕ} (p : Param m n r) : gauge 1 p = p := by
  simp [gauge]

/-- Rectangular full-rank factorization uniqueness, cited in Appendix G.1.
The proof is the standard full-rank factorization argument from Piziak–Odell:
construct the change of basis from a right Gram inverse and then cancel the
full-column-rank factors. -/
theorem fullRank_fiber {m n r : ℕ} {p q : Param m n r}
    (hp : p ∈ regular) (hq : q ∈ regular) :
    observation p = observation q ↔ ∃ s : GL r, q = gauge s p := by
  constructor
  · intro he
    have hGq : IsUnit ((V q)ᵀ * V q) := hq.2.gram_isUnit
    let gq : GL r := hGq.unit
    have hgq : (gq : Mat r r) = (V q)ᵀ * V q := hGq.unit_spec
    let S0 : Mat r r := (V p)ᵀ * V q * ((gq⁻¹ : GL r) : Mat r r)
    have hUS : U p * S0 = U q := by
      calc
        U p * S0 =
            (U p * (V p)ᵀ) * V q * ((gq⁻¹ : GL r) : Mat r r) := by
              simp [S0, Matrix.mul_assoc]
        _ = (U q * (V q)ᵀ) * V q * ((gq⁻¹ : GL r) : Mat r r) := by
              rw [show U p * (V p)ᵀ = U q * (V q)ᵀ by simpa [observation] using he]
        _ = U q * (((V q)ᵀ * V q) * ((gq⁻¹ : GL r) : Mat r r)) := by
              simp [Matrix.mul_assoc]
        _ = U q := by
              rw [← hgq]
              simp
    have hinjS : Function.Injective S0.mulVec := by
      intro x y hxy
      apply hq.1.mulVec_injective
      calc
        U q *ᵥ x = (U p * S0) *ᵥ x := by rw [hUS]
        _ = U p *ᵥ (S0 *ᵥ x) := by rw [Matrix.mulVec_mulVec]
        _ = U p *ᵥ (S0 *ᵥ y) := by rw [hxy]
        _ = (U p * S0) *ᵥ y := by rw [Matrix.mulVec_mulVec]
        _ = U q *ᵥ y := by rw [hUS]
    have hS0 : IsUnit S0 :=
      Matrix.linearIndependent_cols_iff_isUnit.mp
        ((Matrix.mulVec_injective_iff).mp hinjS)
    let s : GL r := hS0.unit
    have hs : (s : Mat r r) = S0 := hS0.unit_spec
    have hSV : S0 * (V q)ᵀ = (V p)ᵀ := by
      apply hp.1.mul_right_cancel
      calc
        U p * (S0 * (V q)ᵀ) = (U p * S0) * (V q)ᵀ := by
          simp [Matrix.mul_assoc]
        _ = U q * (V q)ᵀ := by rw [hUS]
        _ = U p * (V p)ᵀ := by
          simpa [observation] using he.symm
    have hVt : (V q)ᵀ = ((s⁻¹ : GL r) : Mat r r) * (V p)ᵀ := by
      calc
        (V q)ᵀ = 1 * (V q)ᵀ := by simp
        _ = (((s⁻¹ : GL r) : Mat r r) * (s : Mat r r)) * (V q)ᵀ := by simp
        _ = ((s⁻¹ : GL r) : Mat r r) * ((s : Mat r r) * (V q)ᵀ) := by
              simp [Matrix.mul_assoc]
        _ = ((s⁻¹ : GL r) : Mat r r) * (V p)ᵀ := by
              rw [hs, hSV]
    have hV : V q = V p * ((s⁻¹ : GL r) : Mat r r)ᵀ := by
      have ht := congrArg Matrix.transpose hVt
      simpa [Matrix.transpose_mul] using ht
    refine ⟨s, ?_⟩
    ext a
    cases a with
    | inl a =>
        have hu : U q = U p * (s : Mat r r) := by simpa [hs] using hUS.symm.symm
        simpa [gauge, pack, U, V] using congrFun₂ hu a.1 a.2
    | inr a =>
        simpa [gauge, pack, U, V] using congrFun₂ hV a.1 a.2
  · rintro ⟨s, rfl⟩
    exact (observation_gauge s p).symm


/-- Differentiating the matrix product along a parameter curve gives the
usual product-rule tangent equation. -/
lemma observation_tangent_eq_zero
    {m n r : ℕ} {p v : Param m n r} {γ : ℝ → Param m n r}
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p)
    (hobs : (fun t => observation (γ t)) =ᶠ[𝓝 0]
      (fun _ => observation p)) :
    U v * (V p)ᵀ + U p * (V v)ᵀ = 0 := by
  ext i j
  have hentry :
      HasDerivAt (fun t => observation (γ t) i j)
        ((U v * (V p)ᵀ + U p * (V v)ᵀ) i j) 0 := by
    have hterm :
        ∀ a : Fin r,
          HasDerivAt
            (fun t => U (γ t) i a * V (γ t) j a)
            (U v i a * V p j a + U p i a * V v j a) 0 := by
      intro a
      have hu :
          HasDerivAt (fun t => U (γ t) i a) (U v i a) 0 := by
        simpa [U] using
          hγ.clm_apply
            (ContinuousLinearMap.apply ℝ (Param m n r) (Sum.inl (i,a)))
      have hv :
          HasDerivAt (fun t => V (γ t) j a) (V v j a) 0 := by
        simpa [V] using
          hγ.clm_apply
            (ContinuousLinearMap.apply ℝ (Param m n r) (Sum.inr (j,a)))
      simpa [hγ0] using hu.mul hv
    have hsum :=
      (fun a (_ : a ∈ (Finset.univ : Finset (Fin r))) => hterm a)
        |>.fun_sum
    simpa [observation, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_add_distrib] using hsum
  have hconst :
      HasDerivAt (fun t => observation (γ t) i j) 0 0 := by
    exact (hasDerivAt_const (x := 0)
      (c := observation p i j)).congr_of_eventuallyEq
        (hobs.mono fun t ht => congrFun₂ ht i j)
  exact hentry.unique hconst

/-- At a full-rank factorization, the kernel of the differential of
`(U,V) ↦ UVᵀ` is exactly the infinitesimal `GL(r)` gauge orbit. -/
lemma exists_gaugeGenerator_of_observation_tangent
    {m n r : ℕ} {p v : Param m n r} (hp : p ∈ regular)
    (htan : U v * (V p)ᵀ + U p * (V v)ᵀ = 0) :
    ∃ A : Mat r r, v = gaugeGenerator A p := by
  have hGv : IsUnit ((V p)ᵀ * V p) := hp.2.gram_isUnit
  let gv : GL r := hGv.unit
  have hgv : (gv : Mat r r) = (V p)ᵀ * V p := hGv.unit_spec
  let Rv : Mat n r := V p * ((gv⁻¹ : GL r) : Mat r r)
  have hright : (V p)ᵀ * Rv = 1 := by
    simp [Rv, Matrix.mul_assoc, ← hgv]
  let A : Mat r r := -((V v)ᵀ * Rv)
  have hU : U v = U p * A := by
    have h := congrArg (fun M : Mat m n => M * Rv) htan
    simp only [Matrix.add_mul, Matrix.mul_assoc, hright, Matrix.mul_one] at h
    rw [show U p * (V v)ᵀ * Rv = U p * ((V v)ᵀ * Rv) by
      simp [Matrix.mul_assoc]] at h
    simpa [A, Matrix.mul_neg] using eq_neg_of_add_eq_zero_left h
  have hVt : A * (V p)ᵀ + (V v)ᵀ = 0 := by
    have h := htan
    rw [hU, Matrix.mul_assoc] at h
    have hcancel :
        U p * (A * (V p)ᵀ + (V v)ᵀ) = U p * 0 := by
      simpa [Matrix.mul_add, Matrix.mul_assoc] using h
    exact hp.1.mul_right_cancel hcancel
  have hV : V v = -(V p * Aᵀ) := by
    have ht := congrArg Matrix.transpose hVt
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using
      eq_neg_of_add_eq_zero_left ht
  refine ⟨A, ?_⟩
  rw [← pack_U_V v]
  simp [gaugeGenerator, hU, hV]

/-- Tangent version of full-rank functional identifiability. -/
lemma tangent_functional_fibre_is_gauge
    {m n r : ℕ} {p v : Param m n r} (hp : p ∈ regular)
    {γ : ℝ → Param m n r}
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p)
    (hfun : ∀ᶠ t in 𝓝 0, FunctionalEquiv model (γ t) p) :
    ∃ A : Mat r r, v = gaugeGenerator A p := by
  have hobs :
      (fun t => observation (γ t)) =ᶠ[𝓝 0]
        (fun _ => observation p) := by
    filter_upwards [hfun] with t ht
    simpa [model] using ht ()
  exact exists_gaugeGenerator_of_observation_tangent hp
    (observation_tangent_eq_zero hγ hγ0 hobs)


/-- The gradient field of the linear output functional
`Z ↦ ⟪C,Z⟫_F` composed with `(U,V) ↦ UVᵀ`. -/
def normalField {m n r : ℕ} (C : Mat m n) : Field (Param m n r) :=
  fun p => pack (C * V p) (Cᵀ * U p)

/-- The normal distribution to the functional fibre of matrix
factorization, generated by the output-coordinate gradients. -/
def normalDistribution {m n r : ℕ} : Distribution (Param m n r) :=
  fun p => Submodule.span ℝ
    (Set.range (fun C : Mat m n => normalField C p))

lemma normalField_smooth {m n r : ℕ} (C : Mat m n) :
    ContDiff ℝ ∞ (normalField (r := r) C) := by
  unfold normalField pack U V
  fun_prop

lemma normalField_mem {m n r : ℕ} (C : Mat m n) (p : Param m n r) :
    normalField C p ∈ normalDistribution p := by
  exact Submodule.subset_span ⟨C, rfl⟩

/-- The infinitesimal right-gauge directions are orthogonal to every
output-gradient field. -/
lemma inner_normalField_gaugeGenerator
    {m n r : ℕ} (C : Mat m n) (A : Mat r r) (p : Param m n r) :
    ⟪normalField C p, gaugeGenerator A p⟫_ℝ = 0 := by
  simp [normalField, gaugeGenerator, pack, U, V, inner,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_sigma']
  ring

lemma gaugeGenerator_mem_normal_orthogonal
    {m n r : ℕ} (A : Mat r r) (p : Param m n r) :
    gaugeGenerator A p ∈ (normalDistribution p)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨C, rfl⟩ := hz
      simpa [real_inner_comm] using
        inner_normalField_gaugeGenerator C A p
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp [inner_add_right, ihx, ihy]
  | smul a x hx ih =>
      simp [inner_smul_right, ih]

/-- First Lie brackets of the output-gradient fields.  These are the
additional directions used in Marcotte et al.'s completeness computation. -/
lemma lieBracket_normalField
    {m n r : ℕ} (C D : Mat m n) (p : Param m n r) :
    lieBracket (normalField (r := r) C) (normalField D) p =
      pack ((D * Cᵀ - C * Dᵀ) * U p)
        ((Dᵀ * C - Cᵀ * D) * V p) := by
  ext z
  rcases z with z | z
  · rcases z with ⟨i,a⟩
    simp [lieBracket, normalField, pack, U, V, fderiv_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_sigma']
    ring
  · rcases z with ⟨j,a⟩
    simp [lieBracket, normalField, pack, U, V, fderiv_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_sigma']
    ring

lemma lieBracket_normalField_mem_lieCompletion
    {m n r : ℕ} {Ω : Set (Param m n r)}
    (hΩ : IsOpen Ω) {p : Param m n r} (hp : p ∈ Ω)
    (C D : Mat m n) :
    lieBracket (normalField (r := r) C) (normalField D) p ∈
      lieCompletion Ω normalDistribution p := by
  apply Submodule.subset_span
  refine ⟨Ω, lieBracket (normalField (r := r) C) (normalField D),
    hΩ, hp, Set.Subset.rfl, ?_, rfl⟩
  exact LieWordOn.bracket
    (LieWordOn.basic _ ⟨(normalField_smooth C).contDiffOn,
      fun q _ => normalField_mem C q⟩)
    (LieWordOn.basic _ ⟨(normalField_smooth D).contDiffOn,
      fun q _ => normalField_mem D q⟩)


/-- Canonical dual-column matrix for a full-column-rank matrix.  Its
columns are dual to the columns of `A`: `Aᵀ * dualMatrix A = I`. -/
noncomputable def dualMatrix {m r : ℕ} (A : Mat m r)
    (hA : FullColumnRank A) : Mat m r :=
  let g : GL r := hA.gram_isUnit.unit
  A * ((g⁻¹ : GL r) : Mat r r)

lemma transpose_mul_dualMatrix {m r : ℕ} (A : Mat m r)
    (hA : FullColumnRank A) :
    Aᵀ * dualMatrix A hA = 1 := by
  let g : GL r := hA.gram_isUnit.unit
  have hg : (g : Mat r r) = Aᵀ * A :=
    hA.gram_isUnit.unit_spec
  simp [dualMatrix, g, Matrix.mul_assoc, ← hg]

noncomputable def dualColumn {m r : ℕ} (A : Mat m r)
    (hA : FullColumnRank A) (a : Fin r) : Fin m → ℝ :=
  fun i => dualMatrix A hA i a

lemma dot_column_dualColumn {m r : ℕ} (A : Mat m r)
    (hA : FullColumnRank A) (a c : Fin r) :
    ∑ i, A i c * dualColumn A hA a i = if c = a then 1 else 0 := by
  have h := congrFun₂ (transpose_mul_dualMatrix A hA) c a
  simpa [Matrix.mul_apply, Matrix.transpose_apply, dualColumn] using h

lemma dualColumn_ne_zero {m r : ℕ} (A : Mat m r)
    (hA : FullColumnRank A) (a : Fin r) :
    dualColumn A hA a ≠ 0 := by
  intro hz
  have h := dot_column_dualColumn A hA a a
  simp [hz] at h

/-- Rank-one normal fields built from dual columns isolate one skew
coefficient of an infinitesimal gauge matrix. -/
lemma inner_gaugeGenerator_lieBracket_dual
    {m n r : ℕ} {p : Param m n r} (hp : p ∈ regular)
    (A : Mat r r) (a c b : Fin r) :
    let xₐ := dualColumn (U p) hp.1 a
    let x_c := dualColumn (U p) hp.1 c
    let y := dualColumn (V p) hp.2 b
    let C : Mat m n := Matrix.vecMulVec xₐ y
    let D : Mat m n := Matrix.vecMulVec x_c y
    ⟪gaugeGenerator A p,
      lieBracket (normalField (r := r) C) (normalField D) p⟫_ℝ =
      (∑ j, y j * y j) * (A c a - A a c) := by
  dsimp
  rw [lieBracket_normalField]
  simp [gaugeGenerator, normalField, pack, U, V, inner,
    Matrix.vecMulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_sigma', dot_column_dualColumn]
  ring

/-- Orthogonality to the Lie closure of the output-gradient distribution
kills exactly the skew part of the infinitesimal gauge coefficient. -/
lemma gaugeCoefficient_symmetric_of_lieOrthogonal
    {m n r : ℕ} (hr : 0 < r) {Ω : Set (Param m n r)}
    (hΩ : IsOpen Ω) {p : Param m n r} (hpΩ : p ∈ Ω)
    (hp : p ∈ regular) (A : Mat r r)
    (horth :
      gaugeGenerator A p ∈ (lieCompletion Ω normalDistribution p)ᗮ) :
    Aᵀ = A := by
  ext a c
  by_cases hac : a = c
  · subst c
    simp
  · let b : Fin r := ⟨0, hr⟩
    let xₐ := dualColumn (U p) hp.1 a
    let x_c := dualColumn (U p) hp.1 c
    let y := dualColumn (V p) hp.2 b
    let C : Mat m n := Matrix.vecMulVec xₐ y
    let D : Mat m n := Matrix.vecMulVec x_c y
    have hbr :
        lieBracket (normalField (r := r) C) (normalField D) p ∈
          lieCompletion Ω normalDistribution p :=
      lieBracket_normalField_mem_lieCompletion hΩ hpΩ C D
    have hz :
        ⟪gaugeGenerator A p,
          lieBracket (normalField (r := r) C) (normalField D) p⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal' _ _).mp horth _ hbr
    rw [inner_gaugeGenerator_lieBracket_dual hp A a c b] at hz
    have hy : (∑ j, y j * y j) ≠ 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2
        (norm_ne_zero_iff.mpr (dualColumn_ne_zero (V p) hp.2 b))
    have hskew : A c a - A a c = 0 :=
      (mul_eq_zero.mp hz).resolve_left hy
    simpa [Matrix.transpose_apply] using hskew.symm

def balance {m n r : ℕ} (p : Param m n r) : Mat r r :=
  (U p)ᵀ * U p - (V p)ᵀ * V p

def law {m n r : ℕ} (a : Upper r) (p : Param m n r) : ℝ :=
  balance p a.1.1 a.1.2

/-- The true infinitesimal gauge action. -/
def gaugeGenerator {m n r : ℕ} (A : Mat r r) (p : Param m n r) : Param m n r :=
  pack (U p * A) (-(V p * Aᵀ))

/-- E_ab + E_ba: diagonal entries correctly receive a factor of two. -/
def symmetricElementary {r : ℕ} (a : Upper r) : Mat r r := fun i j =>
  (if i = a.1.1 ∧ j = a.1.2 then 1 else 0) +
  (if i = a.1.2 ∧ j = a.1.1 then 1 else 0)

theorem gradient_law {m n r : ℕ} (a : Upper r) (p : Param m n r) :
    gradient (law a) p = gaugeGenerator (symmetricElementary a) p := by
  apply (InnerProductSpace.toDual ℝ (Param m n r)).injective
  rw [toDual_gradient]
  ext q
  rw [← inner_gradient_left]
  simp only [law, balance, gaugeGenerator, pack, U, V]
  simp [fderiv_apply, Matrix.mul_apply, Matrix.transpose_apply,
    symmetricElementary, inner, Finset.sum_sigma']
  ring

theorem law_smooth {m n r : ℕ} (a : Upper r) :
    ContDiff ℝ ∞ (law (m := m) (n := n) a) := by
  unfold law balance U V
  fun_prop

/-- Conservation's elementary algebraic cancellation. Here A is the
backpropagated derivative with respect to the product UVᵀ. -/
theorem balance_tangent_cancellation {m n r : ℕ}
    (u : Mat m r) (v : Mat n r) (A : Mat m n) :
    ((-(A * v))ᵀ * u + uᵀ * (-(A * v))) -
      ((-(Aᵀ * u))ᵀ * v + vᵀ * (-(Aᵀ * u))) = 0 := by
  simp only [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- The gauge field has a local functional symmetry on any open domain. -/
theorem gaugeGenerator_flow {m n r : ℕ} {Ω : Set (Param m n r)}
    (hΩ : IsOpen Ω) (A : Mat r r) :
    ∃ ψ : LocalFlow Ω (gaugeGenerator A), IsFunctionalSymmetry model ψ := by
  let S : ℝ → GL r := fun t => Matrix.expGL (t • A)
  let F : ℝ → Param m n r → Param m n r := fun t p => gauge (S t) p
  let D : Set (ℝ × Param m n r) := {z | z.2 ∈ Ω ∧ F z.1 z.2 ∈ Ω}
  have hDopen : IsOpen D := by
    exact hΩ.preimage_fst_inter_preimage_flow hΩ
      (Matrix.continuous_expGL_action A)
  let ψ : LocalFlow Ω (gaugeGenerator A) :=
    { domain := D
      open_domain := hDopen
      source_mem := by intro t p h; exact h.1
      zero_mem := by
        intro p hp
        simpa [D, F, S, Matrix.expGL_zero, gauge_one] using And.intro hp hp
      time_convex := by
        intro p hp
        exact IsOpen.component_convex_timeInterval hDopen
          (by simpa [D, F, S, Matrix.expGL_zero, gauge_one] using And.intro hp hp)
      toFun := F
      smooth := by
        dsimp [D, F, S]
        fun_prop
      initial := by
        intro p hp
        simp [F, S, Matrix.expGL_zero, gauge_one]
      target_mem := by
        intro t p htp
        exact htp.2
      ode := by
        intro t p htp
        simpa [F, S] using
          Matrix.hasDerivAt_gauge_exp (A := A) (p := p) (t := t)
      composition := by
        intro t s p hsp ht hts
        rw [show F (t + s) p = gauge (S t) (gauge (S s) p) by
          simp [F, S, gauge_mul, Matrix.expGL_add_same]]
      }
  refine ⟨ψ, ?_⟩
  intro t p htp
  simpa [ψ, F] using observation_gauge (S t) p

/-- Gram-difference conservation, independent of identifiability/completeness. -/
theorem laws_conserved {m n r : ℕ} {Y : Type*}
    {Ω : Set (Param m n r)} (ell : Mat m n → Y → ℝ)
    (hL : RegularLossOn Ω (sampleLoss model ell)) (a : Upper r) :
    IsConservedOn Ω (sampleLoss model ell) (law a) := by
  obtain ⟨ψ, hψ⟩ := gaugeGenerator_flow hL.isOpen (symmetricElementary a)
  apply (proposition2 hL ((law_smooth a).contDiffOn.of_le (by simp))).mpr
  intro p hp
  rw [gradient_law]
  exact (corollary7 hL ψ).mp
    (functionalSymmetry_loss model ell ψ hψ) p hp

/-- Marcotte et al. (2023), Section 4.1: completeness of the
upper-triangular Gram-difference coordinates for full-rank matrix
factorization.  This is external to Nguyen--Montúfar and therefore remains an
explicit Stage-1 dependency. -/
class HasMarcotteMatrixFactorizationCompleteness : Prop where
  complete_balance_laws :
    ∀ {m n r : ℕ}, 0 < r → ∀ {Y : Type*}
      (ell : Mat m n → Y → ℝ), SeparatesPredictions ell →
      RegularLossOn (regular : Set (Param m n r)) (sampleLoss model ell) →
      ∀ {p₀ : Param m n r}, p₀ ∈ regular →
        ∃ Ω : Set (Param m n r), IsOpen Ω ∧ p₀ ∈ Ω ∧ Ω ⊆ regular ∧
          CompleteLawsOn Ω (sampleLoss model ell) (law (m := m) (n := n))

/-- Lemma 28 as used by Nguyen--Montúfar. -/
theorem lemma28 [HasMarcotteMatrixFactorizationCompleteness]
    {m n r : ℕ} (hr : 0 < r) {Y : Type*}
    (ell : Mat m n → Y → ℝ) (hsep : SeparatesPredictions ell)
    (hL : RegularLossOn (regular : Set (Param m n r)) (sampleLoss model ell))
    {p₀ : Param m n r} (hp₀ : p₀ ∈ regular) :
    ∃ Ω : Set (Param m n r), IsOpen Ω ∧ p₀ ∈ Ω ∧ Ω ⊆ regular ∧
      CompleteLawsOn Ω (sampleLoss model ell) (law (m := m) (n := n)) :=
  HasMarcotteMatrixFactorizationCompleteness.complete_balance_laws
    hr ell hsep hL hp₀

/-- Counting upper-triangular coordinates. -/
theorem card_upper (r : ℕ) : Fintype.card (Upper r) = r * (r + 1) / 2 := by
  classical
  change Fintype.card {ab : Fin r × Fin r // ab.1.val ≤ ab.2.val} =
    r * (r + 1) / 2
  calc
    Fintype.card {ab : Fin r × Fin r // ab.1.val ≤ ab.2.val}
        = ∑ b : Fin r, (b.val + 1) := by
            rw [Fintype.card_subtype_Σ]
            simp
    _ = ∑ b in Finset.range r, (b + 1) := by
          simpa using Fin.sum_univ_eq_sum_range (fun b : Fin r => b.val + 1)
    _ = r * (r + 1) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_range_id]
          simp
          omega

/-! The paper's Section 2.3 uses the cited matrix-factorization completeness
result directly; no separate squared-loss rank lemma is required here. -/

example : Fintype.card (Upper 2) = 3 := by decide
example : Module.finrank ℝ (Param 2 2 2) = 8 := by
  simp [Param, Index]

end Factorization
end GradientFlowPaper

end -- noncomputable section
