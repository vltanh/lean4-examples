import Lean4Examples.GradientFlowPaper.MatrixFactorization

/-! ## Source module: GradientFlowPaper/Polynomial.lean -/


/-!
Proposition 19 and Appendix G.2.

The paper's "finite-to-one" means finite-to-one MODULO the standard scaling
and permutation symmetries, not finite parameter fibres. Since permutations
form a finite group, they may be absorbed in a finite set of representatives;
`FiniteToOneAt` below therefore quotients by all nonzero diagonal scalings.

The paper does not further define the word "generic" in Proposition 19.
This module therefore separates two issues.  The concrete nonzero-hidden-bias
locus is proved open and dense and is used only for the differential scaling
argument.  The cited finite-identifiability input is represented by the
source-facing witness `GenericFiniteToOneAt`, which says only that
`FiniteToOneAt` holds on an open neighborhood.  The paper-internal step
from a finite fibre modulo scaling to a locally isolated scaling orbit is
proved below by the canonical bias-normalization slice; it is not assumed as
part of the external input.
-/

noncomputable section
open Set Function
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix

namespace GradientFlowPaper
namespace PolynomialNetwork


structure Architecture where
  depth : ℕ
  depth_pos : 0 < depth
  width : ℕ → ℕ
  width_pos : ∀ j, j ≤ depth → 0 < width j
  degree : ℕ → ℕ
  degree_pos : ∀ j, j + 1 < depth → 0 < degree j

variable (A : Architecture)

abbrev Layer := Fin A.depth
abbrev Hidden := Σ j : Fin (A.depth - 1), Fin (A.width (j.val + 1))
abbrev Index := Σ j : Layer A,
  (Fin (A.width (j.val + 1)) × Fin (A.width j.val)) ⊕ Fin (A.width (j.val + 1))
abbrev Param := Vec (Index A)
abbrev Input := Vec (Fin (A.width 0))
abbrev Output := Vec (Fin (A.width A.depth))

def W (p : Param A) (j : Layer A) : Mat (A.width (j.val + 1)) (A.width j.val) :=
  fun i k => p ⟨j, Sum.inl (i, k)⟩

def bias (p : Param A) (j : Layer A) : Fin (A.width (j.val + 1)) → ℝ :=
  fun i => p ⟨j, Sum.inr i⟩

/-- Zero-based layer indices. The final affine layer has no monomial activation. -/
def evalPrefix (p : Param A) (x : Input A) :
    (j : ℕ) → j ≤ A.depth → (Fin (A.width j) → ℝ)
  | 0, _ => fun i => x i
  | j + 1, hj =>
      let l : Layer A := ⟨j, by omega⟩
      let z : Fin (A.width (j + 1)) → ℝ := fun i =>
        (∑ k, W A p l i k * evalPrefix (A := A) p x j (by omega) k) + bias A p l i
      if j + 1 = A.depth then z else fun i => (z i) ^ A.degree j

def model (p : Param A) (x : Input A) : Output A :=
  WithLp.toLp 2 (evalPrefix A p x A.depth le_rfl)

def currentLayer (a : Hidden A) : Layer A := ⟨a.1.val, by have := a.1.isLt; omega⟩
def nextLayer (a : Hidden A) : Layer A := ⟨a.1.val + 1, by have := a.1.isLt; omega⟩

/-- Proposition 19's exact formula, including biases and the activation degree. -/
def law (a : Hidden A) (p : Param A) : ℝ :=
  (∑ k, (W A p (currentLayer A a) a.2 k)^2) +
    (bias A p (currentLayer A a) a.2)^2 -
    (A.degree a.1.val : ℝ) * ∑ i, (W A p (nextLayer A a) i a.2)^2

def outgoingNode (j : Layer A) (hj : j.val + 1 < A.depth)
    (i : Fin (A.width (j.val + 1))) : Hidden A :=
  ⟨⟨j.val, by omega⟩, i⟩

def incomingNode (j : Layer A) (hj : 0 < j.val)
    (i : Fin (A.width j.val)) : Hidden A :=
  ⟨⟨j.val - 1, by have := j.isLt; omega⟩,
    ⟨i.val, by simpa [show j.val - 1 + 1 = j.val by omega] using i.isLt⟩⟩

/-- Boundary diagonal matrices D₀ = D_L = I are built into these functions. -/
def outgoingScale (s : Hidden A → ℝˣ) (j : Layer A)
    (i : Fin (A.width (j.val + 1))) : ℝ :=
  if hj : j.val + 1 < A.depth then (s (outgoingNode A j hj i) : ℝ) else 1

def incomingScale (s : Hidden A → ℝˣ) (j : Layer A)
    (i : Fin (A.width j.val)) : ℝ :=
  if hj : 0 < j.val then
    (s (incomingNode A j hj i) : ℝ) ^ (-(A.degree (j.val - 1) : ℤ))
  else 1

/-- W'_l = D_l W_l D_{l-1}^{-r_{l-1}}, b'_l = D_l b_l. -/
def diagonalGauge (s : Hidden A → ℝˣ) (p : Param A) : Param A :=
  WithLp.toLp 2 (fun a => match a.2 with
    | Sum.inl (i, k) => outgoingScale A s a.1 i * W A p a.1 i k * incomingScale A s a.1 k
    | Sum.inr i => outgoingScale A s a.1 i * bias A p a.1 i)

@[simp] lemma outgoingScale_one (j : Layer A)
    (i : Fin (A.width (j.val + 1))) :
    outgoingScale A (fun _ => (1 : ℝˣ)) j i = 1 := by
  simp [outgoingScale]

@[simp] lemma incomingScale_one (j : Layer A)
    (i : Fin (A.width j.val)) :
    incomingScale A (fun _ => (1 : ℝˣ)) j i = 1 := by
  simp [incomingScale]

lemma outgoingScale_mul (s t : Hidden A → ℝˣ) (j : Layer A)
    (i : Fin (A.width (j.val + 1))) :
    outgoingScale A (fun a => t a * s a) j i =
      outgoingScale A t j i * outgoingScale A s j i := by
  simp [outgoingScale]
  split <;> simp

lemma incomingScale_mul (s t : Hidden A → ℝˣ) (j : Layer A)
    (i : Fin (A.width j.val)) :
    incomingScale A (fun a => t a * s a) j i =
      incomingScale A t j i * incomingScale A s j i := by
  simp [incomingScale]
  split <;> simp [mul_zpow]

@[simp] theorem diagonalGauge_one (p : Param A) :
    diagonalGauge A (fun _ => (1 : ℝˣ)) p = p := by
  ext z
  rcases z with ⟨j, z⟩
  cases z <;> simp [diagonalGauge, W, bias]

/-- The diagonal rescalings form a genuine group action.  The order below
matches function composition: the outer scaling `t` multiplies the inner
scaling `s`. -/
theorem diagonalGauge_mul (s t : Hidden A → ℝˣ) (p : Param A) :
    diagonalGauge A t (diagonalGauge A s p) =
      diagonalGauge A (fun a => t a * s a) p := by
  ext z
  rcases z with ⟨j, z⟩
  cases z with
  | inl ik =>
      rcases ik with ⟨i,k⟩
      simp only [diagonalGauge, W, WithLp.ofLp_toLp]
      rw [outgoingScale_mul, incomingScale_mul]
      ring
  | inr i =>
      simp only [diagonalGauge, bias, WithLp.ofLp_toLp]
      rw [outgoingScale_mul]
      ring

@[simp] theorem diagonalGauge_inv_left (s : Hidden A → ℝˣ) (p : Param A) :
    diagonalGauge A (fun a => (s a)⁻¹) (diagonalGauge A s p) = p := by
  rw [diagonalGauge_mul]
  simpa using diagonalGauge_one A p

@[simp] theorem diagonalGauge_inv_right (s : Hidden A → ℝˣ) (p : Param A) :
    diagonalGauge A s (diagonalGauge A (fun a => (s a)⁻¹) p) = p := by
  rw [diagonalGauge_mul]
  simpa using diagonalGauge_one A p

/-- Continuous one-neuron scaling subgroup. -/
def singleGauge (a : Hidden A) (t : ℝ) (p : Param A) : Param A :=
  diagonalGauge A
    (fun b => Units.mk0 (Real.exp (if b = a then t else 0)) (Real.exp_ne_zero _)) p

def generator (a : Hidden A) (p : Param A) : Param A :=
  deriv (fun t => singleGauge A a t p) 0

theorem diagonalGauge_functional (s : Hidden A → ℝˣ) (p : Param A) :
    FunctionalEquiv (model A) (diagonalGauge A s p) p := by
  intro x
  have hprefix :
      ∀ j (hj : j ≤ A.depth),
        evalPrefix A (diagonalGauge A s p) x j hj =
          fun i =>
            (if h : j = 0 ∨ j = A.depth then 1
             else (s ⟨⟨j - 1, by omega⟩,
               ⟨i.val, by simpa [show j - 1 + 1 = j by omega] using i.isLt⟩⟩ : ℝ)) *
            evalPrefix A p x j hj i := by
    intro j
    induction j with
    | zero =>
        intro hj
        ext i
        simp [evalPrefix]
    | succ j ih =>
        intro hj
        ext i
        by_cases hlast : j + 1 = A.depth
        · subst hlast
          simp [evalPrefix, diagonalGauge, outgoingScale, incomingScale, ih]
        · have hjlt : j + 1 < A.depth := lt_of_le_of_ne hj hlast
          simp [evalPrefix, diagonalGauge, outgoingScale, incomingScale, ih,
            hlast, hjlt, Finset.mul_sum, mul_assoc, ← mul_pow,
            zpow_neg, zpow_natCast]
  ext i
  simpa [model, hprefix A.depth le_rfl]

/-- A finite number of scaling orbits covers the full functional fibre. -/
def FiniteToOneAt (p : Param A) : Prop :=
  ∃ R : Set (Param A), R.Finite ∧
    ∀ q : Param A, FunctionalEquiv (model A) p q →
      ∃ r ∈ R, FunctionalEquiv (model A) p r ∧
        ∃ s : Hidden A → ℝˣ, q = diagonalGauge A s r

/-- A concrete dense-open regular locus sufficient for the differential part
of Appendix G.2: every hidden bias coordinate is nonzero. Nguyen--Montufar
leave the word generic informal; the Usevich dependency below remains
responsible for the finite-to-one architecture statement. -/
def GenericPoint (p : Param A) : Prop :=
  ∀ a : Hidden A, bias A p (currentLayer A a) a.2 ≠ 0

def genericSet : Set (Param A) := {p | GenericPoint A p}

theorem genericSet_isOpen : IsOpen (genericSet A) := by
  change IsOpen (⋂ a : Hidden A,
    {p : Param A | bias A p (currentLayer A a) a.2 ≠ 0})
  apply isOpen_iInter_of_finite
  intro a
  exact isOpen_compl_singleton.preimage (by fun_prop)

theorem genericSet_dense : Dense (genericSet A) := by
  change Dense (⋂ a : Hidden A,
    {p : Param A | bias A p (currentLayer A a) a.2 ≠ 0})
  apply dense_iInter_of_isOpen
  · intro a
    exact isOpen_compl_singleton.preimage (by fun_prop)
  · intro a
    let l : Param A →ₗ[ℝ] ℝ :=
      { toFun := fun p => bias A p (currentLayer A a) a.2
        map_add' := by intro p q; rfl
        map_smul' := by intro t p; rfl }
    have hsurj : Function.Surjective l := by
      intro z
      let e : Index A := ⟨currentLayer A a, Sum.inr a.2⟩
      refine ⟨WithLp.toLp 2 (fun i => if i = e then z else 0), ?_⟩
      simp [l, bias, e]
    have hopen : IsOpenMap l :=
      l.isOpenMap_of_finiteDimensional hsurj
    have hd : Dense (l ⁻¹' ({0}ᶜ : Set ℝ)) :=
      (dense_compl_singleton (0 : ℝ)).preimage hopen
    simpa [l] using hd

theorem generator_bias_coordinate (p : Param A) (a b : Hidden A) :
    generator A a p ⟨currentLayer A b, Sum.inr b.2⟩ =
      if a = b then bias A p (currentLayer A a) a.2 else 0 := by
  unfold generator singleGauge diagonalGauge bias outgoingScale
  by_cases hab : a = b
  · subst b
    simp [hab, Real.deriv_exp]
  · simp [hab, Real.deriv_exp]

theorem generic_generators_independent {p : Param A}
    (hp : GenericPoint A p) :
    LinearIndependent ℝ (fun a : Hidden A => generator A a p) := by
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum a
  have hcoord := congrArg
    (fun v : Param A => v ⟨currentLayer A a, Sum.inr a.2⟩) hsum
  simp [Finset.sum_apply, generator_bias_coordinate, hp a] at hcoord
  exact hcoord

lemma bias_diagonalGauge_hidden (s : Hidden A → ℝˣ) (p : Param A)
    (a : Hidden A) :
    bias A (diagonalGauge A s p) (currentLayer A a) a.2 =
      (s a : ℝ) * bias A p (currentLayer A a) a.2 := by
  simp [bias, diagonalGauge, outgoingScale, currentLayer, outgoingNode]
  congr

/-- Canonical diagonal-scaling coordinates, read from hidden biases. -/
def biasRatioGauge (p q : Param A) (hp : GenericPoint A p) :
    Hidden A → ℝˣ :=
  fun a =>
    if hq : bias A q (currentLayer A a) a.2 ≠ 0 then
      Units.mk0
        (bias A q (currentLayer A a) a.2 /
          bias A p (currentLayer A a) a.2)
        (div_ne_zero hq (hp a))
    else 1

lemma biasRatioGauge_eq_of_gauge {p q : Param A}
    (hp : GenericPoint A p)
    {s : Hidden A → ℝˣ} (hqp : q = diagonalGauge A s p) :
    biasRatioGauge A p q hp = s := by
  funext a
  have hq : bias A q (currentLayer A a) a.2 ≠ 0 := by
    rw [show bias A q (currentLayer A a) a.2 =
      (s a : ℝ) * bias A p (currentLayer A a) a.2 by
        simpa [hqp] using bias_diagonalGauge_hidden A s p a]
    exact mul_ne_zero (Units.ne_zero _) (hp a)
  apply Units.ext
  rw [show bias A q (currentLayer A a) a.2 =
    (s a : ℝ) * bias A p (currentLayer A a) a.2 by
      simpa [hqp] using bias_diagonalGauge_hidden A s p a]
  simp [biasRatioGauge, hp a, hq]

lemma gauge_of_biasRatio_on_orbit {p q : Param A}
    (hp : GenericPoint A p)
    (horbit : ∃ s : Hidden A → ℝˣ, q = diagonalGauge A s p) :
    q = diagonalGauge A (biasRatioGauge A p q hp) p := by
  obtain ⟨s,rfl⟩ := horbit
  rw [biasRatioGauge_eq_of_gauge A hp rfl]

lemma GenericPoint.diagonalGauge {p : Param A} (hp : GenericPoint A p)
    (s : Hidden A → ℝˣ) :
    GenericPoint A (diagonalGauge A s p) := by
  intro a
  rw [bias_diagonalGauge_hidden]
  exact mul_ne_zero (Units.ne_zero _) (hp a)

/-- Real bias ratio used to define a proof-independent local slice map.
Unlike `biasRatioGauge`, this is defined everywhere; only its behavior near
a nonzero-bias point is used. -/
def sliceRatio (p q : Param A) (a : Hidden A) : ℝ :=
  bias A p (currentLayer A a) a.2 /
    bias A q (currentLayer A a) a.2

def sliceOutgoingScale (p q : Param A) (j : Layer A)
    (i : Fin (A.width (j.val + 1))) : ℝ :=
  if hj : j.val + 1 < A.depth then
    sliceRatio A p q (outgoingNode A j hj i)
  else 1

def sliceIncomingScale (p q : Param A) (j : Layer A)
    (i : Fin (A.width j.val)) : ℝ :=
  if hj : 0 < j.val then
    (sliceRatio A p q (incomingNode A j hj i)) ^
      (-(A.degree (j.val - 1) : ℤ))
  else 1

/-- Canonical local slice through a regular parameter: rescale every hidden
unit so that its hidden bias agrees with the corresponding bias of `p`.
The formula is written over `ℝ` rather than `ℝˣ` so it is an ordinary
ambient function and continuity can be discussed without proof arguments. -/
def sliceNormalize (p q : Param A) : Param A :=
  WithLp.toLp 2 (fun z =>
    match z.2 with
    | Sum.inl (i,k) =>
        sliceOutgoingScale A p q z.1 i * W A q z.1 i k *
          sliceIncomingScale A p q z.1 k
    | Sum.inr i =>
        sliceOutgoingScale A p q z.1 i * bias A q z.1 i)

lemma sliceNormalize_eq_diagonalGauge {p q : Param A}
    (hp : GenericPoint A p) (hq : GenericPoint A q) :
    sliceNormalize A p q =
      diagonalGauge A (biasRatioGauge A q p hq) q := by
  ext z
  rcases z with ⟨j,z⟩
  cases z with
  | inl ik =>
      rcases ik with ⟨i,k⟩
      simp [sliceNormalize, sliceOutgoingScale, sliceIncomingScale,
        sliceRatio, diagonalGauge, outgoingScale, incomingScale,
        biasRatioGauge, hp, hq, W]
  | inr i =>
      simp [sliceNormalize, sliceOutgoingScale, sliceRatio,
        diagonalGauge, outgoingScale, biasRatioGauge, hp, hq, bias]

@[simp] lemma sliceNormalize_self {p : Param A} (hp : GenericPoint A p) :
    sliceNormalize A p p = p := by
  rw [sliceNormalize_eq_diagonalGauge A hp hp]
  have hratio :
      biasRatioGauge A p p hp = fun _ => (1 : ℝˣ) := by
    exact biasRatioGauge_eq_of_gauge A hp <| by
      simpa using (diagonalGauge_one A p).symm
  rw [hratio, diagonalGauge_one]

/-- The slice normalization is constant on each regular scaling orbit. -/
lemma sliceNormalize_diagonalGauge {p r : Param A}
    (hp : GenericPoint A p) (hr : GenericPoint A r)
    (s : Hidden A → ℝˣ) :
    sliceNormalize A p (diagonalGauge A s r) =
      sliceNormalize A p r := by
  have hq : GenericPoint A (diagonalGauge A s r) :=
    hr.diagonalGauge A s
  rw [sliceNormalize_eq_diagonalGauge A hp hq,
    sliceNormalize_eq_diagonalGauge A hp hr,
    diagonalGauge_mul]
  congr 2
  funext a
  apply Units.ext
  have hpb : bias A p (currentLayer A a) a.2 ≠ 0 := hp a
  have hrb : bias A r (currentLayer A a) a.2 ≠ 0 := hr a
  have hqb :
      bias A (diagonalGauge A s r) (currentLayer A a) a.2 ≠ 0 := hq a
  simp [biasRatioGauge, hpb, hrb, hqb, bias_diagonalGauge_hidden]
  field_simp [hrb, Units.ne_zero (s a)]
  ring

/-- Continuity of the canonical slice at a regular base point.  All
denominators occurring in the normalization are hidden biases, hence are
nonzero at `p`. -/
lemma continuousAt_sliceNormalize {p : Param A} (hp : GenericPoint A p) :
    ContinuousAt (sliceNormalize A p) p := by
  unfold sliceNormalize sliceOutgoingScale sliceIncomingScale sliceRatio
  fun_prop (disch := aesop)

/-- A finite functional fibre modulo scaling has an isolated scaling orbit at
every regular point.  This is the local-neighborhood deduction that was
previously (and incorrectly) hidden inside `HasPNNGenericRegime.local_regime`.

The normalization sends every regular point in one scaling orbit to the same
slice point.  The fibre of `p` has only finitely many scaling orbits, so
after normalization there are only finitely many competing slice points.
Remove those points and pull the resulting open set back through the
continuous normalization map. -/
theorem finiteToOneAt_local_scaling_orbit
    {p : Param A} (hfinite : FiniteToOneAt A p)
    (hp : GenericPoint A p) :
    ∃ U : Set (Param A), IsOpen U ∧ p ∈ U ∧
      U ⊆ genericSet A ∧
      ∀ q ∈ U,
        FunctionalEquiv (model A) q p ↔
          ∃ s : Hidden A → ℝˣ, q = diagonalGauge A s p := by
  obtain ⟨R, hRfin, hR⟩ := hfinite
  let badReps : Set (Param A) :=
    {r | r ∈ R ∧ GenericPoint A r ∧
      ¬ ∃ t : Hidden A → ℝˣ, p = diagonalGauge A t r}
  let badSlice : Set (Param A) := sliceNormalize A p '' badReps
  have hbadRepsFin : badReps.Finite := by
    apply hRfin.subset
    intro r hr
    exact hr.1
  have hbadSliceFin : badSlice.Finite :=
    hbadRepsFin.image (sliceNormalize A p)
  have hp_not_badSlice : p ∉ badSlice := by
    intro hbad
    rcases hbad with ⟨r, hr, hnorm⟩
    have hrgen : GenericPoint A r := hr.2.1
    apply hr.2.2
    refine ⟨biasRatioGauge A r p hrgen, ?_⟩
    calc
      p = sliceNormalize A p r := hnorm.symm
      _ = diagonalGauge A (biasRatioGauge A r p hrgen) r :=
        sliceNormalize_eq_diagonalGauge A hp hrgen
  have hnormp :
      sliceNormalize A p p ∈ badSliceᶜ := by
    simpa [sliceNormalize_self A hp] using hp_not_badSlice
  have hpre :
      sliceNormalize A p ⁻¹' badSliceᶜ ∈ 𝓝 p := by
    exact (continuousAt_sliceNormalize A hp)
      (hbadSliceFin.isClosed.isOpen_compl.mem_nhds hnormp)
  have hgen : genericSet A ∈ 𝓝 p :=
    (genericSet_isOpen A).mem_nhds hp
  have hgood :
      (sliceNormalize A p ⁻¹' badSliceᶜ) ∩ genericSet A ∈ 𝓝 p :=
    inter_mem hpre hgen
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hgood
  refine ⟨U, hUopen, hpU, ?_, ?_⟩
  · intro q hq
    exact (hUsub hq).2
  · intro q hq
    constructor
    · intro hqp
      have hqgen : GenericPoint A q := (hUsub hq).2
      have hpq : FunctionalEquiv (model A) p q := hqp.symm
      obtain ⟨r, hrR, hpr, s, hqsr⟩ := hR q hpq
      have hrgen : GenericPoint A r := by
        intro a
        intro hz
        have hqzero :
            bias A q (currentLayer A a) a.2 = 0 := by
          rw [hqsr, bias_diagonalGauge_hidden, hz, mul_zero]
        exact hqgen a hqzero
      have hnorm :
          sliceNormalize A p q = sliceNormalize A p r := by
        rw [hqsr]
        exact sliceNormalize_diagonalGauge A hp hrgen s
      have hr_not_bad :
          sliceNormalize A p r ∉ badSlice := by
        intro hrbad
        have hqbad : sliceNormalize A p q ∈ badSlice := by
          rw [hnorm]
          exact hrbad
        exact (hUsub hq).1 hqbad
      have horbit_r :
          ∃ t : Hidden A → ℝˣ, p = diagonalGauge A t r := by
        by_contra hno
        apply hr_not_bad
        exact ⟨r, ⟨hrR, hrgen, hno⟩, rfl⟩
      obtain ⟨t, hptr⟩ := horbit_r
      have hrp :
          r = diagonalGauge A (fun a => (t a)⁻¹) p := by
        calc
          r = diagonalGauge A (fun a => (t a)⁻¹)
              (diagonalGauge A t r) :=
            (diagonalGauge_inv_left A t r).symm
          _ = diagonalGauge A (fun a => (t a)⁻¹) p := by
            rw [← hptr]
      refine ⟨fun a => s a * (t a)⁻¹, ?_⟩
      calc
        q = diagonalGauge A s r := hqsr
        _ = diagonalGauge A s
            (diagonalGauge A (fun a => (t a)⁻¹) p) := by rw [hrp]
        _ = diagonalGauge A (fun a => s a * (t a)⁻¹) p := by
          rw [diagonalGauge_mul]
    · rintro ⟨s, rfl⟩
      exact diagonalGauge_functional A s p

/-- Exponential coordinates on the connected component of the diagonal
scaling group. -/
def expGauge (p : Param A) (x : Hidden A → ℝ) : Param A :=
  diagonalGauge A
    (fun a => Units.mk0 (Real.exp (x a)) (Real.exp_ne_zero _)) p

@[simp] lemma expGauge_zero (p : Param A) :
    expGauge A p 0 = p := by
  ext z
  rcases z with ⟨j,z⟩
  cases z <;> simp [expGauge, diagonalGauge, outgoingScale, incomingScale]

def scalingBasis (a : Hidden A) : Hidden A → ℝ :=
  fun b => if b = a then 1 else 0

lemma expGauge_scalingBasis_line (p : Param A) (a : Hidden A) (t : ℝ) :
    expGauge A p (t • scalingBasis A a) = singleGauge A a t p := by
  unfold expGauge singleGauge
  congr 2
  funext b
  apply Units.ext
  simp [scalingBasis, mul_boole, eq_comm]

lemma expGauge_differentiableAt (p : Param A) (x : Hidden A → ℝ) :
    DifferentiableAt ℝ (expGauge A p) x := by
  unfold expGauge diagonalGauge outgoingScale incomingScale
  fun_prop

lemma fderiv_expGauge_basis (p : Param A) (a : Hidden A) :
    (fderiv ℝ (expGauge A p) 0) (scalingBasis A a) =
      generator A a p := by
  have hb :
      HasDerivAt (fun t : ℝ => t • scalingBasis A a)
        (scalingBasis A a) 0 := by
    simpa using (hasDerivAt_id (x := 0)).smul_const (scalingBasis A a)
  have hcomp :=
    (expGauge_differentiableAt A p 0).hasFDerivAt.comp_hasDerivAt 0 hb
  have hsingle :
      HasDerivAt (fun t : ℝ => singleGauge A a t p)
        (generator A a p) 0 := by
    have hd :
        DifferentiableAt ℝ (fun t : ℝ => singleGauge A a t p) 0 := by
      unfold singleGauge diagonalGauge outgoingScale incomingScale
      fun_prop
    simpa [generator] using hd.hasDerivAt
  have heq :
      (fun t : ℝ => expGauge A p (t • scalingBasis A a)) =
        fun t => singleGauge A a t p := by
    funext t
    exact expGauge_scalingBasis_line A p a t
  rw [heq] at hcomp
  exact hcomp.unique hsingle

lemma fderiv_expGauge_mem_span (p : Param A) (x : Hidden A → ℝ) :
    (fderiv ℝ (expGauge A p) 0) x ∈
      Submodule.span ℝ
        (Set.range (fun a : Hidden A => generator A a p)) := by
  have hx :
      x = ∑ a : Hidden A, x a • scalingBasis A a := by
    ext b
    simp [scalingBasis]
  rw [hx, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul, fderiv_expGauge_basis]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)

/-- Logarithmic bias-ratio coordinates for a differentiable curve through a
generic point. -/
def logBiasRatio (p q : Param A) (a : Hidden A) : ℝ :=
  Real.log
    (bias A q (currentLayer A a) a.2 /
      bias A p (currentLayer A a) a.2)


def logBiasVelocity (p v : Param A) (a : Hidden A) : ℝ :=
  v ⟨currentLayer A a, Sum.inr a.2⟩ /
    bias A p (currentLayer A a) a.2

lemma hasDerivAt_logBiasRatio
    {p : Param A} (hp : GenericPoint A p)
    {γ : ℝ → Param A} {v : Param A}
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p) :
    HasDerivAt
      (fun t => fun a : Hidden A => logBiasRatio A p (γ t) a)
      (logBiasVelocity A p v) 0 := by
  rw [hasDerivAt_pi]
  intro a
  let idx : Index A := ⟨currentLayer A a, Sum.inr a.2⟩
  have hcoord :
      HasDerivAt (fun t => γ t idx) (v idx) 0 :=
    hγ.clm_apply (ContinuousLinearMap.apply ℝ (Param A) idx)
  have hratio :
      HasDerivAt
        (fun t => bias A (γ t) (currentLayer A a) a.2 /
          bias A p (currentLayer A a) a.2)
        (logBiasVelocity A p v a) 0 := by
    simpa [bias, idx, logBiasVelocity] using
      hcoord.div_const (bias A p (currentLayer A a) a.2)
  have hratio0 :
      bias A (γ 0) (currentLayer A a) a.2 /
          bias A p (currentLayer A a) a.2 = 1 := by
    rw [hγ0]
    exact div_self (hp a)
  have hlog :=
    (Real.hasDerivAt_log (by simpa [hratio0] : (1 : ℝ) ≠ 0)).comp 0 hratio
  simpa [logBiasRatio, hratio0] using hlog

lemma eventually_positive_biasRatio
    {p : Param A} (hp : GenericPoint A p)
    {γ : ℝ → Param A} {v : Param A}
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p) :
    ∀ᶠ t in 𝓝 0, ∀ a : Hidden A,
      0 < bias A (γ t) (currentLayer A a) a.2 /
        bias A p (currentLayer A a) a.2 := by
  rw [Filter.eventually_all]
  intro a
  let idx : Index A := ⟨currentLayer A a, Sum.inr a.2⟩
  have hcoord :
      HasDerivAt (fun t => γ t idx) (v idx) 0 :=
    hγ.clm_apply (ContinuousLinearMap.apply ℝ (Param A) idx)
  have hratio :
      ContinuousAt
        (fun t => bias A (γ t) (currentLayer A a) a.2 /
          bias A p (currentLayer A a) a.2) 0 := by
    exact (by
      simpa [bias, idx] using
        hcoord.continuousAt.div_const
          (bias A p (currentLayer A a) a.2))
  apply hratio.eventually
  have hzero :
      bias A (γ 0) (currentLayer A a) a.2 /
        bias A p (currentLayer A a) a.2 = 1 := by
    rw [hγ0]
    exact div_self (hp a)
  simpa [hzero] using (isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num))

lemma expGauge_logBiasRatio_eq_canonical
    {p q : Param A} (hp : GenericPoint A p)
    (hpos : ∀ a : Hidden A,
      0 < bias A q (currentLayer A a) a.2 /
        bias A p (currentLayer A a) a.2) :
    expGauge A p (fun a => logBiasRatio A p q a) =
      diagonalGauge A (biasRatioGauge A p q hp) p := by
  unfold expGauge
  congr 2
  funext a
  apply Units.ext
  have hq : bias A q (currentLayer A a) a.2 ≠ 0 := by
    intro hz
    have := hpos a
    simp [hz] at this
  simp [biasRatioGauge, logBiasRatio, hq,
    Real.exp_log (hpos a)]

/-- Tangent space of the regular diagonal-scaling orbit. -/
theorem tangent_mem_span_scaling_orbit
    {p : Param A} (hp : GenericPoint A p)
    {γ : ℝ → Param A} {v : Param A}
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p)
    (horbit : ∀ᶠ t in 𝓝 0,
      ∃ s : Hidden A → ℝˣ, γ t = diagonalGauge A s p) :
    v ∈ Submodule.span ℝ
      (Set.range (fun a : Hidden A => generator A a p)) := by
  have hpos :=
    eventually_positive_biasRatio A hp hγ hγ0
  have heq : ∀ᶠ t in 𝓝 0,
      γ t = expGauge A p (fun a => logBiasRatio A p (γ t) a) := by
    filter_upwards [horbit, hpos] with t ht hpt
    calc
      γ t = diagonalGauge A (biasRatioGauge A p (γ t) hp) p :=
        gauge_of_biasRatio_on_orbit A hp ht
      _ = expGauge A p (fun a => logBiasRatio A p (γ t) a) :=
        (expGauge_logBiasRatio_eq_canonical A hp hpt).symm
  have hlog :=
    hasDerivAt_logBiasRatio A hp hγ hγ0
  have hcomp :
      HasDerivAt
        (fun t => expGauge A p
          ((fun t => fun a : Hidden A => logBiasRatio A p (γ t) a) t))
        ((fderiv ℝ (expGauge A p) 0) (logBiasVelocity A p v)) 0 :=
    (expGauge_differentiableAt A p 0).hasFDerivAt.comp_hasDerivAt 0 hlog
  have hsame :
      HasDerivAt
        (fun t => expGauge A p
          (fun a : Hidden A => logBiasRatio A p (γ t) a))
        v 0 :=
    hγ.congr_of_eventuallyEq heq
  have hv :
      v = (fderiv ℝ (expGauge A p) 0) (logBiasVelocity A p v) :=
    hsame.unique hcomp
  rw [hv]
  exact fderiv_expGauge_mem_span A p (logBiasVelocity A p v)


/-! The paper's proof of Proposition 19 uses finite-to-one
identifiability in a generic neighborhood.  The local scaling-orbit
conclusion is **not** part of the external hypothesis: it is the theorem
`finiteToOneAt_local_scaling_orbit` proved above. -/

def FiniteToOneOn (U : Set (Param A)) : Prop :=
  ∀ p ∈ U, FiniteToOneAt A p

/-- Source-facing local witness for a generic finite-identifiability point.
This contains only the identifiability property that must ultimately be
supplied from Usevich et al.; it does not contain the desired fibre chart,
generator independence, or tangent-space conclusion. -/
structure GenericFiniteToOneAt (p : Param A) : Prop where
  neighborhood : Set (Param A)
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : p ∈ neighborhood
  finiteToOneOn_neighborhood : FiniteToOneOn A neighborhood

theorem law_smooth (a : Hidden A) : ContDiff ℝ ∞ (law A a) := by
  unfold law W bias
  fun_prop

/-- Appendix G.2: ∇h_i^j = 2χ_i^j; the factor of two is not omitted. -/
theorem gradient_law (a : Hidden A) (p : Param A) :
    gradient (law A a) p = (2 : ℝ) • generator A a p := by
  apply (InnerProductSpace.toDual ℝ (Param A)).injective
  rw [toDual_gradient]
  ext q
  rw [← inner_gradient_left]
  simp [law, generator, singleGauge, diagonalGauge, outgoingScale,
    incomingScale, currentLayer, nextLayer, W, bias, inner,
    Real.deriv_exp, Finset.sum_apply]
  ring

theorem independent_laws_of_generators {U : Set (Param A)}
    (hind : ∀ p ∈ U,
      LinearIndependent ℝ (fun a : Hidden A => generator A a p)) :
    FunctionallyIndependentOn U (law A) := by
  intro p hp
  have hscale :
      (fun a : Hidden A => gradient (law A a) p) =
        fun a => (2 : ℝ) • generator A a p := by
    funext a
    exact gradient_law A a p
  rw [hscale]
  exact (hind p hp).smul (fun _ => by norm_num)

/-- Preservation holds without a finite-to-one or genericity assumption.
Appendix G.2 only needs the infinitesimal derivative of the explicit scaling
symmetry, so no auxiliary local-flow construction is required here. -/
theorem laws_conserved {U : Set (Param A)} {Y : Type*}
    (ell : Output A → Y → ℝ)
    (hL : RegularLossOn U (sampleLoss (model A) ell)) (a : Hidden A) :
    IsConservedOn U (sampleLoss (model A) ell) (law A a) := by
  apply (proposition2 hL ((law_smooth A a).contDiffOn.of_le (by simp))).mpr
  intro p hp
  rw [mem_symmetryDistribution_iff]
  rintro s
  have hcurve :
      HasDerivAt (fun t : ℝ => singleGauge A a t p) (generator A a p) 0 := by
    have hd : DifferentiableAt ℝ (fun t : ℝ => singleGauge A a t p) 0 := by
      unfold singleGauge diagonalGauge outgoingScale incomingScale
      fun_prop
    simpa [generator] using hd.hasDerivAt
  have hsample :
      DifferentiableAt ℝ (sampleLoss (model A) ell s) p :=
    differentiableAt_of_c1 hL.isOpen (hL.c1 s) hp
  have hchain := hasDerivAt_observable hsample hcurve
  have hconst :
      (fun t : ℝ => sampleLoss (model A) ell s (singleGauge A a t p)) =
        fun _ => sampleLoss (model A) ell s p := by
    funext t
    rcases s with ⟨x, y⟩
    exact congrArg (fun z => ell z y)
      (diagonalGauge_functional A
        (fun b => Units.mk0
          (Real.exp (if b = a then t else 0)) (Real.exp_ne_zero _)) p x)
  have hz :
      HasDerivAt
        (fun t : ℝ => sampleLoss (model A) ell s (singleGauge A a t p)) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const 0 _
  have horth := hchain.unique hz
  rw [gradient_law A a p]
  simpa [real_inner_smul_left] using congrArg (fun z : ℝ => (2 : ℝ) * z) horth

/-- The completeness step uses the local fibre description, not merely the
observation that the displayed quantities are conserved. -/
theorem conserved_gradient_spanned
    {U : Set (Param A)} (hU : IsOpen U)
    (hregular : ∀ p ∈ U, GenericPoint A p)
    (hfinite : FiniteToOneOn A U)
    {Y : Type*} (ell : Output A → Y → ℝ) (hsep : SeparatesPredictions ell)
    (hL : RegularLossOn U (sampleLoss (model A) ell))
    {V : Set (Param A)} (hV : IsOpen V) (hVU : V ⊆ U)
    {h : Param A → ℝ} (hh : ContDiffOn ℝ ∞ h V)
    (hc : IsConservedOn V (sampleLoss (model A) ell) h) :
    ∀ p ∈ V, gradient h p ∈
      Submodule.span ℝ (Set.range (fun a : Hidden A => gradient (law A a) p)) := by
  intro p hp
  have hregV := hL.mono hV hVU
  obtain ⟨ψ, -, hψloss⟩ := proposition9 hregV
    (smooth_gradient_on hV hh)
    ((proposition2 hregV (hh.of_le (by simp))).mp hc)
  have hψfun : IsFunctionalSymmetry (model A) ψ :=
    proposition14 (model A) ell hsep ψ hψloss
  let γ : ℝ → Param A := fun t => ψ.toFun t p
  have hγ : HasDerivAt γ (gradient h p) 0 := by
    simpa [γ, ψ.initial p hp] using ψ.ode (ψ.zero_mem p hp)
  have hγ0 : γ 0 = p := ψ.initial p hp
  obtain ⟨W, hW, hpW, -, hfiber⟩ :=
    finiteToOneAt_local_scaling_orbit A
      (hfinite p (hVU hp)) (hregular p (hVU hp))
  have hγW : ∀ᶠ t in 𝓝 0, γ t ∈ W := by
    have hW0 : W ∈ 𝓝 (γ 0) := by
      simpa [hγ0] using hW.mem_nhds hpW
    exact hγ.continuousAt hW0
  have horbit : ∀ᶠ t in 𝓝 0,
      ∃ s : Hidden A → ℝˣ, γ t = diagonalGauge A s p := by
    filter_upwards
      [(ψ.open_times p).mem_nhds (ψ.zero_mem p hp), hγW]
      with t ht htW
    apply (hfiber (γ t) htW).mp
    exact hψfun t p ht
  have hspan :=
    tangent_mem_span_scaling_orbit A (hregular p (hVU hp)) hγ hγ0 horbit
  have heq :
      (fun a : Hidden A => gradient (law A a) p) =
        fun a => (2 : ℝ) • generator A a p := by
    funext a
    exact gradient_law A a p
  rw [heq]
  have hle :
      Submodule.span ℝ (Set.range (fun a : Hidden A => generator A a p)) ≤
        Submodule.span ℝ
          (Set.range (fun a : Hidden A => (2 : ℝ) • generator A a p)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have hrepr :
        generator A a p =
          (2 : ℝ)⁻¹ • ((2 : ℝ) • generator A a p) := by
      simp [htwo]
    rw [hrepr]
    exact (Submodule.span ℝ
      (Set.range (fun a : Hidden A => (2 : ℝ) • generator A a p))).smul_mem _
        (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hspan

/-- Proposition 19 at a point of a generic finite-identifiability
neighborhood, intersected with the explicit dense-open regular locus used by
the differential argument.  The finite-identifiability hypothesis contains
no local fibre/orbit conclusion; that conclusion is derived pointwise above. -/
theorem proposition19
    {Y : Type*} (ell : Output A → Y → ℝ)
    (hsep : SeparatesPredictions ell)
    (hL : RegularLossOn Set.univ (sampleLoss (model A) ell))
    {p₀ : Param A} (hfinite : GenericFiniteToOneAt A p₀)
    (hregular : GenericPoint A p₀) :
    ∃ U : Set (Param A), IsOpen U ∧ p₀ ∈ U ∧
      CompleteLawsOn U (sampleLoss (model A) ell) (law A) := by
  let U := hfinite.neighborhood ∩ genericSet A
  have hU : IsOpen U :=
    hfinite.isOpen_neighborhood.inter (genericSet_isOpen A)
  have hpU : p₀ ∈ U :=
    ⟨hfinite.mem_neighborhood, hregular⟩
  have hregularU : ∀ p ∈ U, GenericPoint A p := by
    intro p hp
    exact hp.2
  have hfiniteU : FiniteToOneOn A U := by
    intro p hp
    exact hfinite.finiteToOneOn_neighborhood p hp.1
  have hind : ∀ p ∈ U,
      LinearIndependent ℝ (fun a : Hidden A => generator A a p) := by
    intro p hp
    exact generic_generators_independent A hp.2
  have hreg := hL.mono hU (Set.subset_univ U)
  refine ⟨U, hU, hpU, (fun a => (law_smooth A a).contDiffOn),
    (fun a => laws_conserved A ell hreg a),
    independent_laws_of_generators A hind, ?_⟩
  intro V hV hVU h hh hc p hp
  exact conserved_gradient_spanned A hU hregularU hfiniteU
    ell hsep hreg hV hVU hh hc p hp

theorem number_of_laws :
    Fintype.card (Hidden A) = ∑ j : Fin (A.depth - 1), A.width (j.val + 1) := by
  simp [Hidden, Fintype.card_sigma]

end PolynomialNetwork
end GradientFlowPaper

end -- noncomputable section
