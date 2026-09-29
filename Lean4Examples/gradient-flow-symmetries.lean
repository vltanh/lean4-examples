import Mathlib

/-!
# GradientFlowPaper — single-file draft

Based on Nguyen and Montúfar, arXiv:2609.34549v1 (supplied PDF).
UNCOMPILED. All mathematical proof holes in this draft have proof bodies.
The scripts have not yet been elaborated or kernel-checked; the next phase is
API/typing repair against the repository's pinned Lean and mathlib versions.

This file is the concatenation of the eight mathematical modules in dependency
order. Use it instead of, not together with, the modular source. The project
targets the repository's Lean and mathlib v4.26.0 pin. No custom axioms are introduced.
-/


/-! ## Source module: GradientFlowPaper/Core.lean -/


/-!
# On Parameter Symmetries and Conservation Laws in Gradient Flow

Uncompiled Lean 4 / mathlib draft of Nguyen--Montúfar, arXiv:2609.34549v1.
This file: Section 2, Proposition 1, Proposition 2, Definition 3, Assumption 13.

The source follows the paper theorem-by-theorem. No custom axioms are
introduced. Proof bodies are present throughout, but are intentionally still
uncompiled and therefore require later API/typing repair.

The ambient parameter space carries its Euclidean inner product.  Functions
on an open parameter domain are represented by ambient functions, with every
claim restricted to that domain.  No differentiability is inferred merely
from the existence of mathlib's totalized `gradient` or `fderiv`.
-/

noncomputable section

open Set Function Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

namespace GradientFlowPaper

abbrev Vec (ι : Type*) := EuclideanSpace ℝ ι
abbrev Field (E : Type*) := E → E
abbrev Distribution (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  E → Submodule ℝ E

section Models

variable {P X Y Z S : Type*}

/-- A model's pointwise functional equivalence relation. -/
def FunctionalEquiv (G : P → X → Z) (p q : P) : Prop :=
  ∀ x, G p x = G q x

/-- Assumption 13. This is separation of *values*, not spanning of gradients. -/
def SeparatesPredictions (ell : Z → Y → ℝ) : Prop :=
  ∀ z z', (∀ y, ell z y = ell z' y) → z = z'

def sampleLoss (G : P → X → Z) (ell : Z → Y → ℝ) :
    X × Y → P → ℝ :=
  fun s p => ell (G p s.1) s.2

def empiricalLoss (L : S → P → ℝ) {n : ℕ} (d : Fin n → S) (p : P) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, L (d i) p

@[simp] theorem empiricalLoss_singleton (L : S → P → ℝ) (s : S) (p : P) :
    empiricalLoss L (fun _ : Fin 1 => s) p = L s p := by
  simp [empiricalLoss]

theorem functionalEquiv_loss (G : P → X → Z) (ell : Z → Y → ℝ)
    {p q : P} (h : FunctionalEquiv G p q) :
    ∀ s, sampleLoss G ell s p = sampleLoss G ell s q := by
  rintro ⟨x, y⟩
  simp only [sampleLoss, h x]

/-- The elementary separation step used in Proposition 14. -/
theorem lossEquiv_iff_functionalEquiv (G : P → X → Z) (ell : Z → Y → ℝ)
    (hsep : SeparatesPredictions ell) (p q : P) :
    (∀ s, sampleLoss G ell s p = sampleLoss G ell s q) ↔
      FunctionalEquiv G p q := by
  constructor
  · intro h x
    exact hsep _ _ (fun y => h (x, y))
  · exact functionalEquiv_loss G ell

/-- Lemma 26(1). -/
theorem separates_of_zero_on_diagonal (ell : Z → Z → ℝ)
    (hdiag : ∀ z, ell z z = 0)
    (hpos : ∀ z y, z ≠ y → 0 < ell z y) :
    SeparatesPredictions ell := by
  intro z z' h
  by_contra hne
  have hp := hpos z' z (Ne.symm hne)
  have hz : ell z' z = 0 := (h z).symm.trans (hdiag z)
  linarith

/-- Lemma 26(2), also useful for the matrix-factorization observation loss. -/
theorem separates_dist [MetricSpace Z] :
    SeparatesPredictions (fun z y : Z => dist z y) := by
  apply separates_of_zero_on_diagonal
  · exact dist_self
  · intro z y h
    exact dist_pos.mpr h

/-- Lemma 26(4): the finite-dimensional absolute/L¹ loss. -/
def absoluteLoss {n : ℕ} (z y : Vec (Fin n)) : ℝ :=
  ∑ i, |z i - y i|

theorem separates_absoluteLoss {n : ℕ} :
    SeparatesPredictions (absoluteLoss : Vec (Fin n) → Vec (Fin n) → ℝ) := by
  apply separates_of_zero_on_diagonal
  · intro z
    simp [absoluteLoss]
  · intro z y hne
    have hex : ∃ i : Fin n, z i ≠ y i := by
      by_contra h
      push_neg at h
      exact hne (WithLp.ext h)
    obtain ⟨i, hi⟩ := hex
    have hterm : 0 < |z i - y i| := abs_pos.mpr (sub_ne_zero.mpr hi)
    have hle :
        |z i - y i| ≤ ∑ j, |z j - y j| :=
      Finset.single_le_sum
        (fun j _ => abs_nonneg (z j - y j)) (Finset.mem_univ i)
    unfold absoluteLoss
    linarith

/-- Lemma 26(5): the finite-dimensional Lᵖ loss written as the sum of
coordinatewise real powers, for p > 0. -/
def lpPowerLoss {n : ℕ} (p : ℝ) (z y : Vec (Fin n)) : ℝ :=
  ∑ i, |z i - y i| ^ p

theorem separates_lpPowerLoss {n : ℕ} {p : ℝ} (hp : 0 < p) :
    SeparatesPredictions (lpPowerLoss p : Vec (Fin n) → Vec (Fin n) → ℝ) := by
  apply separates_of_zero_on_diagonal
  · intro z
    simp [lpPowerLoss, Real.zero_rpow hp.ne']
  · intro z y hne
    have hex : ∃ i : Fin n, z i ≠ y i := by
      by_contra h
      push_neg at h
      exact hne (WithLp.ext h)
    obtain ⟨i, hi⟩ := hex
    have habs : 0 < |z i - y i| := abs_pos.mpr (sub_ne_zero.mpr hi)
    have hterm : 0 < |z i - y i| ^ p :=
      Real.rpow_pos_of_pos habs p
    have hle :
        |z i - y i| ^ p ≤ ∑ j, |z j - y j| ^ p :=
      Finset.single_le_sum
        (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
    unfold lpPowerLoss
    linarith

/-- Closed and open probability simplices used in Lemma 26(6–7). -/
def ProbabilitySimplex (n : ℕ) :=
  {y : Vec (Fin n) // (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}

def PositiveProbabilitySimplex (n : ℕ) :=
  {z : Vec (Fin n) // (∀ i, 0 < z i) ∧ ∑ i, z i = 1}

def simplexVertex {n : ℕ} (i : Fin n) : ProbabilitySimplex n :=
  ⟨WithLp.toLp 2 (fun j => if j = i then 1 else 0),
    ⟨by intro j; split_ifs <;> positivity, by simp⟩⟩

/-- Lemma 26(6): multiclass cross entropy on Δ₊₊ × Δ₊. -/
def crossEntropyLoss {n : ℕ}
    (z : PositiveProbabilitySimplex n) (y : ProbabilitySimplex n) : ℝ :=
  - ∑ i, y.1 i * Real.log (z.1 i)

theorem separates_crossEntropyLoss {n : ℕ} :
    SeparatesPredictions
      (crossEntropyLoss :
        PositiveProbabilitySimplex n → ProbabilitySimplex n → ℝ) := by
  intro z z' h
  apply Subtype.ext
  apply WithLp.ext
  intro i
  have hi := h (simplexVertex i)
  have hlog : Real.log (z.1 i) = Real.log (z'.1 i) := by
    simpa [crossEntropyLoss, simplexVertex] using neg_injective hi
  calc
    z.1 i = Real.exp (Real.log (z.1 i)) :=
      (Real.exp_log (z.2.1 i)).symm
    _ = Real.exp (Real.log (z'.1 i)) := congrArg Real.exp hlog
    _ = z'.1 i := Real.exp_log (z'.2.1 i)

/-- Lemma 26(7): KL divergence on Δ₊₊ × Δ₊. -/
def klDivergenceLoss {n : ℕ}
    (z : PositiveProbabilitySimplex n) (y : ProbabilitySimplex n) : ℝ :=
  ∑ i, y.1 i * Real.log (y.1 i / z.1 i)

theorem separates_klDivergenceLoss {n : ℕ} :
    SeparatesPredictions
      (klDivergenceLoss :
        PositiveProbabilitySimplex n → ProbabilitySimplex n → ℝ) := by
  intro z z' h
  apply Subtype.ext
  apply WithLp.ext
  intro i
  have hi := h (simplexVertex i)
  have hlog :
      Real.log ((z.1 i)⁻¹) = Real.log ((z'.1 i)⁻¹) := by
    simpa [klDivergenceLoss, simplexVertex, one_div] using hi
  have hinv : (z.1 i)⁻¹ = (z'.1 i)⁻¹ := by
    calc
      (z.1 i)⁻¹ = Real.exp (Real.log ((z.1 i)⁻¹)) := by
        rw [Real.exp_log]
        positivity
      _ = Real.exp (Real.log ((z'.1 i)⁻¹)) := congrArg Real.exp hlog
      _ = (z'.1 i)⁻¹ := by
        rw [Real.exp_log]
        positivity
  exact inv_injective.mp hinv

/-- Unit vectors used for the cosine loss in Lemma 26(8). -/
def UnitVector (n : ℕ) := {z : Vec (Fin n) // ‖z‖ = 1}

def cosineLoss {n : ℕ} (z y : UnitVector n) : ℝ :=
  1 - ⟪z.1, y.1⟫_ℝ

theorem separates_cosineLoss {n : ℕ} :
    SeparatesPredictions (cosineLoss : UnitVector n → UnitVector n → ℝ) := by
  intro z z' h
  apply Subtype.ext
  have hz := h z
  have hinner : ⟪z'.1, z.1⟫_ℝ = 1 := by
    have hself : ⟪z.1, z.1⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, z.2]
      norm_num
    simpa [cosineLoss, hself] using hz.symm
  have hnormsq : ‖z'.1 - z.1‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, z'.2, z.2, hinner]
    norm_num
  have hnorm : ‖z'.1 - z.1‖ = 0 := sq_eq_zero_iff.mp hnormsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Lemma 26, represented by the eight source-level separation facts.
Items (1)–(3) are the generic zero-diagonal criterion, metric distance, and
squared Euclidean loss above; items (4)–(8) are the declarations immediately
above. -/
theorem lemma26 :
    (∀ (Z : Type*) (ell : Z → Z → ℝ),
      (∀ z, ell z z = 0) →
      (∀ z y, z ≠ y → 0 < ell z y) →
      SeparatesPredictions ell) ∧
    (∀ (Z : Type*) [MetricSpace Z],
      SeparatesPredictions (fun z y : Z => dist z y)) ∧
    (∀ n, SeparatesPredictions
      (fun z y : Vec (Fin n) => ‖z - y‖ ^ 2)) ∧
    (∀ n, SeparatesPredictions
      (absoluteLoss : Vec (Fin n) → Vec (Fin n) → ℝ)) ∧
    (∀ n (p : ℝ), 0 < p →
      SeparatesPredictions
        (lpPowerLoss p : Vec (Fin n) → Vec (Fin n) → ℝ)) ∧
    (∀ n, SeparatesPredictions
      (crossEntropyLoss :
        PositiveProbabilitySimplex n → ProbabilitySimplex n → ℝ)) ∧
    (∀ n, SeparatesPredictions
      (klDivergenceLoss :
        PositiveProbabilitySimplex n → ProbabilitySimplex n → ℝ)) ∧
    (∀ n, SeparatesPredictions
      (cosineLoss : UnitVector n → UnitVector n → ℝ)) := by
  refine ⟨fun _ ell hdiag hpos =>
      separates_of_zero_on_diagonal ell hdiag hpos,
    fun _ _ => separates_dist, ?_,
    fun _ => separates_absoluteLoss,
    fun _ _ hp => separates_lpPowerLoss hp,
    fun _ => separates_crossEntropyLoss,
    fun _ => separates_klDivergenceLoss,
    fun _ => separates_cosineLoss⟩
  intro n
  apply separates_of_zero_on_diagonal
  · intro z
    simp
  · intro z y hne
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))

end Models

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {S : Type*} {Ω : Set E}

/-- Local Lipschitz regularity on an open parameter domain, explicitly bundled. -/
def LocallyLipschitzOn (Ω : Set E) (v : Field E) : Prop :=
  ∀ p ∈ Ω, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
    ∃ K : ℝ≥0, LipschitzOnWith K v U

structure RegularLossOn (Ω : Set E) (L : S → E → ℝ) : Prop where
  isOpen : IsOpen Ω
  c1 : ∀ s, ContDiffOn ℝ 1 (L s) Ω
  localLip : ∀ s, LocallyLipschitzOn Ω (gradient (L s))

/-- A smooth specialization used for the geometric part of the paper. -/
structure SmoothLossOn (Ω : Set E) (L : S → E → ℝ) : Prop where
  isOpen : IsOpen Ω
  smooth : ∀ s, ContDiffOn ℝ ∞ (L s) Ω

lemma differentiableAt_of_c1 {f : E → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 f Ω) {p : E} (hp : p ∈ Ω) :
    DifferentiableAt ℝ f p :=
  (hf.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hp)

lemma SmoothLossOn.regular {L : S → E → ℝ} (hL : SmoothLossOn Ω L) :
    RegularLossOn Ω L := by
  refine ⟨hL.isOpen, fun s => (hL.smooth s).of_le (by simp), ?_⟩
  intro s
  intro s p hp
  have h₂ : ContDiffOn ℝ 2 (L s) Ω := (hL.smooth s).of_le (by simp)
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (L s)) Ω := by
    exact ((contDiffOn_succ_iff_fderiv_of_isOpen hL.isOpen).mp h₂).2
  have hgrad : ContDiffOn ℝ 1 (gradient (L s)) Ω := by
    rw [show gradient (L s) =
      (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ (L s) by
        ext x
        simp [gradient]]
    exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hD
  have hgradp : ContDiffAt ℝ 1 (gradient (L s)) p :=
    (hgrad p hp).contDiffAt (hL.isOpen.mem_nhds hp)
  obtain ⟨K, V, hV, hKV⟩ := hgradp.exists_lipschitzOnWith
  obtain ⟨U, hUV, hUopen, hpU⟩ := mem_nhds_iff.mp hV
  refine ⟨U ∩ Ω, hUopen.inter hL.isOpen, ⟨hpU, hp⟩, inter_subset_right, K, ?_⟩
  exact hKV.mono (fun x hx => hUV hx.1)

/-- Equation (2): the span of all single-sample gradients. -/
def gradientDistribution (L : S → E → ℝ) (p : E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun s => gradient (L s) p))

def symmetryDistribution (L : S → E → ℝ) (p : E) : Submodule ℝ E :=
  (gradientDistribution L p)ᗮ

lemma sampleGradient_mem (L : S → E → ℝ) (p : E) (s : S) :
    gradient (L s) p ∈ gradientDistribution L p :=
  Submodule.subset_span ⟨s, rfl⟩

lemma mem_symmetryDistribution_iff (L : S → E → ℝ) (p v : E) :
    v ∈ symmetryDistribution L p ↔
      ∀ s, ⟪v, gradient (L s) p⟫_ℝ = 0 := by
  rw [symmetryDistribution, Submodule.mem_orthogonal']
  constructor
  · intro h s
    exact h _ (sampleGradient_mem L p s)
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨s, rfl⟩ := hw
        exact h s
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_right, ha, hb]
    | smul a w _ hw => simp [inner_smul_right, hw]

/-- The actual gradient-flow vector field, not a separately postulated vector. -/
def empiricalField (L : S → E → ℝ) {n : ℕ} (d : Fin n → S) : Field E :=
  fun p => -gradient (empiricalLoss L d) p

lemma gradient_empiricalLoss (L : S → E → ℝ) {n : ℕ} (d : Fin n → S)
    {p : E} (hL : ∀ i, DifferentiableAt ℝ (L (d i)) p) :
    gradient (empiricalLoss L d) p =
      (n : ℝ)⁻¹ • ∑ i, gradient (L (d i)) p := by
  have hd : HasFDerivAt (empiricalLoss L d)
      ((n : ℝ)⁻¹ • ∑ i, fderiv ℝ (L (d i)) p) p := by
    simpa only [empiricalLoss] using
      (HasFDerivAt.fun_sum (u := Finset.univ)
        (fun i _ => (hL i).hasFDerivAt)).const_mul ((n : ℝ)⁻¹)
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa only [toDual_gradient, map_smul, map_sum] using hd.fderiv

lemma empiricalField_mem (L : S → E → ℝ) {n : ℕ} (d : Fin n → S)
    {p : E} (hL : ∀ i, DifferentiableAt ℝ (L (d i)) p) :
    empiricalField L d p ∈ gradientDistribution L p := by
  rw [empiricalField, gradient_empiricalLoss L d hL]
  exact (gradientDistribution L p).neg_mem
    ((gradientDistribution L p).smul_mem _
      ((gradientDistribution L p).sum_mem (fun i _ => sampleGradient_mem L p (d i))))

/-- A solution on a time set, including the requirement that it stays in Ω. -/
def IsIntegralCurveOn (Ω : Set E) (I : Set ℝ) (v : Field E)
    (γ : ℝ → E) : Prop :=
  MapsTo γ I Ω ∧ ∀ t ∈ I, HasDerivAt γ (v (γ t)) t

/-- The trajectory definition from Section 2.1, localized to open time intervals.
On the whole space Proposition 1 supplies the forward-global trajectories. -/
def IsConservedOn (Ω : Set E) (L : S → E → ℝ) (h : E → ℝ) : Prop :=
  ∀ (n : ℕ) (d : Fin n → S), 0 < n →
    ∀ (I : Set ℝ), IsOpen I → Convex ℝ I →
      ∀ γ : ℝ → E, IsIntegralCurveOn Ω I (empiricalField L d) γ →
        ∀ t ∈ I, ∀ u ∈ I, h (γ t) = h (γ u)

/-- The infinitesimal condition is kept distinct from trajectory conservation. -/
def IsInfinitesimalLawOn (Ω : Set E) (L : S → E → ℝ) (h : E → ℝ) : Prop :=
  ∀ p ∈ Ω, gradient h p ∈ symmetryDistribution L p

lemma infinitesimalLaw_iff_samples (L : S → E → ℝ) (h : E → ℝ) :
    IsInfinitesimalLawOn Ω L h ↔
      ∀ p ∈ Ω, ∀ s, ⟪gradient h p, gradient (L s) p⟫_ℝ = 0 := by
  simp only [IsInfinitesimalLawOn, mem_symmetryDistribution_iff]

lemma hasDerivAt_observable {f : E → ℝ} {γ : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun u => f (γ u)) (⟪gradient f (γ t), v⟫_ℝ) t := by
  simpa only [inner_gradient_left] using hf.hasFDerivAt.comp_hasDerivAt t hγ

lemma const_on_open_interval {f : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hconv : Convex ℝ I)
    (hf : ∀ t ∈ I, HasDerivAt f 0 t) {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) :
    f t = f u := by
  exact hI.is_const_of_deriv_eq_zero hconv.isPreconnected
    (fun x hx => (hf x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hf x hx).deriv) ht hu

/-- A Picard--Lindelöf obligation used only to derive the necessary condition. -/
theorem local_solution (hΩ : IsOpen Ω) {v : Field E}
    (hv : LocallyLipschitzOn Ω v) {p : E} (hp : p ∈ Ω) :
    ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ 0 ∈ I ∧
      ∃ γ : ℝ → E, γ 0 = p ∧ IsIntegralCurveOn Ω I v γ := by
  obtain ⟨U, hUopen, hpU, hUΩ, K, hvK⟩ := hv p hp
  have hvU : ContinuousOn v U := hvK.continuousOn
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUopen p hpU
  let a : ℝ≥0 := ⟨r / 2, by positivity⟩
  have hclosed : Metric.closedBall p a ⊆ U := by
    intro q hq
    apply hball
    exact lt_of_le_of_lt hq (by simpa [a] using half_lt_self hr)
  have hcont : ContinuousOn v (Metric.closedBall p a) :=
    hvU.mono hclosed
  have hlip : LipschitzOnWith K v (Metric.closedBall p a) :=
    hvK.mono hclosed
  obtain ⟨ε, hε, γ, hγ0, hγ⟩ :=
    ODE.exists_local_solution_autonomous_of_continuousOn_lipschitzOnWith
      (x₀ := p) (a := a) hcont hlip
  let I : Set ℝ := Set.Ioo (-ε) ε
  refine ⟨I, isOpen_Ioo, convex_Ioo _ _, ⟨by linarith, by linarith⟩, γ, hγ0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro t ht
    exact hUΩ (hclosed (hγ.1 t ht))
  · intro t ht
    exact hγ.2 t ht

/-- Proposition 2, sufficient direction: chain rule + the mean value theorem. -/
theorem conserved_of_infinitesimal {L : S → E → ℝ} {h : E → ℝ}
    (hL : RegularLossOn Ω L) (hh : ContDiffOn ℝ 1 h Ω)
    (horth : IsInfinitesimalLawOn Ω L h) : IsConservedOn Ω L h := by
  intro n d hn I hI hconv γ hγ t ht u hu
  apply const_on_open_interval hI hconv (t := t) (u := u) _ ht hu
  intro a ha
  have hp := hγ.1 ha
  have hmem := empiricalField_mem L d
    (fun i => differentiableAt_of_c1 hL.isOpen (hL.c1 (d i)) hp)
  have hz : ⟪gradient h (γ a), empiricalField L d (γ a)⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (horth _ hp) _ hmem
  simpa only [hz] using
    hasDerivAt_observable (differentiableAt_of_c1 hL.isOpen hh hp) (hγ.2 a ha)

/-- Proposition 2, necessary direction. Singleton datasets are essential. -/
theorem infinitesimal_of_conserved {L : S → E → ℝ} {h : E → ℝ}
    (hL : RegularLossOn Ω L) (hh : ContDiffOn ℝ 1 h Ω)
    (hc : IsConservedOn Ω L h) : IsInfinitesimalLawOn Ω L h := by
  rw [infinitesimalLaw_iff_samples]
  intro p hp s
  have hlip : LocallyLipschitzOn Ω (fun x => -gradient (L s) x) := by
    intro x hx
    obtain ⟨U, ho, hxu, hsub, K, hK⟩ := hL.localLip s x hx
    exact ⟨U, ho, hxu, hsub, K, hK.neg⟩
  obtain ⟨I, hI, hconv, h0, γ, hγ0, hγ⟩ := local_solution hL.isOpen hlip hp
  have hsingle : empiricalField L (fun _ : Fin 1 => s) =
      (fun x => -gradient (L s) x) := by
    simp [empiricalField, empiricalLoss]
  have hconst : ∀ t ∈ I, h (γ t) = h (γ 0) := by
    intro t ht
    apply hc 1 (fun _ => s) (by omega) I hI hconv γ _ t ht 0 h0
    simpa only [hsingle] using hγ
  have heq : (fun t => h (γ t)) =ᶠ[𝓝 0] (fun _ => h (γ 0)) := by
    filter_upwards [hI.mem_nhds h0] with t ht using hconst t ht
  have hzero : HasDerivAt (fun t => h (γ t)) 0 0 :=
    (hasDerivAt_const 0 (h (γ 0))).congr_of_eventuallyEq heq.symm
  have hd := hasDerivAt_observable
    (differentiableAt_of_c1 hL.isOpen hh (hγ.1 h0)) (hγ.2 0 h0)
  have hz := hd.unique hzero
  simpa [hγ0, inner_neg_right] using hz

theorem proposition2 {L : S → E → ℝ} {h : E → ℝ}
    (hL : RegularLossOn Ω L) (hh : ContDiffOn ℝ 1 h Ω) :
    IsConservedOn Ω L h ↔ IsInfinitesimalLawOn Ω L h :=
  ⟨infinitesimal_of_conserved hL hh, conserved_of_infinitesimal hL hh⟩

/-- Definition 3. Independence is pointwise, not independence as functions. -/
def FunctionallyIndependentOn {ι : Type*} (Ω : Set E) (h : ι → E → ℝ) : Prop :=
  ∀ p ∈ Ω, LinearIndependent ℝ (fun i => gradient (h i) p)

/-- Proposition 1: uniqueness is only on [0,∞), not on arbitrary extensions
of a curve to negative times. This avoids a false `∃! γ : ℝ → E` statement. -/
theorem proposition1 (L : S → E → ℝ)
    (hL : RegularLossOn Set.univ L)
    (hlower : ∃ b : ℝ, ∀ s p, b ≤ L s p)
    {n : ℕ} (d : Fin n → S) (hn : 0 < n) (p₀ : E) :
    ∃ γ : ℝ → E,
      γ 0 = p₀ ∧
      (∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt γ (empiricalField L d (γ t)) (Set.Ici 0) t) ∧
      (∀ η : ℝ → E, η 0 = p₀ →
        (∀ t ∈ Set.Ici (0 : ℝ),
          HasDerivWithinAt η (empiricalField L d (η t)) (Set.Ici 0) t) →
        ∀ t ∈ Set.Ici (0 : ℝ), η t = γ t) := by
  classical
  have hLemp : ContDiff ℝ 1 (empiricalLoss L d) := by
    unfold empiricalLoss
    fun_prop
  have hgradLip : LocallyLipschitz (gradient (empiricalLoss L d)) := by
    have h₂ : ContDiff ℝ 2 (empiricalLoss L d) := by
      unfold empiricalLoss
      fun_prop
    have hD : ContDiff ℝ 1 (fderiv ℝ (empiricalLoss L d)) :=
      ((contDiff_succ_iff_fderiv).mp h₂).2
    have hg : ContDiff ℝ 1 (gradient (empiricalLoss L d)) := by
      rw [show gradient (empiricalLoss L d) =
        (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ (empiricalLoss L d) by
          ext x
          simp [gradient]]
      exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp hD
    exact hg.locallyLipschitz
  have hfieldLip : LocallyLipschitz (empiricalField L d) := by
    simpa [empiricalField] using hgradLip.neg
  obtain ⟨J, γ, hJopen, hJconn, h0J, hγ0, hγ, hmax⟩ :=
    ODE.exists_maximal_autonomous_solution hfieldLip p₀
  have henergy : ∀ t ∈ J ∩ Set.Ici (0 : ℝ),
      (∫ s in (0 : ℝ)..t, ‖deriv γ s‖ ^ 2) =
        empiricalLoss L d p₀ - empiricalLoss L d (γ t) := by
    intro t ht
    have hder : ∀ s ∈ Set.Icc (0 : ℝ) t,
        HasDerivAt (fun u => empiricalLoss L d (γ u))
          (-‖gradient (empiricalLoss L d) (γ s)‖^2) s := by
      intro s hs
      have hsJ : s ∈ J := hJconn.out h0J ht.1 hs
      simpa [empiricalField, norm_neg] using
        loss_dissipation (hLemp.differentiable (by norm_num) _) (hγ s hsJ)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder]
    · simp [hγ0, empiricalField] at *
    · exact le_of_lt ht.2
  have hbound : ∀ t ∈ J ∩ Set.Ici (0 : ℝ),
      ‖γ t - p₀‖ ≤
        Real.sqrt (t * (empiricalLoss L d p₀ - b)) := by
    intro t ht
    have hE : ∫ s in (0 : ℝ)..t, ‖deriv γ s‖ ^ 2
        ≤ empiricalLoss L d p₀ - b := by
      rw [henergy t ht]
      linarith [hbelow (γ t)]
    calc
      ‖γ t - p₀‖ =
          ‖∫ s in (0 : ℝ)..t, deriv γ s‖ := by
            rw [← intervalIntegral.integral_deriv_eq_sub]
            · exact hγ.continuousOn.mono
                (hJconn.out_subset h0J ht.1)
            · intro s hs
              exact (hγ s (hJconn.out h0J ht.1 hs)).differentiableAt
      _ ≤ ∫ s in (0 : ℝ)..t, ‖deriv γ s‖ := intervalIntegral.norm_integral_le_of_norm_le
            (fun s _ => le_rfl)
      _ ≤ Real.sqrt t * Real.sqrt
            (∫ s in (0 : ℝ)..t, ‖deriv γ s‖ ^ 2) := by
            simpa using intervalIntegral.integral_norm_le_sqrt_mul_integral_sq
              (fun s => deriv γ s) ht.2
      _ ≤ Real.sqrt t * Real.sqrt (empiricalLoss L d p₀ - b) := by
            gcongr
            exact Real.sqrt_le_sqrt hE
      _ = Real.sqrt (t * (empiricalLoss L d p₀ - b)) := by
            rw [Real.sqrt_mul (by positivity)]
  have hfuture : Set.Ici (0 : ℝ) ⊆ J := by
    apply hmax.Ici_subset_of_no_finite_escape h0J
    intro T hT
    let R := ‖p₀‖ + Real.sqrt (T * (empiricalLoss L d p₀ - b)) + 1
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    intro t ht
    have hbnd := hbound t ⟨ht.1, ht.2.1⟩
    have htT : t ≤ T := ht.2.2
    have hsqrt : Real.sqrt (t * (empiricalLoss L d p₀ - b)) ≤
        Real.sqrt (T * (empiricalLoss L d p₀ - b)) := by
      gcongr
      · exact htT
      · have := hbelow p₀
        linarith
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_norm_add_norm_sub _ _).trans
      (by linarith [hbnd.trans hsqrt])
  refine ⟨γ, hγ0, ?_, ?_⟩
  · intro t ht
    exact (hγ t (hfuture ht)).hasDerivWithinAt
  · intro η hη0 hη t ht
    exact ODE_solution_unique_of_eventually
      (v := fun _ x => empiricalField L d x)
      (s := fun _ => Set.univ)
      (K := 0)
      (hfieldLip.eventually_lipschitzOnWith_at (γ t))
      ((hγ t (hfuture ht)).eventually_hasDerivAt.and
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _))
      ((hη t ht).hasDerivAt (self_mem_nhdsWithin.trans
        (by simpa using ht)).eventually.and
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _))
      (by simpa [hη0, hγ0]) |>.self_of_nhds

/-- The energy identity used in Appendix D.1. -/
theorem loss_dissipation {f : E → ℝ} {γ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t))
    (hγ : HasDerivAt γ (-gradient f (γ t)) t) :
    HasDerivAt (fun s => f (γ s)) (-‖gradient f (γ t)‖ ^ 2) t := by
  simpa [inner_neg_right, real_inner_self_eq_norm_sq] using
    hasDerivAt_observable hf hγ

/-- Lemma 26(3): squared Euclidean distance separates predictions. -/
theorem separates_squared_distance :
    SeparatesPredictions (fun z y : E => ‖z - y‖ ^ 2) := by
  apply separates_of_zero_on_diagonal
  · intro z; simp
  · intro z y hne
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))

end Calculus

end GradientFlowPaper

end -- noncomputable section


/-! ## Source module: GradientFlowPaper/Geometry.lean -/


/-!
Sections 2.1 and 3; Propositions 4--10, Theorem 12, and Appendix A.

The geometry is stated in the C∞ regime explicitly. Proposition 8's
`gradient is closed` direction only needs C². Partial flows have connected
(open, convex) time fibres. Uniqueness of a maximal partial flow means equality
of domains and equality of values *on* that domain, not equality of arbitrary
values of totalized functions outside their domains.
-/

noncomputable section
open Set Function Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

namespace GradientFlowPaper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {S : Type*} {Ω : Set E}

lemma smooth_gradient_on {h : E → ℝ} (hΩ : IsOpen Ω)
    (hh : ContDiffOn ℝ ∞ h Ω) : ContDiffOn ℝ ∞ (gradient h) Ω := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ h) Ω := by
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hh).2
  rw [show gradient h =
    (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ h by
      ext p
      simp [gradient]]
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hD

/-! ## Proposition 4: local factorization -/

def bundleFunctions {ι : Type*} (h : ι → E → ℝ) (p : E) : Vec ι :=
  WithLp.toLp 2 (fun i => h i p)

def LocallyFactorsOn {k : ℕ} (r : ℕ∞ω) (Ω : Set E)
    (h : E → ℝ) (H : E → Vec (Fin k)) : Prop :=
  ∀ p ∈ Ω, ∃ (V : Set E) (U : Set (Vec (Fin k))) (f : Vec (Fin k) → ℝ),
    IsOpen V ∧ p ∈ V ∧ V ⊆ Ω ∧ IsOpen U ∧ H p ∈ U ∧
    MapsTo H V U ∧ ContDiffOn ℝ r f U ∧ EqOn h (f ∘ H) V

lemma fderiv_bundleFunctions_apply {k : ℕ}
    (H : Fin k → E → ℝ) {p u : E}
    (hH : ∀ i, DifferentiableAt ℝ (H i) p) (i : Fin k) :
    (fderiv ℝ (bundleFunctions H) p u) i =
      ⟪gradient (H i) p, u⟫_ℝ := by
  have hB : DifferentiableAt ℝ (bundleFunctions H) p := by
    unfold bundleFunctions
    fun_prop
  have heval :
      HasFDerivAt (fun z : Vec (Fin k) => z i)
        (ContinuousLinearMap.apply ℝ (Vec (Fin k)) i) (bundleFunctions H p) :=
    (ContinuousLinearMap.apply ℝ (Vec (Fin k)) i).hasFDerivAt
  have hc := heval.comp p hB.hasFDerivAt
  have hcoord : (fun x => (bundleFunctions H x) i) = H i := by
    funext x
    rfl
  rw [hcoord] at hc
  have hu := congrArg (fun T : E →L[ℝ] ℝ => T u)
    (hc.unique (hH i).hasFDerivAt)
  simpa [ContinuousLinearMap.comp_apply, inner_gradient_left] using hu

lemma adjoint_fderiv_bundleFunctions_apply {k : ℕ}
    (H : Fin k → E → ℝ) {p : E}
    (hH : ∀ i, DifferentiableAt ℝ (H i) p)
    (y : Vec (Fin k)) :
    (fderiv ℝ (bundleFunctions H) p)† y =
      ∑ i, (y i) • gradient (H i) p := by
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [inner_sum_left, inner_smul_left]
  rw [EuclideanSpace.inner_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_bundleFunctions_apply H hH i]
  simp [real_inner_comm, mul_comm]

lemma bundleFunctions_fderiv_surjective {k : ℕ}
    (H : Fin k → E → ℝ) {p : E}
    (hH : ∀ i, DifferentiableAt ℝ (H i) p)
    (hind : LinearIndependent ℝ (fun i => gradient (H i) p)) :
    Function.Surjective (fderiv ℝ (bundleFunctions H) p) := by
  let T : E →L[ℝ] Vec (Fin k) := fderiv ℝ (bundleFunctions H) p
  have hadj : Function.Injective (T†) := by
    intro y z hyz
    have hsum :
        ∑ i, ((y - z) i) • gradient (H i) p = 0 := by
      rw [← adjoint_fderiv_bundleFunctions_apply H hH (y - z)]
      simp [T, hyz]
    have hyz0 : y - z = 0 := by
      apply WithLp.ext
      intro i
      exact Fintype.linearIndependent_iff.mp hind
        (fun j => (y - z) j) hsum i
    exact sub_eq_zero.mp hyz0
  have hkerAdj : LinearMap.ker (T†) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hadj
  have hrangeOrth : (LinearMap.range T)ᗮ = ⊥ := by
    rw [T.orthogonal_range, hkerAdj]
  have hrange : LinearMap.range T = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact hrangeOrth
  exact LinearMap.range_eq_top.mp hrange

lemma gradient_mem_span_of_locallyFactors {k : ℕ} {r : ℕ∞ω}
    (hr : 1 ≤ r) {Ω : Set E} (hΩ : IsOpen Ω)
    (H : Fin k → E → ℝ) (h : E → ℝ)
    (hH : ∀ i, ContDiffOn ℝ r (H i) Ω)
    (hh : ContDiffOn ℝ r h Ω)
    (hfac : LocallyFactorsOn r Ω h (bundleFunctions H)) :
    ∀ p ∈ Ω, gradient h p ∈
      Submodule.span ℝ (Set.range (fun i => gradient (H i) p)) := by
  intro p hp
  obtain ⟨V, U, f, hV, hpV, hVΩ, hU, hHpU, hmap, hf, heq⟩ :=
    hfac p hp
  have hHat : ∀ i, DifferentiableAt ℝ (H i) p :=
    fun i => ((hH i).of_le hr).differentiableOn (by norm_num)
      |>.differentiableAt (hΩ.mem_nhds hp)
  have hBat : DifferentiableAt ℝ (bundleFunctions H) p := by
    unfold bundleFunctions
    fun_prop
  have hfat : DifferentiableAt ℝ f (bundleFunctions H p) :=
    (hf.of_le hr).differentiableOn (by norm_num)
      |>.differentiableAt (hU.mem_nhds hHpU)
  have hhat : DifferentiableAt ℝ h p :=
    (hh.of_le hr).differentiableOn (by norm_num)
      |>.differentiableAt (hΩ.mem_nhds hp)
  have hevent : h =ᶠ[𝓝 p] (f ∘ bundleFunctions H) := by
    filter_upwards [hV.mem_nhds hpV] with q hq
    exact heq hq
  have hder :
      fderiv ℝ h p =
        (fderiv ℝ f (bundleFunctions H p)).comp
          (fderiv ℝ (bundleFunctions H) p) := by
    rw [hevent.fderiv_eq]
    exact (hfat.hasFDerivAt.comp p hBat.hasFDerivAt).fderiv
  let coeff : Fin k → ℝ := fun i => gradient f (bundleFunctions H p) i
  have hgrad :
      gradient h p = ∑ i, coeff i • gradient (H i) p := by
    apply ext_inner_left ℝ
    intro u
    rw [← inner_gradient_left, hder]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← inner_gradient_left]
    rw [EuclideanSpace.inner_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_bundleFunctions_apply H hHat i]
    simp [coeff, real_inner_comm, mul_comm]
  rw [hgrad]
  exact (Submodule.span ℝ
    (Set.range (fun i => gradient (H i) p))).sum_mem
      (fun i _ =>
        (Submodule.span ℝ
          (Set.range (fun i => gradient (H i) p))).smul_mem _
          (Submodule.subset_span ⟨i, rfl⟩))


lemma fderiv_vanishes_on_bundle_kernel {k : ℕ}
    {Ω : Set E} (H : Fin k → E → ℝ) (h : E → ℝ)
    {q u : E} (hq : q ∈ Ω)
    (hH : ∀ i, DifferentiableAt ℝ (H i) q)
    (hh : DifferentiableAt ℝ h q)
    (hspan : gradient h q ∈
      Submodule.span ℝ (Set.range (fun i => gradient (H i) q)))
    (hu : u ∈ LinearMap.ker (fderiv ℝ (bundleFunctions H) q)) :
    (fderiv ℝ h q) u = 0 := by
  have horth : ∀ i, ⟪gradient (H i) q, u⟫_ℝ = 0 := by
    intro i
    have hcoord := fderiv_bundleFunctions_apply H hH i (u := u)
    have hzero : (fderiv ℝ (bundleFunctions H) q u) i = 0 := by
      rw [LinearMap.mem_ker.mp hu]
      rfl
    linarith
  have hinner : ⟪gradient h q, u⟫_ℝ = 0 := by
    induction hspan using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact horth i
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
    | smul a x hx ih => simp [inner_smul_left, ih]
  rw [← inner_gradient_left]
  exact hinner


lemma constant_on_vertical_implicit_slice
    {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    {U : Set F} {Z : Set K}
    (hU : IsOpen U) (hZ : IsOpen Z) (hZconn : IsPreconnected Z)
    (φ : F × K → E) (B : E → F) (h : E → ℝ)
    (hφ : ContDiffOn ℝ 1 φ (U ×ˢ Z))
    (hBφ : ∀ y ∈ U, ∀ z ∈ Z, B (φ (y,z)) = y)
    (hB : ∀ y ∈ U, ∀ z ∈ Z, DifferentiableAt ℝ B (φ (y,z)))
    (hh : ∀ y ∈ U, ∀ z ∈ Z, DifferentiableAt ℝ h (φ (y,z)))
    (hker : ∀ y ∈ U, ∀ z ∈ Z, ∀ u : E,
      (fderiv ℝ B (φ (y,z))) u = 0 →
      (fderiv ℝ h (φ (y,z))) u = 0) :
    ∀ y ∈ U, ∃ c : ℝ, ∀ z ∈ Z, h (φ (y,z)) = c := by
  intro y hy
  let g : K → ℝ := fun z => h (φ (y,z))
  have hgdiff : DifferentiableOn ℝ g Z := by
    intro z hz
    have hφz : DifferentiableAt ℝ (fun w : K => φ (y,w)) z := by
      have hpair : DifferentiableAt ℝ (fun w : K => (y,w)) z := by fun_prop
      have hφat : DifferentiableAt ℝ φ (y,z) :=
        (hφ.differentiableOn (by norm_num)).differentiableAt
          ((hU.prod hZ).mem_nhds ⟨hy,hz⟩)
      exact hφat.comp z hpair
    exact (hh y hy z hz).comp z hφz |>.differentiableWithinAt
  have hgzero : Z.EqOn (fderiv ℝ g) 0 := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro w
    have hpair :
        HasFDerivAt (fun u : K => (y,u))
          (ContinuousLinearMap.inr ℝ F K) z := by
      fun_prop
    have hφat : DifferentiableAt ℝ φ (y,z) :=
      (hφ.differentiableOn (by norm_num)).differentiableAt
        ((hU.prod hZ).mem_nhds ⟨hy,hz⟩)
    have hsliceφ :
        HasFDerivAt (fun u : K => φ (y,u))
          ((fderiv ℝ φ (y,z)).comp (ContinuousLinearMap.inr ℝ F K)) z :=
      hφat.hasFDerivAt.comp z hpair
    have hBslice :
        (fun u : K => B (φ (y,u))) =ᶠ[𝓝 z] (fun _ => y) := by
      filter_upwards [hZ.mem_nhds hz] with u hu
      exact hBφ y hy u hu
    have hBderiv :
        fderiv ℝ (fun u : K => B (φ (y,u))) z = 0 :=
      hBslice.fderiv_eq.trans (fderiv_const (c := y))
    have hBchain :
        fderiv ℝ (fun u : K => B (φ (y,u))) z =
          (fderiv ℝ B (φ (y,z))).comp
            ((fderiv ℝ φ (y,z)).comp (ContinuousLinearMap.inr ℝ F K)) := by
      exact ((hB y hy z hz).hasFDerivAt.comp z hsliceφ).fderiv.symm
    have hvertical :
        (fderiv ℝ B (φ (y,z)))
          ((fderiv ℝ φ (y,z)) (0,w)) = 0 := by
      have := congrArg (fun T : K →L[ℝ] F => T w)
        (hBchain.symm.trans hBderiv)
      simpa [ContinuousLinearMap.comp_apply] using this
    have hhchain :
        fderiv ℝ g z =
          (fderiv ℝ h (φ (y,z))).comp
            ((fderiv ℝ φ (y,z)).comp (ContinuousLinearMap.inr ℝ F K)) := by
      exact ((hh y hy z hz).hasFDerivAt.comp z hsliceφ).fderiv.symm
    rw [hhchain]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.zero_apply]
    exact hker y hy z hz _ hvertical
  exact hZ.exists_is_const_of_fderiv_eq_zero hZconn hgdiff hgzero


lemma locallyFactors_of_gradient_mem_span {k : ℕ} {r : ℕ∞ω}
    (hr : 1 ≤ r) {Ω : Set E} (hΩ : IsOpen Ω)
    (H : Fin k → E → ℝ) (h : E → ℝ)
    (hH : ∀ i, ContDiffOn ℝ r (H i) Ω)
    (hh : ContDiffOn ℝ r h Ω)
    (hind : FunctionallyIndependentOn Ω H)
    (hspan : ∀ p ∈ Ω, gradient h p ∈
      Submodule.span ℝ (Set.range (fun i => gradient (H i) p))) :
    LocallyFactorsOn r Ω h (bundleFunctions H) := by
  intro p hp
  let B : E → Vec (Fin k) := bundleFunctions H
  let T : E →L[ℝ] Vec (Fin k) := fderiv ℝ B p
  have hBon : ContDiffOn ℝ r B Ω := by
    unfold B bundleFunctions
    fun_prop
  have hBat : ContDiffAt ℝ r B p :=
    (hBon p hp).contDiffAt (hΩ.mem_nhds hp)
  have hBder : HasFDerivAt B T p := by
    exact hBat.differentiableAt (by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hr)) |>.hasFDerivAt
  have hHat : ∀ i, DifferentiableAt ℝ (H i) p :=
    fun i => ((hH i).of_le hr).differentiableOn (by norm_num)
      |>.differentiableAt (hΩ.mem_nhds hp)
  have hsurj : Function.Surjective T := by
    exact bundleFunctions_fderiv_surjective H hHat (hind p hp)
  have hrange : LinearMap.range T = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hr0 : r ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  have hstrict : HasStrictFDerivAt B T p :=
    hBat.hasStrictFDerivAt' hBder hr0
  have hker : (LinearMap.ker T).ClosedComplemented :=
    T.ker_closedComplemented_of_finiteDimensional_range
  let data :=
    hstrict.implicitFunctionDataOfComplemented B T hrange hker
  let e : OpenPartialHomeomorph E (Vec (Fin k) × LinearMap.ker T) :=
    data.toOpenPartialHomeomorph

  have hprodOn : ContDiffOn ℝ r data.prodFun Ω := by
    intro q hq
    have hBq := hBon q hq
    have hright :
        ContDiffWithinAt ℝ r data.rightFun Ω q := by
      dsimp [data, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
      fun_prop
    exact hBq.prodMk hright
  have hprodAt : ContDiffAt ℝ r data.prodFun p :=
    (hprodOn p hp).contDiffAt (hΩ.mem_nhds hp)
  have hfdcont : ContinuousAt (fderiv ℝ data.prodFun) p :=
    hprodAt.continuousAt_fderiv hr0
  have hinv0 : (fderiv ℝ data.prodFun p).IsInvertible :=
    data.isInvertible_fderiv_prodFun
  have hinvN :
      ∀ᶠ q in 𝓝 p, (fderiv ℝ data.prodFun q).IsInvertible :=
    hfdcont.eventually hinv0.eventually_nhds
  have hgood :
      Ω ∩ e.source ∩
        {q | (fderiv ℝ data.prodFun q).IsInvertible} ∈ 𝓝 p := by
    refine inter_mem (inter_mem (hΩ.mem_nhds hp)
      (e.open_source.mem_nhds ?_)) hinvN
    exact data.pt_mem_toOpenPartialHomeomorph_source
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hgood
  have hWsource : W ⊆ e.source := fun q hq => (hWsub hq).2.1
  have hWΩ : W ⊆ Ω := fun q hq => (hWsub hq).1
  have hWinv : ∀ q ∈ W, (fderiv ℝ data.prodFun q).IsInvertible :=
    fun q hq => (hWsub hq).2.2

  let WT : Set (Vec (Fin k) × LinearMap.ker T) := e '' W
  have hWTOpen : IsOpen WT :=
    e.isOpen_image_of_subset_source hWopen hWsource
  have he_p : e p = (B p, 0) := by
    dsimp [e, data]
    exact hstrict.implicitToOpenPartialHomeomorphOfComplemented_self
      B T hrange hker
  have hpWT : (B p, (0 : LinearMap.ker T)) ∈ WT :=
    ⟨p, hpW, he_p⟩
  obtain ⟨U, Z₀, hU, hBpU, hZ₀, h0Z₀, hUZWT⟩ :=
    mem_nhds_prod_iff'.mp (hWTOpen.mem_nhds hpWT)
  obtain ⟨ε, hε, hballZ⟩ := Metric.isOpen_iff.mp hZ₀ 0 h0Z₀
  let Z : Set (LinearMap.ker T) := Metric.ball 0 ε
  have hZ : IsOpen Z := isOpen_ball
  have h0Z : (0 : LinearMap.ker T) ∈ Z := Metric.mem_ball_self hε
  have hZZ₀ : Z ⊆ Z₀ := by
    intro z hz
    exact hballZ hz
  have hUZWT' : U ×ˢ Z ⊆ WT := by
    intro yz hyz
    exact hUZWT ⟨hyz.1, hZZ₀ hyz.2⟩
  have hZconn : IsPreconnected Z :=
    (convex_ball (0 : LinearMap.ker T) ε).isPreconnected

  let φ : Vec (Fin k) × LinearMap.ker T → E := e.symm
  have hφW : ∀ yz ∈ U ×ˢ Z, φ yz ∈ W := by
    intro yz hyz
    rcases hUZWT' hyz with ⟨q, hqW, hqeq⟩
    have hqsource : q ∈ e.source := hWsource hqW
    change e.symm yz ∈ W
    have : e.symm yz = q := by
      rw [← hqeq]
      exact e.left_inv hqsource
    simpa [this] using hqW
  have hφtarget : U ×ˢ Z ⊆ e.target := by
    intro yz hyz
    rcases hUZWT' hyz with ⟨q,hqW,rfl⟩
    exact e.mapsTo (hWsource hqW)
  have hφsmooth : ContDiffOn ℝ r φ (U ×ˢ Z) := by
    intro yz hyz
    have hyzt : yz ∈ e.target := hφtarget hyz
    have hxW : e.symm yz ∈ W := hφW yz hyz
    have hxΩ : e.symm yz ∈ Ω := hWΩ hxW
    have hprodq : ContDiffAt ℝ r data.prodFun (e.symm yz) :=
      (hprodOn _ hxΩ).contDiffAt (hΩ.mem_nhds hxΩ)
    have hinv := hWinv _ hxW
    rcases hinv with ⟨d, hd⟩
    have hder :
        HasFDerivAt e (d : E →L[ℝ] Vec (Fin k) × LinearMap.ker T)
          (e.symm yz) := by
      change HasFDerivAt data.prodFun
        (d : E →L[ℝ] Vec (Fin k) × LinearMap.ker T) (e.symm yz)
      rw [hd]
      exact hprodq.differentiableAt hr0 |>.hasFDerivAt
    exact (e.contDiffAt_symm hyzt hder hprodq).contDiffWithinAt

  have hBφ :
      ∀ y ∈ U, ∀ z ∈ Z, B (φ (y,z)) = y := by
    intro y hy z hz
    have hyz : (y,z) ∈ e.target := hφtarget ⟨hy,hz⟩
    have happ := e.apply_symm_apply hyz
    have hfst := congrArg Prod.fst happ
    simpa [φ, e, data, ImplicitFunctionData.prodFun] using hfst
  have hBφdiff :
      ∀ y ∈ U, ∀ z ∈ Z, DifferentiableAt ℝ B (φ (y,z)) := by
    intro y hy z hz
    have hxΩ := hWΩ (hφW (y,z) ⟨hy,hz⟩)
    exact (hBon.differentiableOn (by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hr)) _ hxΩ)
      |>.differentiableAt (hΩ.mem_nhds hxΩ)
  have hhφdiff :
      ∀ y ∈ U, ∀ z ∈ Z, DifferentiableAt ℝ h (φ (y,z)) := by
    intro y hy z hz
    have hxΩ := hWΩ (hφW (y,z) ⟨hy,hz⟩)
    exact ((hh.of_le hr).differentiableOn (by norm_num) _ hxΩ)
      |>.differentiableAt (hΩ.mem_nhds hxΩ)
  have hvertical :
      ∀ y ∈ U, ∀ z ∈ Z, ∀ u : E,
        (fderiv ℝ B (φ (y,z))) u = 0 →
        (fderiv ℝ h (φ (y,z))) u = 0 := by
    intro y hy z hz u hu
    have hxW := hφW (y,z) ⟨hy,hz⟩
    have hxΩ := hWΩ hxW
    apply fderiv_vanishes_on_bundle_kernel
      (Ω := Ω) H h hxΩ
      (fun i => ((hH i).of_le hr).differentiableOn (by norm_num)
        |>.differentiableAt (hΩ.mem_nhds hxΩ))
      (((hh.of_le hr).differentiableOn (by norm_num))
        |>.differentiableAt (hΩ.mem_nhds hxΩ))
      (hspan _ hxΩ)
    exact LinearMap.mem_ker.mpr hu
  have hconst :=
    constant_on_vertical_implicit_slice
      hU hZ hZconn φ B h
      (hφsmooth.of_le hr) hBφ hBφdiff hhφdiff hvertical

  let f : Vec (Fin k) → ℝ := fun y => h (φ (y,0))
  have hfsmooth : ContDiffOn ℝ r f U := by
    have hslice :
        ContDiffOn ℝ r (fun y : Vec (Fin k) => φ (y,0)) U := by
      exact hφsmooth.comp
        (contDiffOn_id.prodMk contDiffOn_const)
        (fun y hy => ⟨hy,h0Z⟩)
    apply hh.comp hslice
    intro y hy
    exact hWΩ (hφW (y,0) ⟨hy,h0Z⟩)

  let V : Set E := e.symm '' (U ×ˢ Z)
  have hVopen : IsOpen V := by
    exact e.symm.isOpen_image_of_subset_source
      (hU.prod hZ) hφtarget
  have hpV : p ∈ V := by
    refine ⟨(B p, (0 : LinearMap.ker T)), ⟨hBpU,h0Z⟩, ?_⟩
    change e.symm (B p, 0) = p
    rw [← he_p]
    exact e.left_inv (hWsource hpW)
  have hVΩ : V ⊆ Ω := by
    rintro q ⟨yz,hyz,rfl⟩
    exact hWΩ (hφW yz hyz)
  have hmap : MapsTo B V U := by
    rintro q ⟨⟨y,z⟩,hyz,rfl⟩
    simpa [φ] using hBφ y hyz.1 z hyz.2
  have heq : EqOn h (f ∘ B) V := by
    rintro q ⟨⟨y,z⟩,hyz,rfl⟩
    obtain ⟨a, ha⟩ := hconst y hyz.1
    have hz := ha z hyz.2
    have h0 := ha 0 h0Z
    have hBy := hBφ y hyz.1 z hyz.2
    simp only [Function.comp_apply, f]
    rw [hBy]
    exact hz.trans h0.symm
  exact ⟨V, U, f, hVopen, hpV, hVΩ, hU, hBpU,
    hmap, hfsmooth, heq⟩

theorem proposition4
    {k : ℕ} {r : ℕ∞ω} (hr : 1 ≤ r)
    (hΩ : IsOpen Ω) (H : Fin k → E → ℝ) (h : E → ℝ)
    (hH : ∀ i, ContDiffOn ℝ r (H i) Ω) (hh : ContDiffOn ℝ r h Ω)
    (hind : FunctionallyIndependentOn Ω H) :
    (∀ p ∈ Ω, gradient h p ∈
      Submodule.span ℝ (Set.range (fun i => gradient (H i) p))) ↔
      LocallyFactorsOn r Ω h (bundleFunctions H) :=
  ⟨locallyFactors_of_gradient_mem_span hr hΩ H h hH hh hind,
    gradient_mem_span_of_locallyFactors hr hΩ H h hH hh⟩

/-! ## Local flows and infinitesimal invariance -/

structure LocalFlow (Ω : Set E) (v : Field E) where
  domain : Set (ℝ × E)
  open_domain : IsOpen domain
  source_mem : ∀ {t p}, (t, p) ∈ domain → p ∈ Ω
  zero_mem : ∀ p ∈ Ω, (0, p) ∈ domain
  time_convex : ∀ p ∈ Ω, Convex ℝ {t | (t, p) ∈ domain}
  toFun : ℝ → E → E
  smooth : ContDiffOn ℝ ∞ (fun z : ℝ × E => toFun z.1 z.2) domain
  initial : ∀ p ∈ Ω, toFun 0 p = p
  target_mem : ∀ {t p}, (t, p) ∈ domain → toFun t p ∈ Ω
  ode : ∀ {t p}, (t, p) ∈ domain →
    HasDerivAt (fun s => toFun s p) (v (toFun t p)) t
  composition : ∀ {t s p}, (s, p) ∈ domain →
    (t, toFun s p) ∈ domain → (t + s, p) ∈ domain →
    toFun (t + s) p = toFun t (toFun s p)

namespace LocalFlow

variable {v : Field E}

def Extends (ψ φ : LocalFlow Ω v) : Prop :=
  φ.domain ⊆ ψ.domain ∧
    ∀ t p, (t, p) ∈ φ.domain → ψ.toFun t p = φ.toFun t p

def IsMaximal (ψ : LocalFlow Ω v) : Prop :=
  ∀ φ : LocalFlow Ω v, ψ.Extends φ

def Same (ψ φ : LocalFlow Ω v) : Prop :=
  ψ.domain = φ.domain ∧
    ∀ t p, (t, p) ∈ ψ.domain → ψ.toFun t p = φ.toFun t p

/-- Completeness relative to Ω. -/
def IsGlobal (ψ : LocalFlow Ω v) : Prop :=
  ∀ t p, p ∈ Ω → (t, p) ∈ ψ.domain

lemma generator (ψ : LocalFlow Ω v) {p : E} (hp : p ∈ Ω) :
    deriv (fun t => ψ.toFun t p) 0 = v p := by
  simpa only [ψ.initial p hp] using (ψ.ode (ψ.zero_mem p hp)).deriv

lemma maximal_unique {ψ φ : LocalFlow Ω v}
    (hψ : ψ.IsMaximal) (hφ : φ.IsMaximal) : ψ.Same φ := by
  refine ⟨Set.Subset.antisymm (hφ ψ).1 (hψ φ).1, ?_⟩
  intro t p hp
  exact ((hφ ψ).2 t p hp).symm

lemma open_times (ψ : LocalFlow Ω v) (p : E) :
    IsOpen {t : ℝ | (t, p) ∈ ψ.domain} :=
  ψ.open_domain.preimage (continuous_id.prodMk continuous_const)

end LocalFlow

/-- Standard autonomous-ODE background used by Proposition 9.  This is an
explicit Stage-1 dependency, not an assumed theorem constant. -/
class HasMaximalSmoothLocalFlows : Prop where
  exists_maximal :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      {Ω : Set E} {v : Field E}, IsOpen Ω → ContDiffOn ℝ ∞ v Ω →
        ∃ ψ : LocalFlow Ω v, ψ.IsMaximal

/-- Standard ODE/local-flow background required by Proposition 9. -/
theorem exists_maximal_localFlow [HasMaximalSmoothLocalFlows] (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) :
    ∃ ψ : LocalFlow Ω v, ψ.IsMaximal :=
  HasMaximalSmoothLocalFlows.exists_maximal hΩ hv

def FieldCompleteOn (Ω : Set E) (v : Field E) : Prop :=
  ∃ ψ : LocalFlow Ω v, ψ.IsGlobal

def FlowPreserves {v : Field E} (ψ : LocalFlow Ω v) (f : E → ℝ) : Prop :=
  ∀ t p, (t, p) ∈ ψ.domain → f (ψ.toFun t p) = f p

def IsLossSymmetry {v : Field E} (L : S → E → ℝ)
    (ψ : LocalFlow Ω v) : Prop :=
  ∀ s, FlowPreserves ψ (L s)

/-- Propositions 23 and 24 use the same chain-rule argument as Corollaries 6,7. -/
theorem flowPreserves_iff {v : Field E} (ψ : LocalFlow Ω v)
    (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f Ω) :
    FlowPreserves ψ f ↔ ∀ p ∈ Ω, ⟪gradient f p, v p⟫_ℝ = 0 := by
  constructor
  · intro hinv p hp
    have heq : (fun t => f (ψ.toFun t p)) =ᶠ[𝓝 0] (fun _ => f p) := by
      filter_upwards [(ψ.open_times p).mem_nhds (ψ.zero_mem p hp)] with t ht
      exact hinv t p ht
    have hconst : HasDerivAt (fun t => f (ψ.toFun t p)) 0 0 :=
      (hasDerivAt_const 0 (f p)).congr_of_eventuallyEq heq.symm
    have hder := hasDerivAt_observable
      (differentiableAt_of_c1 hΩ hf (ψ.target_mem (ψ.zero_mem p hp)))
      (ψ.ode (ψ.zero_mem p hp))
    simpa only [ψ.initial p hp] using hder.unique hconst
  · intro horth t p htp
    have hp := ψ.source_mem htp
    have hd : ∀ a ∈ {a : ℝ | (a, p) ∈ ψ.domain},
        HasDerivAt (fun a => f (ψ.toFun a p)) 0 a := by
      intro a ha
      have hq := ψ.target_mem ha
      simpa only [horth _ hq] using
        hasDerivAt_observable (differentiableAt_of_c1 hΩ hf hq) (ψ.ode ha)
    have hc := const_on_open_interval (ψ.open_times p) (ψ.time_convex p hp)
      hd htp (ψ.zero_mem p hp)
    simpa only [ψ.initial p hp] using hc

/-- Corollary 6 (and its partial-flow extension, Proposition 23).
For a fixed dataset, take f = empiricalLoss L d. -/
theorem corollary6 {v : Field E} (ψ : LocalFlow Ω v)
    (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f Ω) :
    FlowPreserves ψ f ↔ ∀ p ∈ Ω, ⟪v p, gradient f p⟫_ℝ = 0 := by
  simpa only [real_inner_comm] using flowPreserves_iff ψ hΩ hf

/-- Corollary 7 and Proposition 24. Specializing to global flows gives Corollary 7. -/
theorem corollary7 {L : S → E → ℝ} (hL : RegularLossOn Ω L)
    {v : Field E} (ψ : LocalFlow Ω v) :
    IsLossSymmetry L ψ ↔ ∀ p ∈ Ω, v p ∈ symmetryDistribution L p := by
  constructor
  · intro hs p hp
    rw [mem_symmetryDistribution_iff]
    intro s
    rw [real_inner_comm]
    exact (flowPreserves_iff ψ hL.isOpen (hL.c1 s)).mp (hs s) p hp
  · intro hv s
    apply (flowPreserves_iff ψ hL.isOpen (hL.c1 s)).mpr
    intro p hp
    rw [real_inner_comm]
    exact (mem_symmetryDistribution_iff L p (v p)).mp (hv p hp) s

/-- Proposition 23, the partial-action extension of Corollary 6. -/
theorem proposition23 {v : Field E} (ψ : LocalFlow Ω v)
    (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f Ω) :
    FlowPreserves ψ f ↔ ∀ p ∈ Ω, ⟪v p, gradient f p⟫_ℝ = 0 :=
  corollary6 ψ hΩ hf

/-- Proposition 24, the partial-action extension of Corollary 7. -/
theorem proposition24 {L : S → E → ℝ} (hL : RegularLossOn Ω L)
    {v : Field E} (ψ : LocalFlow Ω v) :
    IsLossSymmetry L ψ ↔ ∀ p ∈ Ω, v p ∈ symmetryDistribution L p :=
  corollary7 hL ψ

/-- Proposition 9, existence plus invariance. -/
theorem proposition9 [HasMaximalSmoothLocalFlows]
    {L : S → E → ℝ} (hL : RegularLossOn Ω L)
    {v : Field E} (hv : ContDiffOn ℝ ∞ v Ω)
    (hvorth : ∀ p ∈ Ω, v p ∈ symmetryDistribution L p) :
    ∃ ψ : LocalFlow Ω v, ψ.IsMaximal ∧ IsLossSymmetry L ψ := by
  obtain ⟨ψ, hmax⟩ := exists_maximal_localFlow hL.isOpen hv
  exact ⟨ψ, hmax, (corollary7 hL ψ).mpr hvorth⟩

/-- Proposition 25 packages the partial-symmetry extensions of Propositions
24 and 9 exactly as in Appendix E.6. -/
theorem proposition25 [HasMaximalSmoothLocalFlows]
    {L : S → E → ℝ} (hL : RegularLossOn Ω L) :
    (∀ {v : Field E} (ψ : LocalFlow Ω v),
      IsLossSymmetry L ψ →
      ∀ p ∈ Ω, v p ∈ symmetryDistribution L p) ∧
    (∀ {v : Field E}, ContDiffOn ℝ ∞ v Ω →
      (∀ p ∈ Ω, v p ∈ symmetryDistribution L p) →
      ∃ ψ : LocalFlow Ω v, ψ.IsMaximal ∧ IsLossSymmetry L ψ) := by
  constructor
  · intro v ψ hψ
    exact (proposition24 hL ψ).mp hψ
  · intro v hv horth
    exact proposition9 hL hv horth

theorem maximal_global_of_complete {v : Field E} {ψ : LocalFlow Ω v}
    (hmax : ψ.IsMaximal) (hc : FieldCompleteOn Ω v) : ψ.IsGlobal := by
  obtain ⟨φ, hφ⟩ := hc
  intro t p hp
  exact (hmax φ).1 (hφ t p hp)

/-! ## Proposition 5: a genuinely connected Lie-group statement -/

section LieGroup

variable {A Γ : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [Group Γ] [TopologicalSpace Γ]
  [ChartedSpace A Γ] [LieGroup (𝓘(ℝ, A)) ∞ Γ] [ConnectedSpace Γ]


lemma isLocallyConstant_of_mfderiv_eq_zero
    {M H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ H H)
    [IsManifold I 1 M]
    (F : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ, ℝ) 1 F)
    (hzero : ∀ x, mfderiv I 𝓘(ℝ, ℝ) F x = 0) :
    IsLocallyConstant F := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let e := extChartAt I x
  have hxsrc : x ∈ e.source := mem_extChartAt_source x
  have hxtgt : e x ∈ e.target := e.map_source hxsrc
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp e.open_target (e x) hxtgt
  let B : Set H := Metric.ball (e x) ε
  have hBopen : IsOpen B := isOpen_ball
  have hxB : e x ∈ B := Metric.mem_ball_self hε
  have hBtgt : B ⊆ e.target := hball
  let G : H → ℝ := fun y => F (e.symm y)
  have hGdiff : DifferentiableOn ℝ G B := by
    intro y hy
    have hyt := hBtgt hy
    have hsymmMD :
        MDiffAt I I (e.symm) y :=
      e.mdifferentiableAt_symm hyt
    have hFMD :
        MDiffAt I 𝓘(ℝ, ℝ) F (e.symm y) :=
      hF.mdifferentiableAt (by norm_num)
    have hcomp := hFMD.comp y hsymmMD
    simpa [G, mdifferentiableAt_iff_differentiableAt] using hcomp
  have hGzero : B.EqOn (fderiv ℝ G) 0 := by
    intro y hy
    have hyt := hBtgt hy
    have hsymmMD :
        MDiffAt I I (e.symm) y :=
      e.mdifferentiableAt_symm hyt
    have hFMD :
        MDiffAt I 𝓘(ℝ, ℝ) F (e.symm y) :=
      hF.mdifferentiableAt (by norm_num)
    have hchain :=
      mfderiv_comp (I' := I) y hFMD hsymmMD
    rw [hzero] at hchain
    have hmfzero :
        mfderiv I 𝓘(ℝ, ℝ) G y = 0 := by
      simpa [G, ContinuousLinearMap.zero_comp] using hchain
    simpa [mfderiv_eq_fderiv] using hmfzero
  obtain ⟨c₀, hc₀⟩ :=
    hBopen.exists_is_const_of_fderiv_eq_zero
      (convex_ball (e x) ε).isPreconnected hGdiff hGzero
  let U : Set M := e.symm '' B
  have hUopen : IsOpen U :=
    e.symm.isOpen_image_of_subset_source hBopen hBtgt
  have hxU : x ∈ U := by
    refine ⟨e x, hxB, ?_⟩
    exact e.left_inv hxsrc
  refine ⟨U, hUopen, hxU, ?_⟩
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  have hyeq : G y = G (e x) := by
    exact (hc₀ y hy).trans (hc₀ (e x) hxB).symm
  simpa [G, e.left_inv hxsrc] using hyeq


lemma mfderiv_rightMul_surjective (g : Γ) :
    Function.Surjective
      (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, A)) (fun h : Γ => h * g) 1) := by
  let Rg : Γ → Γ := fun h => h * g
  let Rginv : Γ → Γ := fun h => h * g⁻¹
  have hRg : ContMDiff (𝓘(ℝ, A)) (𝓘(ℝ, A)) ∞ Rg :=
    contMDiff_mul_right
  have hRginv : ContMDiff (𝓘(ℝ, A)) (𝓘(ℝ, A)) ∞ Rginv :=
    contMDiff_mul_right
  let dR :=
    mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, A)) Rg 1
  let dRi :=
    mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, A)) Rginv g
  have hcomp :
      dR.comp dRi = ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, A)) g) := by
    have hchain :=
      mfderiv_comp (I' := 𝓘(ℝ, A)) g
        (hRg.mdifferentiableAt (by simp))
        (hRginv.mdifferentiableAt (by simp))
    have heq :
        (Rg ∘ Rginv) = fun h : Γ => h := by
      funext h
      simp [Rg, Rginv, Function.comp_def, mul_assoc]
    rw [heq, mfderiv_id] at hchain
    simpa [dR, dRi, Rg, Rginv] using hchain.symm
  intro b
  refine ⟨dRi b, ?_⟩
  have hb := congrArg (fun T :
      TangentSpace (𝓘(ℝ, A)) g →L[ℝ]
        TangentSpace (𝓘(ℝ, A)) g => T b) hcomp
  simpa [dR, ContinuousLinearMap.comp_apply] using hb

lemma orbit_eval_mfderiv_zero_of_identity_condition
    (act : Γ → E → E)
    (hactmul : ∀ g h p, act (g * h) p = act g (act h p))
    (hactΩ : ∀ g p, p ∈ Ω → act g p ∈ Ω)
    (hsmooth : ∀ p ∈ Ω,
      ContMDiff (𝓘(ℝ, A)) (𝓘(ℝ, E)) ∞ (fun g => act g p))
    (hΩ : IsOpen Ω) (f : E → ℝ) (hf : ContDiffOn ℝ 1 f Ω)
    (hinf : ∀ p ∈ Ω, ∀ a : TangentSpace (𝓘(ℝ, A)) (1 : Γ),
      (fderiv ℝ f p)
        ((mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun g => act g p) 1) a) = 0)
    {p : E} (hp : p ∈ Ω) :
    ∀ g : Γ,
      mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, ℝ))
        (fun h : Γ => f (act h p)) g = 0 := by
  intro g
  let q : E := act g p
  have hq : q ∈ Ω := hactΩ g p hp
  let orbitP : Γ → E := fun h => act h p
  let orbitQ : Γ → E := fun h => act h q
  let Rg : Γ → Γ := fun h => h * g
  have horbit :
      orbitQ = orbitP ∘ Rg := by
    funext h
    simp [orbitQ, orbitP, Rg, q, Function.comp_def, hactmul]
  have hRgMD :
      MDiffAt (𝓘(ℝ, A)) (𝓘(ℝ, A)) Rg 1 :=
    contMDiff_mul_right.mdifferentiableAt (by simp)
  have hPmd :
      MDiffAt (𝓘(ℝ, A)) (𝓘(ℝ, E)) orbitP g :=
    (hsmooth p hp).mdifferentiableAt (by simp)
  have hQmd :
      MDiffAt (𝓘(ℝ, A)) (𝓘(ℝ, E)) orbitQ 1 :=
    (hsmooth q hq).mdifferentiableAt (by simp)
  have horbitDer :
      mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) orbitQ 1 =
        (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) orbitP g).comp
          (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, A)) Rg 1) := by
    rw [horbit]
    exact mfderiv_comp (I' := 𝓘(ℝ, A)) 1 hPmd hRgMD
  have hfat : DifferentiableAt ℝ f q :=
    differentiableAt_of_c1 hΩ hf hq
  have hFmd :
      MDiffAt (𝓘(ℝ, A)) (𝓘(ℝ, ℝ))
        (fun h : Γ => f (orbitP h)) g :=
    hfat.contMDiffAt.contMDiffAt.comp g hPmd
      |>.mdifferentiableAt (by norm_num)
  apply ContinuousLinearMap.ext
  intro b
  obtain ⟨a, ha⟩ := mfderiv_rightMul_surjective (A := A) (Γ := Γ) g b
  have hzero := hinf q hq a
  have hqchain :
      (fderiv ℝ f q)
        ((mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) orbitQ 1) a) = 0 :=
    hzero
  rw [horbitDer, ContinuousLinearMap.comp_apply, ha] at hqchain
  have hchain :=
    mfderiv_comp (I' := 𝓘(ℝ, E)) g
      hfat.contDiffAt.contMDiffAt.mdifferentiableAt hPmd
  have happ := congrArg (fun T :
      TangentSpace (𝓘(ℝ, A)) g →L[ℝ]
        TangentSpace (𝓘(ℝ, ℝ)) (f q) => T b) hchain
  simpa [orbitP, q, mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply] using hqchain

/-- Equation (5) written without an adjoint: every tangent direction at the
identity annihilates the loss. This is equivalent to the transposed equation. -/
theorem proposition5
    (act : Γ → E → E)
    (hact1 : ∀ p, act 1 p = p)
    (hactmul : ∀ g h p, act (g * h) p = act g (act h p))
    (hactΩ : ∀ g p, p ∈ Ω → act g p ∈ Ω)
    (hsmooth : ∀ p ∈ Ω,
      ContMDiff (𝓘(ℝ, A)) (𝓘(ℝ, E)) ∞ (fun g => act g p))
    (hΩ : IsOpen Ω) (f : E → ℝ) (hf : ContDiffOn ℝ 1 f Ω) :
    (∀ g p, p ∈ Ω → f (act g p) = f p) ↔
      (∀ p ∈ Ω, ∀ a : TangentSpace (𝓘(ℝ, A)) (1 : Γ),
        (fderiv ℝ f p)
          ((mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun g => act g p) 1) a) = 0) := by
  constructor
  · intro hinv p hp a
    let orbit : Γ → E := fun g => act g p
    let F : Γ → ℝ := fun g => f (orbit g)
    have hFconst : F = fun _ : Γ => f p := by
      funext g
      exact hinv g p hp
    have horbitMD :
        MDiffAt (𝓘(ℝ, A)) (𝓘(ℝ, E)) orbit 1 :=
      (hsmooth p hp).mdifferentiableAt (by simp)
    have hfat : DifferentiableAt ℝ f p :=
      differentiableAt_of_c1 hΩ hf hp
    have hchain :=
      mfderiv_comp (I' := 𝓘(ℝ, E)) 1
        hfat.contDiffAt.contMDiffAt.mdifferentiableAt horbitMD
    have hzero :
        mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, ℝ)) F 1 = 0 := by
      rw [hFconst, mfderiv_const]
    have happ := congrArg
      (fun T : TangentSpace (𝓘(ℝ, A)) (1 : Γ) →L[ℝ]
          TangentSpace (𝓘(ℝ, ℝ)) (f p) => T a)
      hchain
    rw [hzero] at happ
    simpa [F, orbit, hact1, mfderiv_eq_fderiv,
      ContinuousLinearMap.comp_apply] using happ.symm
  · intro hinf g p hp
    let F : Γ → ℝ := fun h => f (act h p)
    have hFmd : ContMDiff (𝓘(ℝ, A)) (𝓘(ℝ, ℝ)) 1 F := by
      intro h
      have hq : act h p ∈ Ω := hactΩ h p hp
      have hforbit :
          ContMDiffAt (𝓘(ℝ, A)) (𝓘(ℝ, E)) ∞
            (fun k : Γ => act k p) h :=
        (hsmooth p hp) h
      have hfat : ContDiffAt ℝ 1 f (act h p) :=
        (hf _ hq).contDiffAt (hΩ.mem_nhds hq)
      exact hfat.contMDiffAt.comp h
        (hforbit.of_le (by norm_num))
    have hzero :
        ∀ h : Γ,
          mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, ℝ)) F h = 0 :=
      orbit_eval_mfderiv_zero_of_identity_condition
        act hactmul hactΩ hsmooth hΩ f hf hinf hp
    have hloc : IsLocallyConstant F :=
      isLocallyConstant_of_mfderiv_eq_zero
        (𝓘(ℝ, A)) F hFmd hzero
    have heq : F g = F 1 :=
      hloc.apply_eq_of_isPreconnected isPreconnected_univ
        (Set.mem_univ g) (Set.mem_univ 1)
    simpa [F, hact1] using heq

/-- One-parameter subgroup data used in Appendix C. -/
def IsOneParameterSubgroup (φ : ℝ → Γ) : Prop :=
  φ 0 = 1 ∧ (∀ s t, φ (s + t) = φ s * φ t) ∧
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, A)) ∞ φ

def InfinitesimalGenerator (φ : ℝ → Γ) :
    TangentSpace (𝓘(ℝ, A)) (1 : Γ) :=
  (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, A)) φ 0) 1

def oneParameterProduct (φ : Fin s → ℝ → Γ) :
    List (Fin s × ℝ) → Γ
  | [] => 1
  | (i,t) :: xs => oneParameterProduct φ xs * φ i t

def ProductsGenerate (φ : Fin s → ℝ → Γ) : Prop :=
  ∀ g : Γ, ∃ xs : List (Fin s × ℝ), oneParameterProduct φ xs = g

/-- Fulton--Harris generation theorem quoted as Theorem 22. This is an
external background result in Stage 1. -/
class HasConnectedLieGroupGeneration
    (A Γ : Type*)
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [Group Γ] [TopologicalSpace Γ] [ChartedSpace A Γ]
    [LieGroup (𝓘(ℝ, A)) ∞ Γ] [ConnectedSpace Γ] : Prop where
  generate :
    ∀ {s : ℕ} (φ : Fin s → ℝ → Γ),
      (∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) →
      Submodule.span ℝ
        (Set.range (fun i =>
          InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) = ⊤ →
      ProductsGenerate φ

/-- Theorem 22: if the infinitesimal generators of finitely many
one-parameter subgroups span the Lie algebra of a connected Lie group, finite
products of those one-parameter subgroups generate the group. -/
theorem theorem22 [HasConnectedLieGroupGeneration A Γ]
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i))
    (hspan : Submodule.span ℝ
      (Set.range (fun i =>
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) = ⊤) :
    ProductsGenerate φ :=
  HasConnectedLieGroupGeneration.generate φ hφ hspan

end LieGroup

/-! ## Closed vector fields, potentials, and Corollary 10 -/

/-- Coordinate-free form of the cross-partial identities (8). -/
def IsClosedFieldOn (Ω : Set E) (v : Field E) : Prop :=
  ∀ p ∈ Ω, ∀ a b : E,
    ⟪(fderiv ℝ v p) a, b⟫_ℝ = ⟪a, (fderiv ℝ v p) b⟫_ℝ

def IsPotentialOn (Ω : Set E) (v : Field E) (h : E → ℝ) : Prop :=
  ∀ p ∈ Ω, gradient h p = v p

theorem gradient_isClosed (hΩ : IsOpen Ω) {h : E → ℝ}
    (hh : ContDiffOn ℝ 2 h Ω) : IsClosedFieldOn Ω (gradient h) := by
  intro p hp a b
  have hp2 : ContDiffAt ℝ 2 h p :=
    (hh p hp).contDiffAt (hΩ.mem_nhds hp)
  have hgrad :
      HasFDerivAt (gradient h)
        ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp
          (fderiv ℝ (fderiv ℝ h) p)) p := by
    have hD :
        HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) p) p :=
      (hp2.fderiv_right (by norm_num)).hasFDerivAt
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ E).symm.contDiff.contDiffAt.hasFDerivAt.comp p hD
  rw [hgrad.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have hs := hp2.isSymmSndFDerivAt (by norm_num)
  change
    (fderiv ℝ (fderiv ℝ h) p a) b =
      (fderiv ℝ (fderiv ℝ h) p b) a
  exact hs a b

def radialPotential (v : Field E) (a p : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, ⟪v (a + t • (p - a)), p - a⟫_ℝ

def fieldOneForm (v : Field E) (p : E) : E →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ E) (v p)

lemma hasFDerivAt_fieldOneForm {v : Field E} {p : E}
    (hv : DifferentiableAt ℝ v p) :
    HasFDerivAt (fieldOneForm v)
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp
        (fderiv ℝ v p)) p := by
  exact (InnerProductSpace.toDual ℝ E).contDiff.contDiffAt.hasFDerivAt.comp
    p hv.hasFDerivAt

lemma fderiv_fieldOneForm_apply {v : Field E} {p : E}
    (hv : DifferentiableAt ℝ v p) (x y : E) :
    (fderiv ℝ (fieldOneForm v) p x) y =
      ⟪fderiv ℝ v p x, y⟫_ℝ := by
  rw [(hasFDerivAt_fieldOneForm hv).fderiv]
  simp [fieldOneForm, ContinuousLinearMap.comp_apply]

lemma fieldOneForm_fderiv_symmetric {v : Field E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (hclosed : IsClosedFieldOn Ω v) :
    ∀ p ∈ Ω, ∀ x y : E,
      fderiv ℝ (fieldOneForm v) p x y =
        fderiv ℝ (fieldOneForm v) p y x := by
  intro p hp x y
  have hvp : DifferentiableAt ℝ v p :=
    (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hp)
  rw [fderiv_fieldOneForm_apply hvp, fderiv_fieldOneForm_apply hvp]
  exact (hclosed p hp x y).trans real_inner_comm

lemma poincare_convex_open
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {v : Field E} (hv : ContDiffOn ℝ ∞ v U)
    (hclosed : IsClosedFieldOn U v) :
    ∃ h : E → ℝ, ContDiffOn ℝ ∞ h U ∧ IsPotentialOn U v h := by
  have hωdiff : DifferentiableOn ℝ (fieldOneForm v) U := by
    intro p hp
    have hvp : DifferentiableAt ℝ v p :=
      (hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
    exact (hasFDerivAt_fieldOneForm hvp).differentiableAt.differentiableWithinAt
  have hωsym :
      ∀ p ∈ U, ∀ x y : E,
        fderiv ℝ (fieldOneForm v) p x y =
          fderiv ℝ (fieldOneForm v) p y x :=
    fieldOneForm_fderiv_symmetric hU hv hclosed
  obtain ⟨h, hh⟩ :=
    hconv.exists_forall_hasFDerivAt_of_fderiv_symmetric
      hU hωdiff hωsym
  have hpot : IsPotentialOn U v h := by
    intro p hp
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient, (hh p hp).fderiv]
    rfl
  have hdiff : DifferentiableOn ℝ h U :=
    fun p hp => (hh p hp).differentiableAt.differentiableWithinAt
  have hωsmooth : ContDiffOn ℝ ∞ (fieldOneForm v) U := by
    exact (InnerProductSpace.toDual ℝ E).contDiff.comp_contDiffOn hv
      (fun _ _ => Set.mem_univ _)
  have hfderSmooth : ContDiffOn ℝ ∞ (fderiv ℝ h) U :=
    hωsmooth.congr (fun p hp => (hh p hp).fderiv)
  have hsmooth : ContDiffOn ℝ ∞ h U :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hU).2 ⟨hdiff, hfderSmooth⟩
  exact ⟨h, hsmooth, hpot⟩


lemma radialPotential_eq_curveIntegral (v : Field E) (a p : E) :
    radialPotential v a p =
      ∫ᶜ x in Path.segment a p, fieldOneForm v x := by
  unfold radialPotential
  rw [curveIntegral_segment]
  apply intervalIntegral.integral_congr
  intro t ht
  simp [fieldOneForm, AffineMap.lineMap_apply, real_inner_comm]

lemma convexHull_triple_subset_of_starConvex
    {Ω : Set E} {a p q : E}
    (hstar : StarConvex ℝ a Ω)
    (hpq : segment ℝ p q ⊆ Ω) :
    convexHull ℝ {a, p, q} ⊆ Ω := by
  rw [← convexJoin_singleton_segment]
  rintro x hx
  rw [mem_convexJoin] at hx
  obtain ⟨a', ha', y, hy, hxy⟩ := hx
  simp only [mem_singleton_iff] at ha'
  subst a'
  exact hstar.segment_subset (hpq hy) hxy

lemma radialPotential_hasFDerivAt
    {Ω : Set E} (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (hclosed : IsClosedFieldOn Ω v)
    {a p : E} (ha : a ∈ Ω) (hstar : StarConvex ℝ a Ω)
    (hp : p ∈ Ω) :
    HasFDerivAt (radialPotential v a) (fieldOneForm v p) p := by
  obtain ⟨ε, hε, hballΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  let B : Set E := Metric.ball p ε
  have hpB : p ∈ B := Metric.mem_ball_self hε
  have hBopen : IsOpen B := isOpen_ball
  have hBconv : Convex ℝ B := convex_ball p ε
  have hBΩ : B ⊆ Ω := hballΩ
  have hωcont : ContinuousOn (fieldOneForm v) B := by
    exact ((InnerProductSpace.toDual ℝ E).continuous.comp_continuousOn
      (hv.continuousOn.mono hBΩ))
  have hsegWithin :
      HasFDerivWithinAt
        (fun q => ∫ᶜ x in Path.segment p q, fieldOneForm v x)
        (fieldOneForm v p) B p :=
    HasFDerivWithinAt.curveIntegral_segment_source hBconv hωcont hpB
  have hseg :
      HasFDerivAt
        (fun q => ∫ᶜ x in Path.segment p q, fieldOneForm v x)
        (fieldOneForm v p) p :=
    hsegWithin.hasFDerivAt (hBopen.mem_nhds hpB)
  have hsum :
      HasFDerivAt
        (fun q => radialPotential v a p +
          ∫ᶜ x in Path.segment p q, fieldOneForm v x)
        (fieldOneForm v p) p :=
    hseg.const_add _
  have heq :
      radialPotential v a =ᶠ[𝓝 p]
        (fun q => radialPotential v a p +
          ∫ᶜ x in Path.segment p q, fieldOneForm v x) := by
    filter_upwards [Metric.ball_mem_nhds p hε] with q hq
    have hpqB : segment ℝ p q ⊆ B :=
      hBconv.segment_subset hpB hq
    have hpqΩ : segment ℝ p q ⊆ Ω := hpqB.trans hBΩ
    let T : Set E := convexHull ℝ {a, p, q}
    have hTconv : Convex ℝ T := convex_convexHull ℝ _
    have hTΩ : T ⊆ Ω :=
      convexHull_triple_subset_of_starConvex hstar hpqΩ
    have haT : a ∈ T :=
      subset_convexHull ℝ _ (by simp [T])
    have hpT : p ∈ T :=
      subset_convexHull ℝ _ (by simp [T])
    have hqT : q ∈ T :=
      subset_convexHull ℝ _ (by simp [T])
    have hω :
        ∀ x ∈ T,
          HasFDerivWithinAt (fieldOneForm v)
            (fderiv ℝ (fieldOneForm v) x) T x := by
      intro x hx
      have hxΩ := hTΩ hx
      have hvx : DifferentiableAt ℝ v x :=
        (hv.differentiableOn (by simp)).differentiableAt
          (hΩ.mem_nhds hxΩ)
      exact (hasFDerivAt_fieldOneForm hvx).hasFDerivWithinAt
    have hsym :
        ∀ x ∈ T, ∀ u ∈ tangentConeAt ℝ T x,
          ∀ w ∈ tangentConeAt ℝ T x,
            fderiv ℝ (fieldOneForm v) x u w =
              fderiv ℝ (fieldOneForm v) x w u := by
      intro x hx u hu w hw
      exact fieldOneForm_fderiv_symmetric hΩ hv hclosed
        x (hTΩ hx) u w
    have htri :=
      hTconv.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
        hω hsym haT hpT hqT
    rw [radialPotential_eq_curveIntegral, radialPotential_eq_curveIntegral]
    exact htri.symm
  exact hsum.congr_of_eventuallyEq heq

lemma poincare_star_mathlib
    {Ω : Set E} (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (hclosed : IsClosedFieldOn Ω v)
    {a : E} (ha : a ∈ Ω) (hstar : StarConvex ℝ a Ω) :
    ContDiffOn ℝ ∞ (radialPotential v a) Ω ∧
      IsPotentialOn Ω v (radialPotential v a) := by
  have hder :
      ∀ p ∈ Ω,
        HasFDerivAt (radialPotential v a) (fieldOneForm v p) p :=
    fun p hp => radialPotential_hasFDerivAt hΩ hv hclosed ha hstar hp
  have hpot : IsPotentialOn Ω v (radialPotential v a) := by
    intro p hp
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient, (hder p hp).fderiv]
    rfl
  have hdiff : DifferentiableOn ℝ (radialPotential v a) Ω :=
    fun p hp => (hder p hp).differentiableAt.differentiableWithinAt
  have hωsmooth : ContDiffOn ℝ ∞ (fieldOneForm v) Ω := by
    exact (InnerProductSpace.toDual ℝ E).contDiff.comp_contDiffOn hv
      (fun _ _ => Set.mem_univ _)
  have hfder :
      ContDiffOn ℝ ∞ (fderiv ℝ (radialPotential v a)) Ω :=
    hωsmooth.congr (fun p hp => (hder p hp).fderiv)
  have hsmooth : ContDiffOn ℝ ∞ (radialPotential v a) Ω :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).2 ⟨hdiff, hfder⟩
  exact ⟨hsmooth, hpot⟩

/-- Global Poincaré lemma on a star-shaped domain. -/
theorem poincare_star
    (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (hclosed : IsClosedFieldOn Ω v)
    {a : E} (ha : a ∈ Ω) (hstar : StarConvex ℝ a Ω) :
    ContDiffOn ℝ ∞ (radialPotential v a) Ω ∧
      IsPotentialOn Ω v (radialPotential v a) :=
  poincare_star_mathlib hΩ hv hclosed ha hstar

/-- Local Poincaré lemma, with a connected ball and uniqueness modulo constants. -/
theorem poincare_local (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (hclosed : IsClosedFieldOn Ω v)
    {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (h : E → ℝ),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧ IsPreconnected U ∧
      ContDiffOn ℝ ∞ h U ∧ IsPotentialOn U v h := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  have hpball : p ∈ Metric.ball p ε := Metric.mem_ball_self hε
  obtain ⟨h, hh, hpot⟩ :=
    poincare_convex_open isOpen_ball (convex_ball p ε)
      (hv.mono hball) (fun q hq => hclosed q (hball hq))
  exact ⟨Metric.ball p ε, h, isOpen_ball, hpball,
    hball, (convex_ball p ε).isPreconnected, hh, hpot⟩

theorem potential_unique_mod_constant (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {v : Field E} {h k : E → ℝ}
    (hh : ContDiffOn ℝ 1 h Ω) (hk : ContDiffOn ℝ 1 k Ω)
    (hhv : IsPotentialOn Ω v h) (hkv : IsPotentialOn Ω v k) :
    ∃ c : ℝ, ∀ p ∈ Ω, h p = k p + c := by
  apply hΩ.exists_eq_add_of_fderiv_eq hc
    (hh.differentiableOn (by norm_num)) (hk.differentiableOn (by norm_num))
  intro p hp
  ext a
  rw [← inner_gradient_left, ← inner_gradient_left, hhv p hp, hkv p hp]

/-- Proposition 8, forward direction; the regularity requirement is explicit. -/
theorem proposition8_forward {L : S → E → ℝ}
    (hL : RegularLossOn Ω L) {h : E → ℝ}
    (hh : ContDiffOn ℝ 2 h Ω) (hc : IsConservedOn Ω L h) :
    IsClosedFieldOn Ω (gradient h) ∧ IsInfinitesimalLawOn Ω L h := by
  exact ⟨gradient_isClosed hL.isOpen hh,
    (proposition2 hL (hh.of_le (by norm_num))).mp hc⟩

/-- Corollary 10: a smooth conserved potential generates a unique maximal
partial symmetry. Arbitrary restrictions of that flow are not claimed unique. -/
theorem corollary10_forward [HasMaximalSmoothLocalFlows]
    {L : S → E → ℝ}
    (hL : RegularLossOn Ω L) {h : E → ℝ}
    (hh : ContDiffOn ℝ ∞ h Ω)
    (hc : IsConservedOn Ω L h) :
    ∃ ψ : LocalFlow Ω (gradient h),
      ψ.IsMaximal ∧ IsLossSymmetry L ψ ∧
      (∀ φ : LocalFlow Ω (gradient h), φ.IsMaximal → ψ.Same φ) := by
  obtain ⟨ψ, hmax, hsym⟩ := proposition9 hL (smooth_gradient_on hL.isOpen hh)
    ((proposition2 hL (hh.of_le (by simp))).mp hc)
  exact ⟨ψ, hmax, hsym, fun φ hφ => LocalFlow.maximal_unique hmax hφ⟩

/-- Restriction of regular loss assumptions to an open subdomain. -/
lemma RegularLossOn.mono {L : S → E → ℝ} (hL : RegularLossOn Ω L)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ Ω) : RegularLossOn U L := by
  refine ⟨hU, fun s => (hL.c1 s).mono hsub, ?_⟩
  intro s p hp
  obtain ⟨V, hV, hpV, hVΩ, K, hK⟩ := hL.localLip s p (hsub hp)
  exact ⟨U ∩ V, hU.inter hV, ⟨hp, hpV⟩, Set.inter_subset_left,
    K, hK.mono Set.inter_subset_right⟩

theorem corollary10_reverse
    {L : S → E → ℝ}
    (hL : RegularLossOn Ω L) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (ψ : LocalFlow Ω v)
    (hsym : IsLossSymmetry L ψ) (hclosed : IsClosedFieldOn Ω v)
    {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (h : E → ℝ), IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ h U ∧ IsPotentialOn U v h ∧ IsConservedOn U L h := by
  obtain ⟨U, h, hU, hpU, hsub, _, hh, hpot⟩ :=
    poincare_local hL.isOpen hv hclosed hp
  refine ⟨U, h, hU, hpU, hsub, hh, hpot, ?_⟩
  apply (proposition2 (hL.mono hU hsub) (hh.of_le (by simp))).mpr
  intro q hq
  rw [hpot q hq]
  exact (corollary7 hL ψ).mp hsym q (hsub hq)

/-- Proposition 8, local reverse direction, directly from a closed field. -/
theorem proposition8_local [HasMaximalSmoothLocalFlows]
    {L : S → E → ℝ}
    (hL : RegularLossOn Ω L) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (hclosed : IsClosedFieldOn Ω v)
    (horth : ∀ p ∈ Ω, v p ∈ symmetryDistribution L p)
    {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (h : E → ℝ), IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ h U ∧ IsPotentialOn U v h ∧ IsConservedOn U L h := by
  obtain ⟨ψ, _, hψ⟩ := proposition9 hL hv horth
  exact corollary10_reverse hL hv ψ hψ hclosed hp

/-- Proposition 8 on a star-shaped domain; the potential is explicit. -/
theorem proposition8_star [HasStarPoincareLemma E]
    {L : S → E → ℝ}
    (hL : RegularLossOn Ω L) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) (hclosed : IsClosedFieldOn Ω v)
    (horth : ∀ p ∈ Ω, v p ∈ symmetryDistribution L p)
    {a : E} (ha : a ∈ Ω) (hstar : StarConvex ℝ a Ω) :
    IsPotentialOn Ω v (radialPotential v a) ∧
      IsConservedOn Ω L (radialPotential v a) := by
  obtain ⟨hh, hpot⟩ := poincare_star hL.isOpen hv hclosed ha hstar
  refine ⟨hpot, (proposition2 hL (hh.of_le (by simp))).mpr ?_⟩
  intro p hp
  rw [hpot p hp]
  exact horth p hp

/-! ## Lie completion and the symmetry--conservation gap -/

def lieBracket (v w : Field E) : Field E :=
  fun p => (fderiv ℝ w p) (v p) - (fderiv ℝ v p) (w p)

def IsSectionOn (Ω : Set E) (D : Distribution E) (v : Field E) : Prop :=
  ContDiffOn ℝ ∞ v Ω ∧ ∀ p ∈ Ω, v p ∈ D p

/-- Local smooth frames: a regular smooth distribution, not necessarily a
trivial vector bundle with a single global frame. -/
def HasLocalSmoothFrame (Ω : Set E) (D : Distribution E) : Prop :=
  ∀ p ∈ Ω, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
    ∃ (n : ℕ) (v : Fin n → Field E),
      (∀ i, ContDiffOn ℝ ∞ (v i) U) ∧
      ∀ q ∈ U, LinearIndependent ℝ (fun i => v i q) ∧
        D q = Submodule.span ℝ (Set.range (fun i => v i q))

def ConstantRankOn (Ω : Set E) (D : Distribution E) (r : ℕ) : Prop :=
  ∀ p ∈ Ω, Module.finrank ℝ (D p) = r

def InvolutiveOn (Ω : Set E) (D : Distribution E) : Prop :=
  ∀ U : Set E, IsOpen U → U ⊆ Ω →
    ∀ v w : Field E, IsSectionOn U D v → IsSectionOn U D w →
      ∀ p ∈ U, lieBracket v w p ∈ D p

/-- Smooth-module and Lie-bracket closure on a local domain. -/
inductive LieWordOn (U : Set E) (D : Distribution E) : Field E → Prop
  | basic (v : Field E) (hv : IsSectionOn U D v) : LieWordOn U D v
  | add {v w} : LieWordOn U D v → LieWordOn U D w →
      LieWordOn U D (fun p => v p + w p)
  | smul (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a U) {v} :
      LieWordOn U D v → LieWordOn U D (fun p => a p • v p)
  | bracket {v w} : LieWordOn U D v → LieWordOn U D w →
      LieWordOn U D (lieBracket v w)

/-- Use germs of local sections, not just globally defined generators. -/
def lieCompletion (Ω : Set E) (D : Distribution E) (p : E) : Submodule ℝ E :=
  Submodule.span ℝ {a | ∃ (U : Set E) (v : Field E),
    IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧ LieWordOn U D v ∧ v p = a}

lemma le_lieCompletion {D : Distribution E} (hD : HasLocalSmoothFrame Ω D)
    {p : E} (hp : p ∈ Ω) : D p ≤ lieCompletion Ω D p := by
  obtain ⟨U, hU, hpU, hsub, n, v, hv, hframe⟩ := hD p hp
  rw [(hframe p hpU).2]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨U, v i, hU, hpU, hsub, LieWordOn.basic _ ⟨hv i, ?_⟩, rfl⟩
  intro q hq
  rw [(hframe q hq).2]
  exact Submodule.subset_span ⟨i, rfl⟩

lemma lieCompletion_restrict {D : Distribution E} {U : Set E}
    (hU : IsOpen U) (hsub : U ⊆ Ω) {p : E} (hp : p ∈ U) :
    lieCompletion U D p = lieCompletion Ω D p := by
  have word_mono :
      ∀ {V W : Set E}, W ⊆ V → ∀ {v : Field E},
        LieWordOn V D v → LieWordOn W D v := by
    intro V W hWV v hv
    induction hv with
    | basic v hv =>
        exact LieWordOn.basic v
          ⟨hv.1.mono hWV, fun q hq => hv.2 q (hWV hq)⟩
    | add hv hw ihv ihw =>
        exact LieWordOn.add ihv ihw
    | smul a ha hv ih =>
        exact LieWordOn.smul a (ha.mono hWV) ih
    | bracket hv hw ihv ihw =>
        exact LieWordOn.bracket ihv ihw
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨V, v, hV, hpV, hVU, hv, rfl⟩
    apply Submodule.subset_span
    exact ⟨V, v, hV, hpV, hVU.trans hsub, hv, rfl⟩
  · apply Submodule.span_le.mpr
    rintro a ⟨V, v, hV, hpV, hVΩ, hv, rfl⟩
    let W := V ∩ U
    have hW : IsOpen W := hV.inter hU
    have hpW : p ∈ W := ⟨hpV, hp⟩
    have hWU : W ⊆ U := inter_subset_right
    have hWV : W ⊆ V := inter_subset_left
    apply Submodule.subset_span
    exact ⟨W, v, hW, hpW, hWU, word_mono hWV hv, rfl⟩

lemma lieCompletion_eq_iff {D : Distribution E} (hD : HasLocalSmoothFrame Ω D) :
    (∀ p ∈ Ω, lieCompletion Ω D p = D p) ↔ InvolutiveOn Ω D := by
  constructor
  · intro hEq U hU hUΩ v w hv hw p hp
    have hword : LieWordOn U D (lieBracket v w) :=
      LieWordOn.bracket (LieWordOn.basic v hv) (LieWordOn.basic w hw)
    have hmem : lieBracket v w p ∈ lieCompletion Ω D p := by
      apply Submodule.subset_span
      exact ⟨U, lieBracket v w, hU, hp, hUΩ, hword, rfl⟩
    simpa [hEq p (hUΩ hp)] using hmem
  · intro hinv p hp
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro a ⟨U, v, hU, hpU, hUΩ, hv, rfl⟩
      have word_section : ∀ {w : Field E}, LieWordOn U D w → IsSectionOn U D w := by
        intro w hw
        induction hw with
        | basic w hw => exact hw
        | add hv hw ihv ihw =>
            refine ⟨ihv.1.add ihw.1, ?_⟩
            intro q hq
            exact (D q).add_mem (ihv.2 q hq) (ihw.2 q hq)
        | smul a ha hw ih =>
            refine ⟨ha.smul ih.1, ?_⟩
            intro q hq
            exact (D q).smul_mem (a q) (ih.2 q hq)
        | bracket hv hw ihv ihw =>
            refine ⟨ihv.1.lieBracket_vectorField ihw.1 (by simp), ?_⟩
            intro q hq
            exact hinv U hU hUΩ _ _ ihv ihw q hq
      exact (word_section hv).2 p hpU
    · exact le_lieCompletion hD hp

def LocallyCompletelyIntegrableOn
    (Ω : Set E) (D : Distribution E) : Prop :=
  ∀ p ∈ Ω, ∃ (U : Set E) (m : ℕ) (h : Fin m → E → ℝ),
    IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
    (∀ i, ContDiffOn ℝ ∞ (h i) U) ∧
    (∀ q ∈ U,
      LinearIndependent ℝ (fun i => gradient (h i) q) ∧
      Submodule.span ℝ (Set.range (fun i => gradient (h i) q)) = (D q)ᗮ)

/-- Differential-geometric background used by Theorem 12: Theorem 21
(Frobenius), involutivity of the Lie closure, first integrals, and smooth
orthogonal frames. -/
class HasFrobeniusBackground
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] : Prop where
  frobenius_iff :
    ∀ {Ω : Set E} {D : Distribution E} {r : ℕ},
      IsOpen Ω → HasLocalSmoothFrame Ω D → ConstantRankOn Ω D r →
      (LocallyCompletelyIntegrableOn Ω D ↔ InvolutiveOn Ω D)
  lieClosure_involutive :
    ∀ {Ω : Set E} {D : Distribution E},
      HasLocalSmoothFrame Ω (lieCompletion Ω D) →
      InvolutiveOn Ω (lieCompletion Ω D)
  firstIntegrals :
    ∀ {Ω : Set E} {D : Distribution E} {r : ℕ},
      IsOpen Ω → HasLocalSmoothFrame Ω D →
      ConstantRankOn Ω D r → InvolutiveOn Ω D →
      ∀ {p : E}, p ∈ Ω →
        ∃ (U : Set E) (h : Fin (Module.finrank ℝ E - r) → E → ℝ),
          IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
          (∀ i, ContDiffOn ℝ ∞ (h i) U) ∧
          FunctionallyIndependentOn U h ∧
          (∀ q ∈ U,
            Submodule.span ℝ (Set.range (fun i => gradient (h i) q)) = (D q)ᗮ)
  orthogonalFrame :
    ∀ {Ω : Set E} {D : Distribution E} {r : ℕ},
      IsOpen Ω → HasLocalSmoothFrame Ω D →
      ConstantRankOn Ω D r → ∀ {p : E}, p ∈ Ω →
        ∃ (U : Set E) (v : Fin (Module.finrank ℝ E - r) → Field E),
          IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
          (∀ i, ContDiffOn ℝ ∞ (v i) U) ∧
          (∀ q ∈ U, LinearIndependent ℝ (fun i => v i q) ∧
            Submodule.span ℝ (Set.range (fun i => v i q)) = (D q)ᗮ)

/-- Theorem 21 (Frobenius), in the local complete-integrability
form reviewed in Appendix A. -/
theorem theorem21 [HasFrobeniusBackground E]
    {D : Distribution E} {r : ℕ}
    (hΩ : IsOpen Ω) (hframe : HasLocalSmoothFrame Ω D)
    (hrank : ConstantRankOn Ω D r) :
    LocallyCompletelyIntegrableOn Ω D ↔ InvolutiveOn Ω D :=
  HasFrobeniusBackground.frobenius_iff hΩ hframe hrank

lemma lieCompletion_involutive [HasFrobeniusBackground E]
    {D : Distribution E}
    (hD : HasLocalSmoothFrame Ω (lieCompletion Ω D)) :
    InvolutiveOn Ω (lieCompletion Ω D) :=
  HasFrobeniusBackground.lieClosure_involutive hD

lemma firstIntegral_lieCompletion {D : Distribution E} {h : E → ℝ}
    (hΩ : IsOpen Ω) (hh : ContDiffOn ℝ ∞ h Ω)
    (hD : ∀ p ∈ Ω, gradient h p ∈ (D p)ᗮ) :
    ∀ p ∈ Ω, gradient h p ∈ (lieCompletion Ω D p)ᗮ := by
  have word_smooth :
      ∀ {U : Set E} {v : Field E}, LieWordOn U D v →
        ContDiffOn ℝ ∞ v U := by
    intro U v hv
    induction hv with
    | basic v hv => exact hv.1
    | add hv hw ihv ihw => exact ihv.add ihw
    | smul a ha hv ih => exact ha.smul ih
    | bracket hv hw ihv ihw =>
        simpa [lieBracket] using
          ihv.lieBracket_vectorField ihw (by simp)
  have word_annihilates :
      ∀ {U : Set E}, IsOpen U → U ⊆ Ω →
      ∀ {v : Field E}, LieWordOn U D v →
        ∀ q ∈ U, ⟪gradient h q, v q⟫_ℝ = 0 := by
    intro U hU hUΩ v hv
    induction hv with
    | basic v hv =>
        intro q hq
        exact (Submodule.mem_orthogonal' _ _).mp
          (hD q (hUΩ hq)) (v q) (hv.2 q hq)
    | add hv hw ihv ihw =>
        intro q hq
        simp [inner_add_right, ihv q hq, ihw q hq]
    | smul a ha hv ih =>
        intro q hq
        simp [inner_smul_right, ih q hq]
    | bracket hv hw ihv ihw =>
        intro q hq
        have hsv := word_smooth hv
        have hsw := word_smooth hw
        have hhq : ContDiffAt ℝ ∞ h q :=
          (hh q (hUΩ hq)).contDiffAt (hΩ.mem_nhds (hUΩ hq))
        have hvq : DifferentiableAt ℝ _ q :=
          (hsv q hq).contDiffAt (hU.mem_nhds hq) |>.differentiableAt (by simp)
        have hwq : DifferentiableAt ℝ _ q :=
          (hsw q hq).contDiffAt (hU.mem_nhds hq) |>.differentiableAt (by simp)
        have hzv :
            (fun x => fderiv ℝ h x (v x)) =ᶠ[𝓝 q] (fun _ => 0) := by
          filter_upwards [hU.mem_nhds hq] with x hx
          rw [← inner_gradient_left]
          exact ihv x hx
        have hzw :
            (fun x => fderiv ℝ h x (w x)) =ᶠ[𝓝 q] (fun _ => 0) := by
          filter_upwards [hU.mem_nhds hq] with x hx
          rw [← inner_gradient_left]
          exact ihw x hx
        have hbr := fderiv_apply_lieBracket
          (f := h) hhq (by simp) hvq hwq
        rw [hzv.fderiv_eq, hzw.fderiv_eq] at hbr
        simp at hbr
        rw [← inner_gradient_left]
        simpa [lieBracket] using hbr
  intro p hp
  rw [Submodule.mem_orthogonal']
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨U, v, hU, hpU, hUΩ, hv, rfl⟩ := hz
      exact word_annihilates hU hUΩ hv p hpU
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp [inner_add_right, ihx, ihy]
  | smul a x hx ih =>
      simp [inner_smul_right, ih]

/-- Local Frobenius theorem in exactly the form used in Appendix E.8. -/
theorem theorem21_frobenius [HasFrobeniusBackground E]
    {D : Distribution E} {r : ℕ}
    (hΩ : IsOpen Ω) (hframe : HasLocalSmoothFrame Ω D)
    (hrank : ConstantRankOn Ω D r) (hinv : InvolutiveOn Ω D)
    {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (h : Fin (Module.finrank ℝ E - r) → E → ℝ),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∀ i, ContDiffOn ℝ ∞ (h i) U) ∧
      FunctionallyIndependentOn U h ∧
      (∀ q ∈ U, Submodule.span ℝ (Set.range (fun i => gradient (h i) q)) = (D q)ᗮ) :=
  HasFrobeniusBackground.firstIntegrals hΩ hframe hrank hinv hp

/-- Local/germ completeness, as actually used by Propositions 4 and 16--17.
This is stronger than a merely maximal family of globally defined functions. -/
def CompleteLawsOn {ι : Type*} (Ω : Set E) (L : S → E → ℝ)
    (h : ι → E → ℝ) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (h i) Ω) ∧
  (∀ i, IsConservedOn Ω L (h i)) ∧
  FunctionallyIndependentOn Ω h ∧
  (∀ (V : Set E), IsOpen V → V ⊆ Ω → ∀ f : E → ℝ,
    ContDiffOn ℝ ∞ f V → IsConservedOn V L f →
      ∀ p ∈ V, gradient f p ∈
        Submodule.span ℝ (Set.range (fun i => gradient (h i) p)))

lemma CompleteLawsOn.mono {ι : Type*} {L : S → E → ℝ} {h : ι → E → ℝ}
    {U : Set E} (hc : CompleteLawsOn Ω L h)
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) :
    CompleteLawsOn U L h := by
  refine ⟨fun i => (hc.1 i).mono hUΩ, ?_, ?_, ?_⟩
  · intro i n d hn I hI hconv γ hγ t ht u hu
    exact hc.2.1 i n d hn I hI hconv γ
      ⟨fun s hs => hUΩ (hγ.1 hs), hγ.2⟩ t ht u hu
  · intro p hp
    exact hc.2.2.1 p (hUΩ hp)
  · intro V hV hVU f hf hfc p hp
    exact hc.2.2.2 V hV (hVU.trans hUΩ) f hf hfc p hp

lemma CompleteLawsOn.reindex {ι κ : Type*} (e : κ ≃ ι)
    {L : S → E → ℝ} {h : ι → E → ℝ}
    (hc : CompleteLawsOn Ω L h) :
    CompleteLawsOn Ω L (fun k => h (e k)) := by
  refine ⟨fun k => hc.1 (e k), fun k => hc.2.1 (e k), ?_, ?_⟩
  · intro p hp
    exact (hc.2.2.1 p hp).comp e.injective
  · intro V hV hVU f hf hfc p hp
    have hs := hc.2.2.2 V hV hVU f hf hfc p hp
    simpa only [Set.range_comp, e.surjective.range_comp] using hs

section IsometryTransport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]

lemma gradient_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} {q : F}
    (hf : DifferentiableAt ℝ f (e.symm q)) :
    gradient (fun z : F => f (e.symm z)) q = e (gradient f (e.symm q)) := by
  apply (InnerProductSpace.toDual ℝ F).injective
  ext v
  rw [toDual_gradient, ← inner_gradient_left]
  have hcomp := hf.hasFDerivAt.comp q e.symm.toContinuousLinearEquiv.hasFDerivAt
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← inner_gradient_left]
  exact e.inner_map_map (gradient f (e.symm q)) (e.symm v) |>.trans <| by simp

lemma RegularLossOn.precomp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {L : S → E → ℝ}
    {U : Set E} (hL : RegularLossOn U L)
    {V : Set F} (hV : IsOpen V) (hVU : ∀ q ∈ V, e.symm q ∈ U) :
    RegularLossOn V (fun s q => L s (e.symm q)) := by
  refine ⟨hV, ?_, ?_⟩
  · intro s
    exact (hL.c1 s).comp
      e.symm.toContinuousLinearEquiv.contDiff.contDiffOn hVU
  · intro s q hq
    obtain ⟨W, hW, heW, hWU, K, hK⟩ :=
      hL.localLip s (e.symm q) (hVU q hq)
    let W' : Set F := V ∩ e '' W
    have hW' : IsOpen W' :=
      hV.inter (e.toHomeomorph.isOpenMap W hW)
    have hqW' : q ∈ W' := ⟨hq, ⟨e.symm q, heW, by simp⟩⟩
    refine ⟨W', hW', hqW', inter_subset_left, K, ?_⟩
    intro x hx y hy
    have hxW : e.symm x ∈ W := by
      rcases hx.2 with ⟨x', hx', rfl⟩
      simpa using hx'
    have hyW : e.symm y ∈ W := by
      rcases hy.2 with ⟨y', hy', rfl⟩
      simpa using hy'
    rw [gradient_comp_linearIsometryEquiv e
      (differentiableAt_of_c1 hL.isOpen (hL.c1 s) (hWU hxW))]
    rw [gradient_comp_linearIsometryEquiv e
      (differentiableAt_of_c1 hL.isOpen (hL.c1 s) (hWU hyW))]
    simpa using hK hxW hyW

lemma CompleteLawsOn.pullback_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F)
    {ΩF : Set F} {L : S → F → ℝ} {h : ι → F → ℝ}
    (hc : CompleteLawsOn ΩF L h) :
    CompleteLawsOn (e.symm '' ΩF)
      (fun s p => L s (e p))
      (fun i p => h i (e p)) := by
  have hopen : IsOpen (e.symm '' ΩF) :=
    e.symm.toHomeomorph.isOpenMap ΩF <| by
      exact (hc.1 Classical.choice).isOpen_domain
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (hc.1 i).comp e.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun p hp => by rcases hp with ⟨q,hq,rfl⟩; simpa using hq)
  · intro i n d hn I hI hconv γ hγ t ht u hu
    let η : ℝ → F := fun s => e (γ s)
    have hη : IsIntegralCurveOn ΩF I
        (empiricalField L d) η := by
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases hγ.1 hs with ⟨q,hq,heq⟩
        simpa [η, heq] using hq
      · intro s hs
        have hdγ := hγ.2 s hs
        simpa [η, empiricalField,
          gradient_comp_linearIsometryEquiv e.symm] using hdγ.clm_apply
            e.toContinuousLinearEquiv
    exact hc.2.1 i n d hn I hI hconv η hη t ht u hu
  · intro p hp
    rcases hp with ⟨q,hq,rfl⟩
    have hi := hc.2.2.1 q hq
    simpa [FunctionallyIndependentOn,
      gradient_comp_linearIsometryEquiv e.symm] using hi.map'
      e.symm.injective
  · intro V hV hVΩ f hf hfc p hp
    let g : F → ℝ := fun q => f (e.symm q)
    let W : Set F := e '' V
    have hW : IsOpen W := e.toHomeomorph.isOpenMap V hV
    have hWΩ : W ⊆ ΩF := by
      rintro q ⟨x,hx,rfl⟩
      rcases hVΩ hx with ⟨y,hy,hey⟩
      simpa using hey ▸ hy
    have hg : ContDiffOn ℝ ∞ g W :=
      hf.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (fun q hq => by rcases hq with ⟨x,hx,rfl⟩; simpa using hx)
    have hgc : IsConservedOn W L g := by
      intro n d hn I hI hconv γ hγ t ht u hu
      let η : ℝ → E := fun s => e.symm (γ s)
      have hη : IsIntegralCurveOn (e.symm '' ΩF) I
          (empiricalField (fun s p => L s (e p)) d) η := by
        refine ⟨?_, ?_⟩
        · intro s hs
          exact ⟨γ s, hWΩ (hγ.1 hs), by simp [η]⟩
        · intro s hs
          simpa [η, empiricalField,
            gradient_comp_linearIsometryEquiv e] using
              (hγ.2 s hs).clm_apply e.symm.toContinuousLinearEquiv
      exact hfc n d hn I hI hconv η hη t ht u hu
    rcases hp with ⟨q,hq,rfl⟩
    have hs := hc.2.2.2 W hW hWΩ g hg hgc q ⟨e.symm q, hq, by simp⟩
    simpa [g, gradient_comp_linearIsometryEquiv e.symm] using hs

end IsometryTransport

structure PartialSymmetry (Ω : Set E) (L : S → E → ℝ) where
  generator : Field E
  smooth_generator : ContDiffOn ℝ ∞ generator Ω
  flow : LocalFlow Ω generator
  invariant : IsLossSymmetry L flow

/-- Definition 11, with "complete" meaning infinitesimally spanning, not
complete as an ODE vector field. -/
def CompleteSymmetriesOn {ι : Type*} (Ω : Set E) (L : S → E → ℝ)
    (ψ : ι → PartialSymmetry Ω L) : Prop :=
  ∀ p ∈ Ω,
    LinearIndependent ℝ (fun i => (ψ i).generator p) ∧
    Submodule.span ℝ (Set.range (fun i => (ψ i).generator p)) =
      symmetryDistribution L p

lemma orthogonal_local_frame [HasFrobeniusBackground E]
    {D : Distribution E} {r : ℕ}
    (hΩ : IsOpen Ω) (hframe : HasLocalSmoothFrame Ω D)
    (hrank : ConstantRankOn Ω D r) {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (v : Fin (Module.finrank ℝ E - r) → Field E),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∀ i, ContDiffOn ℝ ∞ (v i) U) ∧
      (∀ q ∈ U, LinearIndependent ℝ (fun i => v i q) ∧
        Submodule.span ℝ (Set.range (fun i => v i q)) = (D q)ᗮ) :=
  HasFrobeniusBackground.orthogonalFrame hΩ hframe hrank hp

/-- Theorem 12(i)--(ii). `rLie` is the paper's barred r, distinct from r. -/
theorem theorem12 [HasMaximalSmoothLocalFlows] [HasFrobeniusBackground E]
    {L : S → E → ℝ} (hL : SmoothLossOn Ω L)
    {r rLie : ℕ}
    (hW : HasLocalSmoothFrame Ω (gradientDistribution L))
    (hr : ConstantRankOn Ω (gradientDistribution L) r)
    (hLie : HasLocalSmoothFrame Ω (lieCompletion Ω (gradientDistribution L)))
    (hrLie : ConstantRankOn Ω (lieCompletion Ω (gradientDistribution L)) rLie)
    {p : E} (hp : p ∈ Ω) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∃ ψ : Fin (Module.finrank ℝ E - r) → PartialSymmetry U L,
        CompleteSymmetriesOn U L ψ) ∧
      (∃ h : Fin (Module.finrank ℝ E - rLie) → E → ℝ,
        CompleteLawsOn U L h) := by
  obtain ⟨Us, v, hUs, hpUs, hsΩ, hv, hvframe⟩ :=
    orthogonal_local_frame hL.isOpen hW hr hp
  obtain ⟨Uc, h, hUc, hpUc, hcΩ, hh, hind, hhframe⟩ :=
    theorem21_frobenius hL.isOpen hLie hrLie (lieCompletion_involutive hLie) hp
  let U := Us ∩ Uc
  have hU : IsOpen U := hUs.inter hUc
  have hUΩ : U ⊆ Ω := fun _ hx => hsΩ hx.1
  have hreg := hL.regular.mono hU hUΩ
  have hvmem : ∀ i q, q ∈ U → v i q ∈ symmetryDistribution L q := by
    intro i q hq
    rw [symmetryDistribution, ← (hvframe q hq.1).2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hflows : ∀ i, ∃ ψ : LocalFlow U (v i), IsLossSymmetry L ψ := by
    intro i
    obtain ⟨ψ, _, hi⟩ := proposition9 hreg
      ((hv i).mono Set.inter_subset_left) (hvmem i)
    exact ⟨ψ, hi⟩
  choose ψ hψ using hflows
  refine ⟨U, hU, ⟨hpUs, hpUc⟩, hUΩ, ?_, ?_⟩
  · let Ψ : Fin (Module.finrank ℝ E - r) → PartialSymmetry U L :=
      fun i => ⟨v i, (hv i).mono Set.inter_subset_left, ψ i, hψ i⟩
    exact ⟨Ψ, fun q hq => hvframe q hq.1⟩
  · refine ⟨h, (fun i => (hh i).mono Set.inter_subset_right), ?_,
      (fun q hq => hind q hq.2), ?_⟩
    · intro i
      apply (proposition2 hreg
        (((hh i).mono Set.inter_subset_right).of_le (by simp))).mpr
      intro q hq
      have hi : gradient (h i) q ∈
          (lieCompletion Ω (gradientDistribution L) q)ᗮ := by
        rw [← hhframe q hq.2]
        exact Submodule.subset_span ⟨i, rfl⟩
      apply (Submodule.mem_orthogonal' _ _).mpr
      intro a ha
      exact (Submodule.mem_orthogonal' _ _).mp hi a
        (le_lieCompletion hW (hUΩ hq) ha)
    · intro V hV hVU f hf hfc q hq
      have hVΩ : V ⊆ Ω := fun _ hx => hUΩ (hVU hx)
      have hfo := (proposition2 (hL.regular.mono hV hVΩ)
        (hf.of_le (by simp))).mp hfc
      have hfl := firstIntegral_lieCompletion hV hf hfo q hq
      rw [lieCompletion_restrict hV hVΩ hq] at hfl
      rw [hhframe q (hVU hq).2]
      exact hfl

/-- The arithmetic part of Theorem 12(iii), with no subtraction in ℕ
silently masking a negative quantity. -/
theorem gap_arithmetic {D r rLie : ℕ} (h₁ : r ≤ rLie) (h₂ : rLie ≤ D) :
    (D - r) - (D - rLie) = rLie - r ∧
      ((D - r) - (D - rLie) = 0 ↔ rLie = r) := by
  omega

theorem theorem12_gap {L : S → E → ℝ} {r rLie : ℕ}
    (hΩ : Ω.Nonempty)
    (hW : HasLocalSmoothFrame Ω (gradientDistribution L))
    (hr : ConstantRankOn Ω (gradientDistribution L) r)
    (hrLie : ConstantRankOn Ω (lieCompletion Ω (gradientDistribution L)) rLie) :
    r ≤ rLie ∧
    ((Module.finrank ℝ E - r) - (Module.finrank ℝ E - rLie) = rLie - r) ∧
    (rLie = r ↔ InvolutiveOn Ω (gradientDistribution L)) := by
  obtain ⟨p, hp⟩ := hΩ
  have h₁ : r ≤ rLie := by
    have h := (Submodule.finrank_strictMono (K := ℝ) (V := E)).monotone
      (le_lieCompletion hW hp)
    simpa only [hr p hp, hrLie p hp] using h
  have h₂ : rLie ≤ Module.finrank ℝ E := by
    have h := (Submodule.finrank_strictMono (K := ℝ) (V := E)).monotone
      (show lieCompletion Ω (gradientDistribution L) p ≤ ⊤ from le_top)
    simpa only [hrLie p hp, Submodule.finrank_top] using h
  refine ⟨h₁, (gap_arithmetic h₁ h₂).1, ?_⟩
  constructor
  · intro he
    apply (lieCompletion_eq_iff hW).mp
    intro q hq
    by_contra hne
    have hlt : gradientDistribution L q <
        lieCompletion Ω (gradientDistribution L) q :=
      lt_of_le_of_ne (le_lieCompletion hW hq) (Ne.symm hne)
    have hx := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hr q hq, hrLie q hq, he] at hx
    exact (Nat.lt_irrefl r) hx
  · intro hi
    have he := (lieCompletion_eq_iff hW).mpr hi p hp
    calc
      rLie = Module.finrank ℝ (lieCompletion Ω (gradientDistribution L) p) :=
        (hrLie p hp).symm      _ = Module.finrank ℝ (gradientDistribution L p) :=
        congrArg (fun V : Submodule ℝ E => Module.finrank ℝ V) he
      _ = r := hr p hp

/-- A useful bound that does not need a constant-rank Lie completion. -/
theorem independent_laws_le_symmetry_rank {L : S → E → ℝ}
    (hL : RegularLossOn Ω L) {n : ℕ} (h : Fin n → E → ℝ)
    (hh : ∀ i, ContDiffOn ℝ 1 (h i) Ω)
    (hc : ∀ i, IsConservedOn Ω L (h i))
    (hi : FunctionallyIndependentOn Ω h) {p : E} (hp : p ∈ Ω) :
    n ≤ Module.finrank ℝ (symmetryDistribution L p) := by
  let v : Fin n → symmetryDistribution L p :=
    fun i => ⟨gradient (h i) p, (proposition2 hL (hh i)).mp (hc i) p hp⟩
  have hv : LinearIndependent ℝ v :=
    (hi p hp).of_comp (symmetryDistribution L p).subtype
  simpa using hv.fintype_card_le_finrank

end GradientFlowPaper

end -- noncomputable section


/-! ## Source module: GradientFlowPaper/Inheritance.lean -/


/-!
Section 4: Proposition 14, Propositions 15--16, Theorem 17.

Finite orthogonal blocks are implemented as a single EuclideanSpace indexed
by a sigma type. In particular, no sup-norm product is mistaken for an
inner-product space.

For functional symmetries, completeness below quantifies over actual smooth
local flows, rather than identifying every pointwise kernel vector with a
realizable symmetry. Assumption 13 is used only for equality of predictions;
it is NOT replaced by a pointwise spanning assumption on output gradients.
-/

noncomputable section
open Set Function Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

namespace GradientFlowPaper

variable [HasMaximalSmoothLocalFlows]

section FunctionalSymmetries

variable {E X Y Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {Ω : Set E} {v : Field E}

def IsFunctionalSymmetry (G : E → X → Z) (ψ : LocalFlow Ω v) : Prop :=
  ∀ t p, (t, p) ∈ ψ.domain → FunctionalEquiv G (ψ.toFun t p) p

theorem functionalSymmetry_loss (G : E → X → Z) (ell : Z → Y → ℝ)
    (ψ : LocalFlow Ω v) (hs : IsFunctionalSymmetry G ψ) :
    IsLossSymmetry (sampleLoss G ell) ψ := by
  rintro ⟨x, y⟩ t p htp
  exact congrArg (fun z => ell z y) (hs t p htp x)

/-- Proposition 14; no differentiability is needed in this separation step. -/
theorem proposition14 (G : E → X → Z) (ell : Z → Y → ℝ)
    (hsep : SeparatesPredictions ell) (ψ : LocalFlow Ω v)
    (hs : IsLossSymmetry (sampleLoss G ell) ψ) :
    IsFunctionalSymmetry G ψ := by
  intro t p htp x
  exact hsep _ _ (fun y => hs (x, y) t p htp)

structure FunctionalPartialSymmetry (Ω : Set E) (G : E → X → Z) where
  generator : Field E
  smooth_generator : ContDiffOn ℝ ∞ generator Ω
  flow : LocalFlow Ω generator
  invariant : IsFunctionalSymmetry G flow

/-- Local functional completeness, allowing arbitrary smaller open domains. -/
def CompleteFunctionalSymmetriesOn {ι : Type*} (Ω : Set E) (G : E → X → Z)
    (ψ : ι → FunctionalPartialSymmetry Ω G) : Prop :=
  (∀ p ∈ Ω, LinearIndependent ℝ (fun i => (ψ i).generator p)) ∧
  (∀ V : Set E, IsOpen V → V ⊆ Ω →
    ∀ φ : FunctionalPartialSymmetry V G,
      ∀ p ∈ V, φ.generator p ∈
        Submodule.span ℝ (Set.range (fun i => (ψ i).generator p)))

end FunctionalSymmetries

namespace Blocks

variable {B : Type*} [Fintype B] [DecidableEq B]
variable (ι : B → Type*) [∀ j, Fintype (ι j)]

abbrev Total := Vec (Sigma ι)

def block (j : B) (p : Total ι) : Vec (ι j) :=
  WithLp.toLp 2 (fun a => p ⟨j, a⟩)

def inject (j : B) (u : Vec (ι j)) : Total ι :=
  WithLp.toLp 2 (fun a => if h : a.1 = j then u (h ▸ a.2) else 0)

def replace (j : B) (p : Total ι) (u : Vec (ι j)) : Total ι :=
  p - inject ι j (block ι j p) + inject ι j u

def domain (U : ∀ j, Set (Vec (ι j))) : Set (Total ι) :=
  {p | ∀ j, block ι j p ∈ U j}

def extendLaw (j : B) (h : Vec (ι j) → ℝ) : Total ι → ℝ :=
  fun p => h (block ι j p)

def extendField (j : B) (v : Field (Vec (ι j))) : Field (Total ι) :=
  fun p => inject ι j (v (block ι j p))

def sliceLaw (j : B) (p : Total ι) (h : Total ι → ℝ) : Vec (ι j) → ℝ :=
  fun u => h (replace ι j p u)

def blockLinear (j : B) : Total ι →ₗ[ℝ] Vec (ι j) where
  toFun := block ι j
  map_add' := by intros; ext a; rfl
  map_smul' := by intros; ext a; rfl

def injectLinear (j : B) : Vec (ι j) →ₗ[ℝ] Total ι where
  toFun := inject ι j
  map_add' := by
    intro u v; ext a
    simp [inject]
    split <;> simp_all
  map_smul' := by
    intro c u; ext a
    simp [inject]
    split <;> simp_all

@[simp] lemma inject_zero (j : B) : inject ι j (0 : Vec (ι j)) = 0 :=
  (injectLinear ι j).map_zero

@[simp] lemma inject_add (j : B) (u v : Vec (ι j)) :
    inject ι j (u + v) = inject ι j u + inject ι j v :=
  (injectLinear ι j).map_add u v

@[simp] lemma inject_smul (j : B) (c : ℝ) (u : Vec (ι j)) :
    inject ι j (c • u) = c • inject ι j u :=
  (injectLinear ι j).map_smul c u

@[simp] lemma norm_inject_eq (j : B) (u : Vec (ι j)) :
    ‖inject ι j u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq_sqrt_sum_sq, EuclideanSpace.norm_eq_sqrt_sum_sq]
  congr 1
  simp [inject, Finset.sum_sigma']

@[simp] lemma block_inject_same (j : B) (u : Vec (ι j)) :
    block ι j (inject ι j u) = u := by
  ext a
  simp [block, inject]

@[simp] lemma block_inject_ne {j k : B} (hjk : k ≠ j) (u : Vec (ι j)) :
    block ι k (inject ι j u) = 0 := by
  ext a
  simp [block, inject, hjk]

@[simp] lemma block_replace_same (j : B) (p : Total ι) (u : Vec (ι j)) :
    block ι j (replace ι j p u) = u := by
  change blockLinear ι j (p - inject ι j (block ι j p) + inject ι j u) = u
  simp

@[simp] lemma replace_self (j : B) (p : Total ι) :
    replace ι j p (block ι j p) = p := by
  simp [replace]

lemma sum_inject_blocks (p : Total ι) :
    (∑ j, inject ι j (block ι j p)) = p := by
  ext a
  simp [inject, block]

lemma open_domain {U : ∀ j, Set (Vec (ι j))} (hU : ∀ j, IsOpen (U j)) :
    IsOpen (domain ι U) := by
  change IsOpen (⋂ j, (block ι j) ⁻¹' U j)
  exact isOpen_iInter_of_finite
    (fun j => (hU j).preimage (blockLinear ι j).continuous_of_finiteDimensional)

/-- Every open neighborhood in a finite orthogonal direct sum contains a
product neighborhood. This is the elementary shrinking step used implicitly
when Theorem 17 is applied locally. -/
lemma exists_product_box {W : Set (Total ι)} (hW : IsOpen W)
    {p : Total ι} (hp : p ∈ W) :
    ∃ U : ∀ j, Set (Vec (ι j)),
      (∀ j, IsOpen (U j)) ∧
      (∀ j, block ι j p ∈ U j) ∧
      domain ι U ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW p hp
  let δ : ℝ := ε / (Fintype.card B + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let U : ∀ j, Set (Vec (ι j)) :=
    fun j => Metric.ball (block ι j p) δ
  refine ⟨U, fun j => isOpen_ball, ?_, ?_⟩
  · intro j
    exact Metric.mem_ball_self hδ
  · intro q hq
    apply hball
    rw [dist_eq_norm, ← sum_inject_blocks ι (q - p)]
    calc
      ‖∑ j, inject ι j (block ι j (q - p))‖
          ≤ ∑ j, ‖inject ι j (block ι j (q - p))‖ := norm_sum_le _ _
      _ = ∑ j, ‖block ι j q - block ι j p‖ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [show block ι j (q - p) =
              block ι j q - block ι j p by
                change blockLinear ι j (q - p) = _
                simp]
            exact norm_inject_eq ι j _
      _ < ∑ _j : B, δ := by
            apply Finset.sum_lt_sum
            · intro j _
              have hj := hq j
              simpa [U, Metric.mem_ball, dist_eq_norm] using hj
            · exact Finset.univ_nonempty
      _ = Fintype.card B * δ := by simp
      _ < ε := by
            dsimp [δ]
            have hc : (Fintype.card B : ℝ) < Fintype.card B + 1 := by norm_num
            nlinarith

lemma replace_mem {U : ∀ j, Set (Vec (ι j))} {p : Total ι}
    (hp : p ∈ domain ι U) {j : B} {u : Vec (ι j)} (hu : u ∈ U j) :
    replace ι j p u ∈ domain ι U := by
  intro k
  by_cases hkj : k = j
  · subst k; simpa using hu
  · have he : block ι k (replace ι j p u) = block ι k p := by
      change blockLinear ι k (p - inject ι j (block ι j p) + inject ι j u) = _
      simp [hkj]
    rw [he]
    exact hp k

lemma gradient_extendLaw {U : ∀ j, Set (Vec (ι j))}
    (hU : ∀ j, IsOpen (U j)) (j : B) {h : Vec (ι j) → ℝ}
    (hh : ContDiffOn ℝ 1 h (U j)) {p : Total ι} (hp : p ∈ domain ι U) :
    gradient (extendLaw ι j h) p = inject ι j (gradient h (block ι j p)) := by
  have hb :
      HasFDerivAt (block ι j)
        (blockLinear ι j).toContinuousLinearMap p :=
    (blockLinear ι j).toContinuousLinearMap.hasFDerivAt
  have hh' : DifferentiableAt ℝ h (block ι j p) :=
    differentiableAt_of_c1 (hU j) hh (hp j)
  have hc :
      HasFDerivAt (extendLaw ι j h)
        ((fderiv ℝ h (block ι j p)).comp
          (blockLinear ι j).toContinuousLinearMap) p := by
    simpa [extendLaw, Function.comp_def] using
      hh'.hasFDerivAt.comp p hb
  apply (InnerProductSpace.toDual ℝ (Total ι)).injective
  rw [toDual_gradient, hc.fderiv]
  ext u
  simp only [ContinuousLinearMap.comp_apply]
  rw [← inner_gradient_left]
  change ⟪gradient h (block ι j p), block ι j u⟫_ℝ =
    ⟪inject ι j (gradient h (block ι j p)), u⟫_ℝ
  simp [block, inject, inner, Finset.sum_sigma']

lemma smooth_extendLaw {U : ∀ j, Set (Vec (ι j))}
    (j : B) {h : Vec (ι j) → ℝ} (hh : ContDiffOn ℝ ∞ h (U j)) :
    ContDiffOn ℝ ∞ (extendLaw ι j h) (domain ι U) := by
  apply hh.comp (blockLinear ι j).toContinuousLinearMap.contDiff.contDiffOn
  exact fun _ hp => hp j

/-- Gradient of a scalar function restricted to one affine parameter block. -/
lemma gradient_sliceLaw {V : Set (Total ι)} (hV : IsOpen V)
    (j : B) (p : Total ι) {h : Total ι → ℝ}
    (hh : ContDiffOn ℝ 1 h V) {u : Vec (ι j)}
    (hu : replace ι j p u ∈ V) :
    gradient (sliceLaw ι j p h) u =
      block ι j (gradient h (replace ι j p u)) := by
  let R : Vec (ι j) → Total ι := fun z => replace ι j p z
  have hR :
      HasFDerivAt R (injectLinear ι j).toContinuousLinearMap u := by
    simpa [R, replace] using
      (injectLinear ι j).toContinuousLinearMap.hasFDerivAt.const_add
        (p - inject ι j (block ι j p))
  have hh' : DifferentiableAt ℝ h (R u) :=
    differentiableAt_of_c1 hV hh hu
  have hc :
      HasFDerivAt (sliceLaw ι j p h)
        ((fderiv ℝ h (R u)).comp
          (injectLinear ι j).toContinuousLinearMap) u := by
    simpa [sliceLaw, R, Function.comp_def] using
      hh'.hasFDerivAt.comp u hR
  apply (InnerProductSpace.toDual ℝ (Vec (ι j))).injective
  rw [toDual_gradient, hc.fderiv]
  ext z
  simp only [ContinuousLinearMap.comp_apply]
  rw [← inner_gradient_left, ← inner_gradient_left]
  simp [R, block, inject, inner, Finset.sum_sigma']

/-- A lifted flow leaves every other orthogonal parameter block fixed. -/
theorem exists_liftedFlow {U : ∀ j, Set (Vec (ι j))}
    (hU : ∀ j, IsOpen (U j)) (j : B) {v : Field (Vec (ι j))}
    (ψ : LocalFlow (U j) v) :
    ∃ Ψ : LocalFlow (domain ι U) (extendField ι j v),
      (∀ t p, Ψ.toFun t p = replace ι j p (ψ.toFun t (block ι j p))) ∧
      (∀ t p, (t, p) ∈ Ψ.domain ↔
        p ∈ domain ι U ∧ (t, block ι j p) ∈ ψ.domain) := by
  let D : Set (ℝ × Total ι) :=
    {z | z.2 ∈ domain ι U ∧ (z.1, block ι j z.2) ∈ ψ.domain}
  let F : ℝ → Total ι → Total ι :=
    fun t p => replace ι j p (ψ.toFun t (block ι j p))
  have hDopen : IsOpen D := by
    have h₁ : IsOpen ((Prod.snd : ℝ × Total ι → Total ι) ⁻¹' domain ι U) :=
      (open_domain ι hU).preimage continuous_snd
    have h₂ : IsOpen
        ((fun z : ℝ × Total ι => (z.1, block ι j z.2)) ⁻¹' ψ.domain) :=
      ψ.open_domain.preimage
        (continuous_fst.prodMk
          ((blockLinear ι j).continuous_of_finiteDimensional.comp continuous_snd))
    simpa [D, Set.preimage_setOf_eq] using h₁.inter h₂
  let Ψ : LocalFlow (domain ι U) (extendField ι j v) :=
    { domain := D
      open_domain := hDopen
      source_mem := by
        intro t p htp
        exact htp.1
      zero_mem := by
        intro p hp
        exact ⟨hp, ψ.zero_mem (hp j)⟩
      time_convex := by
        intro p hp
        simpa [D, hp] using ψ.time_convex (block ι j p) (hp j)
      toFun := F
      smooth := by
        have hψ := ψ.smooth
        dsimp [D, F]
        fun_prop
      initial := by
        intro p hp
        simp [F, ψ.initial (block ι j p) (hp j), replace_self]
      target_mem := by
        intro t p htp
        exact replace_mem ι htp.1 (ψ.target_mem htp.2)
      ode := by
        intro t p htp
        have hψode := ψ.ode htp.2
        apply hasDerivAt_of_forall_coord
        intro a
        rcases a with ⟨k, ak⟩
        by_cases hkj : k = j
        · subst k
          simpa [F, replace, block, inject] using
            hψode.clm_apply
              ((ContinuousLinearMap.apply ℝ (ι j → ℝ) ak).comp
                (WithLp.linearEquiv _ _ _).toContinuousLinearMap)
        · have hconst :
              (fun s => F s p ⟨k, ak⟩) =
                fun _ => p ⟨k, ak⟩ := by
            funext s
            simp [F, replace, inject, hkj]
          rw [hconst]
          simpa [extendField, inject, hkj] using
            hasDerivAt_const t (p ⟨k, ak⟩)
      composition := by
        intro t s p hsp ht hts
        have hψcomp := ψ.composition hsp.2 ht.2 hts.2
        ext a
        rcases a with ⟨k, ak⟩
        by_cases hkj : k = j
        · subst k
          simpa [F, replace, block, inject] using congrArg (fun q => q ak) hψcomp
        · simp [F, replace, inject, hkj] }
  refine ⟨Ψ, ?_, ?_⟩
  · intro t p
    rfl
  · intro t p
    rfl

lemma smooth_extendField {U : ∀ j, Set (Vec (ι j))}
    (j : B) {v : Field (Vec (ι j))} (hv : ContDiffOn ℝ ∞ v (U j)) :
    ContDiffOn ℝ ∞ (extendField ι j v) (domain ι U) := by
  exact (injectLinear ι j).toContinuousLinearMap.contDiff.comp_contDiffOn
    (hv.comp (blockLinear ι j).toContinuousLinearMap.contDiff.contDiffOn (fun _ hp => hp j))

/-- The linear algebra of combining disjoint blocks. -/
lemma mem_span_of_blocks {α : B → Type*}
    (f : ∀ j, α j → Vec (ι j)) (v : Total ι)
    (hv : ∀ j, block ι j v ∈ Submodule.span ℝ (Set.range (f j))) :
    v ∈ Submodule.span ℝ
      (Set.range (fun a : Sigma α => inject ι a.1 (f a.1 a.2))) := by
  let K := Submodule.span ℝ
    (Set.range (fun a : Sigma α => inject ι a.1 (f a.1 a.2)))
  rw [← sum_inject_blocks ι v]
  apply K.sum_mem
  intro j _
  induction hv j using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, rfl⟩ := hu
      exact Submodule.subset_span ⟨⟨j, a⟩, rfl⟩
  | zero => simpa using K.zero_mem
  | add u w _ _ hu hw =>
      simpa using K.add_mem hu hw
  | smul c u _ hu =>
      simpa using K.smul_mem c hu

lemma independent_injected {α : B → Type*} [∀ j, Fintype (α j)]
    (f : ∀ j, α j → Vec (ι j))
    (hf : ∀ j, LinearIndependent ℝ (f j)) :
    LinearIndependent ℝ (fun a : Sigma α => inject ι a.1 (f a.1 a.2)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  rcases a with ⟨j, a⟩
  have hblock := congrArg (block ι j) hc
  have hsum :
      (∑ b : α j, c ⟨j, b⟩ • f j b) = 0 := by
    simpa [map_sum, block_inject_same, block_inject_ne, Finset.sum_sigma']
      using hblock
  exact (Fintype.linearIndependent_iff.mp (hf j) _ hsum) a

end Blocks

section Inheritance

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {ι : B → Type*} [∀ j, Fintype (ι j)]
variable {U : ∀ j, Set (Vec (ι j))}
variable {X Y Z : Type*} {Xb Yb Zb : B → Type*}

/-- Equation (9), stated on a product of open domains. -/
def PreservesBlockEquivalence (j : B)
    (g : Vec (ι j) → Xb j → Zb j) (G : Blocks.Total ι → X → Z) : Prop :=
  ∀ p ∈ Blocks.domain ι U, ∀ u ∈ U j,
    FunctionalEquiv g u (Blocks.block ι j p) →
      FunctionalEquiv G (Blocks.replace ι j p u) p

/-- Equation (11). -/
def ReflectsBlockEquivalence
    (g : ∀ j, Vec (ι j) → Xb j → Zb j) (G : Blocks.Total ι → X → Z) : Prop :=
  ∀ p ∈ Blocks.domain ι U, ∀ q ∈ Blocks.domain ι U,
    FunctionalEquiv G p q →
      ∀ j, FunctionalEquiv (g j) (Blocks.block ι j p) (Blocks.block ι j q)

/-- Equation (12): compositional identifiability. -/
def CompositionallyIdentifiable
    (g : ∀ j, Vec (ι j) → Xb j → Zb j) (G : Blocks.Total ι → X → Z) : Prop :=
  ∀ p ∈ Blocks.domain ι U, ∀ q ∈ Blocks.domain ι U,
    FunctionalEquiv G p q ↔
      ∀ j, FunctionalEquiv (g j) (Blocks.block ι j p) (Blocks.block ι j q)

lemma compositional_preserves {g : ∀ j, Vec (ι j) → Xb j → Zb j}
    {G : Blocks.Total ι → X → Z}
    (hG : CompositionallyIdentifiable (U := U) g G) (j : B) :
    PreservesBlockEquivalence (U := U) j (g j) G := by
  intro p hp u hu he
  apply (hG _ (Blocks.replace_mem ι hp hu) _ hp).mpr
  intro k
  by_cases hkj : k = j
  · subst k; simpa using he
  · have hb : Blocks.block ι k (Blocks.replace ι j p u) = Blocks.block ι k p := by
      change Blocks.blockLinear ι k
        (p - Blocks.inject ι j (Blocks.block ι j p) + Blocks.inject ι j u) = _
      simp [hkj]
    intro x
    rw [hb]

/-- Proposition 15, the functional-symmetry part. -/
theorem proposition15_symmetry (hU : ∀ j, IsOpen (U j)) (j : B)
    (g : Vec (ι j) → Xb j → Zb j) (G : Blocks.Total ι → X → Z)
    (hG : PreservesBlockEquivalence (U := U) j g G)
    (ψ : FunctionalPartialSymmetry (U j) g) :
    ∃ Ψ : FunctionalPartialSymmetry (Blocks.domain ι U) G,
      Ψ.generator = Blocks.extendField ι j ψ.generator ∧
      (∀ t p, Ψ.flow.toFun t p =
        Blocks.replace ι j p (ψ.flow.toFun t (Blocks.block ι j p))) := by
  obtain ⟨φ, hmap, hdom⟩ := Blocks.exists_liftedFlow ι hU j ψ.flow
  have hinv : IsFunctionalSymmetry G φ := by
    intro t p htp
    obtain ⟨hp, ht⟩ := (hdom t p).mp htp
    rw [hmap t p]
    exact hG p hp _ (ψ.flow.target_mem ht)
      (ψ.invariant t (Blocks.block ι j p) ht)
  exact ⟨⟨_, Blocks.smooth_extendField ι j ψ.smooth_generator, φ, hinv⟩,
    rfl, hmap⟩

/-- Proposition 15, conservation-law inheritance. The larger loss need not
separate predictions. Smoothness of the conserved h is explicit. -/
theorem proposition15_law (hU : ∀ j, IsOpen (U j)) (j : B)
    (g : Vec (ι j) → Xb j → Zb j) (ell : Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z) (Ell : Z → Y → ℝ)
    (hsep : SeparatesPredictions ell)
    (hg : RegularLossOn (U j) (sampleLoss g ell))
    (hG : PreservesBlockEquivalence (U := U) j g G)
    (hL : RegularLossOn (Blocks.domain ι U) (sampleLoss G Ell))
    {h : Vec (ι j) → ℝ} (hh : ContDiffOn ℝ ∞ h (U j))
    (hc : IsConservedOn (U j) (sampleLoss g ell) h) :
    IsConservedOn (Blocks.domain ι U) (sampleLoss G Ell) (Blocks.extendLaw ι j h) := by
  obtain ⟨φ, _, hφ⟩ := proposition9 hg (smooth_gradient_on (hU j) hh)
    ((proposition2 hg (hh.of_le (by simp))).mp hc)
  let ψ : FunctionalPartialSymmetry (U j) g :=
    ⟨gradient h, smooth_gradient_on (hU j) hh, φ, proposition14 g ell hsep φ hφ⟩
  obtain ⟨Ψ, hgen, _⟩ := proposition15_symmetry hU j g G hG ψ
  have hloss := functionalSymmetry_loss G Ell Ψ.flow Ψ.invariant
  apply (proposition2 hL ((Blocks.smooth_extendLaw ι j hh).of_le (by simp))).mpr
  intro p hp
  rw [Blocks.gradient_extendLaw ι hU j (hh.of_le (by simp)) hp]
  have hm := (corollary7 hL Ψ.flow).mp hloss p hp
  simpa only [hgen, Blocks.extendField, ψ] using hm

/-- Infinitesimal form of the reflection hypothesis.  It is proved by
differentiating the reflected functional equivalence along the coupled flow. -/
lemma reflected_generator_component_infinitesimal
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (href : ReflectsBlockEquivalence (U := U) g G)
    {V : Set (Blocks.Total ι)} (hV : IsOpen V) (hVU : V ⊆ Blocks.domain ι U)
    (φ : FunctionalPartialSymmetry V G) {p : Blocks.Total ι} (hp : p ∈ V) :
    ∀ j, Blocks.block ι j (φ.generator p) ∈
      symmetryDistribution (sampleLoss (g j) (ell j)) (Blocks.block ι j p) := by
  intro j
  rw [mem_symmetryDistribution_iff]
  rintro s
  let γ : ℝ → Vec (ι j) :=
    fun t => Blocks.block ι j (φ.flow.toFun t p)
  have hγ :
      HasDerivAt γ (Blocks.block ι j (φ.generator p)) 0 := by
    have hode := φ.flow.ode (φ.flow.zero_mem p hp)
    have hb := hode.clm_apply
      (Blocks.blockLinear ι j).toContinuousLinearMap
    simpa [γ, φ.flow.initial p hp] using hb
  have heq :
      (fun t => sampleLoss (g j) (ell j) s (γ t)) =ᶠ[𝓝 0]
        (fun _ => sampleLoss (g j) (ell j) s (Blocks.block ι j p)) := by
    filter_upwards [
      (φ.flow.open_times p).mem_nhds (φ.flow.zero_mem p hp)
    ] with t ht
    have htargetV : φ.flow.toFun t p ∈ V := φ.flow.target_mem ht
    have heG : FunctionalEquiv G (φ.flow.toFun t p) p :=
      φ.invariant t p ht
    have hej := href (φ.flow.toFun t p) (hVU htargetV) p (hVU hp) heG j
    have hpred := hej s.1
    simpa [sampleLoss, γ] using
      congrArg (fun z => ell j z s.2) hpred
  have hconst :
      HasDerivAt (fun t => sampleLoss (g j) (ell j) s (γ t)) 0 0 :=
    (hasDerivAt_const 0
      (sampleLoss (g j) (ell j) s (Blocks.block ι j p))).congr_of_eventuallyEq
        heq.symm
  have hdiff :
      DifferentiableAt ℝ (sampleLoss (g j) (ell j) s) (Blocks.block ι j p) :=
    differentiableAt_of_c1 (hU j) ((hreg j).c1 s) ((hVU hp) j)
  have hchain := hasDerivAt_observable hdiff hγ
  have hz := hchain.unique hconst
  simpa [γ, real_inner_comm] using hz

/-- Differential step from Appendix F.4. A component of a coupled flow is
integrated after freezing the other initial coordinates. -/
theorem reflected_symmetry_component_spanned
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (hsep : ∀ j, SeparatesPredictions (ell j))
    (href : ReflectsBlockEquivalence (U := U) g G)
    {α : B → Type*}
    (ψ : ∀ j, α j → FunctionalPartialSymmetry (U j) (g j))
    (hψ : ∀ j, CompleteFunctionalSymmetriesOn (U j) (g j) (ψ j))
    {V : Set (Blocks.Total ι)} (hV : IsOpen V) (hVU : V ⊆ Blocks.domain ι U)
    (φ : FunctionalPartialSymmetry V G) {p : Blocks.Total ι} (hp : p ∈ V) :
    ∀ j, Blocks.block ι j (φ.generator p) ∈
      Submodule.span ℝ (Set.range (fun a => (ψ j a).generator (Blocks.block ι j p))) := by
  intro j
  let W : Set (Vec (ι j)) :=
    {u | Blocks.replace ι j p u ∈ V}
  have hreplace_cont :
      Continuous (fun u : Vec (ι j) => Blocks.replace ι j p u) := by
    unfold Blocks.replace
    fun_prop
  have hW : IsOpen W := hV.preimage hreplace_cont
  have hpW : Blocks.block ι j p ∈ W := by
    simpa [W, Blocks.replace_self] using hp
  have hWU : W ⊆ U j := by
    intro u hu
    have hdom := hVU hu
    simpa [W] using hdom j
  let w : Field (Vec (ι j)) :=
    fun u => Blocks.block ι j
      (φ.generator (Blocks.replace ι j p u))
  have hw : ContDiffOn ℝ ∞ w W := by
    exact (Blocks.blockLinear ι j).toContinuousLinearMap.contDiff.comp_contDiffOn
      (φ.smooth_generator.comp
        (by
          unfold Blocks.replace
          fun_prop)
        (fun _ hu => hu))
  have hworth : ∀ u ∈ W,
      w u ∈ symmetryDistribution (sampleLoss (g j) (ell j)) u := by
    intro u hu
    have hi := reflected_generator_component_infinitesimal
      hU g ell G hreg href hV hVU φ hu j
    simpa [w, Blocks.block_replace_same] using hi
  have hregW := (hreg j).mono hW hWU
  obtain ⟨flow, -, hflow⟩ := proposition9 hregW hw hworth
  let φj : FunctionalPartialSymmetry W (g j) :=
    ⟨w, hw, flow, proposition14 (g j) (ell j) (hsep j) flow hflow⟩
  have hspan := (hψ j).2 W hW hWU φj (Blocks.block ι j p) hpW
  simpa [φj, w, Blocks.replace_self] using hspan

/-- The analogous slicing step for conservation laws. For fixed other
coordinates, the component of ∇h is the gradient of the sliced function. -/
theorem reflected_law_component_spanned
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z) (Ell : Z → Y → ℝ)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (href : ReflectsBlockEquivalence (U := U) g G)
    (hL : RegularLossOn (Blocks.domain ι U) (sampleLoss G Ell))
    (hsep : SeparatesPredictions Ell)
    {β : B → Type*} (H : ∀ j, β j → Vec (ι j) → ℝ)
    (hH : ∀ j, CompleteLawsOn (U j) (sampleLoss (g j) (ell j)) (H j))
    {V : Set (Blocks.Total ι)} (hV : IsOpen V) (hVU : V ⊆ Blocks.domain ι U)
    {h : Blocks.Total ι → ℝ} (hh : ContDiffOn ℝ ∞ h V)
    (hc : IsConservedOn V (sampleLoss G Ell) h)
    {p : Blocks.Total ι} (hp : p ∈ V) :
    ∀ j, Blocks.block ι j (gradient h p) ∈
      Submodule.span ℝ (Set.range (fun a => gradient (H j a) (Blocks.block ι j p))) := by
  have hregV := hL.mono hV hVU
  obtain ⟨flow, -, hflow⟩ := proposition9 hregV
    (smooth_gradient_on hV hh)
    ((proposition2 hregV (hh.of_le (by simp))).mp hc)
  let φ : FunctionalPartialSymmetry V G :=
    ⟨gradient h, smooth_gradient_on hV hh, flow,
      proposition14 G Ell hsep flow hflow⟩
  intro j
  let W : Set (Vec (ι j)) :=
    {u | Blocks.replace ι j p u ∈ V}
  have hreplace_cont :
      Continuous (fun u : Vec (ι j) => Blocks.replace ι j p u) := by
    unfold Blocks.replace
    fun_prop
  have hW : IsOpen W := hV.preimage hreplace_cont
  have hpW : Blocks.block ι j p ∈ W := by
    simpa [W, Blocks.replace_self] using hp
  have hWU : W ⊆ U j := by
    intro u hu
    have hdom := hVU hu
    simpa [W] using hdom j
  let hs : Vec (ι j) → ℝ := Blocks.sliceLaw ι j p h
  have hhs : ContDiffOn ℝ ∞ hs W := by
    exact hh.comp
      (by
        unfold Blocks.replace
        fun_prop)
      (fun _ hu => hu)
  have hcons : IsConservedOn W (sampleLoss (g j) (ell j)) hs := by
    apply (proposition2 ((hreg j).mono hW hWU) (hhs.of_le (by simp))).mpr
    intro u hu
    rw [Blocks.gradient_sliceLaw ι hV j p (hh.of_le (by simp)) hu]
    have hi := reflected_generator_component_infinitesimal
      hU g ell G hreg href hV hVU φ hu j
    simpa [φ] using hi
  have hspan := (hH j).2.2.2 W hW hWU hs hhs hcons
    (Blocks.block ι j p) hpW
  rw [Blocks.gradient_sliceLaw ι hV j p (hh.of_le (by simp)) hp] at hspan
  simpa [hs, Blocks.replace_self] using hspan

/-- Proposition 16, symmetry part. The displayed extensions need NOT themselves
be symmetries under the one-way reflection assumption. -/
theorem proposition16_symmetries
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (hsep : ∀ j, SeparatesPredictions (ell j))
    (href : ReflectsBlockEquivalence (U := U) g G)
    {α : B → Type*}
    (ψ : ∀ j, α j → FunctionalPartialSymmetry (U j) (g j))
    (hψ : ∀ j, CompleteFunctionalSymmetriesOn (U j) (g j) (ψ j))
    {V : Set (Blocks.Total ι)} (hV : IsOpen V) (hVU : V ⊆ Blocks.domain ι U)
    (φ : FunctionalPartialSymmetry V G) {p : Blocks.Total ι} (hp : p ∈ V) :
    φ.generator p ∈ Submodule.span ℝ
      (Set.range (fun a : Sigma α =>
        Blocks.extendField ι a.1 (ψ a.1 a.2).generator p)) := by
  exact Blocks.mem_span_of_blocks ι
    (fun j a => (ψ j a).generator (Blocks.block ι j p)) _
    (reflected_symmetry_component_spanned hU g ell G hreg hsep href ψ hψ hV hVU φ hp)

/-- Proposition 16, conservation-law part, for any finite number of blocks. -/
theorem proposition16_laws
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z) (Ell : Z → Y → ℝ)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (href : ReflectsBlockEquivalence (U := U) g G)
    (hL : RegularLossOn (Blocks.domain ι U) (sampleLoss G Ell))
    (hsep : SeparatesPredictions Ell)
    {β : B → Type*} (H : ∀ j, β j → Vec (ι j) → ℝ)
    (hH : ∀ j, CompleteLawsOn (U j) (sampleLoss (g j) (ell j)) (H j))
    {V : Set (Blocks.Total ι)} (hV : IsOpen V) (hVU : V ⊆ Blocks.domain ι U)
    {h : Blocks.Total ι → ℝ} (hh : ContDiffOn ℝ ∞ h V)
    (hc : IsConservedOn V (sampleLoss G Ell) h)
    {p : Blocks.Total ι} (hp : p ∈ V) :
    gradient h p ∈ Submodule.span ℝ
      (Set.range (fun a : Sigma β => gradient (Blocks.extendLaw ι a.1 (H a.1 a.2)) p)) := by
  have he : (fun a : Sigma β => gradient (Blocks.extendLaw ι a.1 (H a.1 a.2)) p) =
      (fun a : Sigma β => Blocks.inject ι a.1
        (gradient (H a.1 a.2) (Blocks.block ι a.1 p))) := by
    funext a
    exact Blocks.gradient_extendLaw ι hU a.1
      ((hH a.1).1 a.2 |>.of_le (by simp)) (hVU hp)
  rw [he]
  exact Blocks.mem_span_of_blocks ι _ _
    (reflected_law_component_spanned hU g ell G Ell hreg href hL hsep H hH hV hVU hh hc hp)

/-- Theorem 17, conservation laws, with explicit disjoint-block independence. -/
theorem theorem17_laws
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z) (Ell : Z → Y → ℝ)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (hsep : ∀ j, SeparatesPredictions (ell j))
    (hG : CompositionallyIdentifiable (U := U) g G)
    (hL : RegularLossOn (Blocks.domain ι U) (sampleLoss G Ell))
    (hSep : SeparatesPredictions Ell)
    {β : B → Type*} [∀ j, Fintype (β j)]
    (H : ∀ j, β j → Vec (ι j) → ℝ)
    (hH : ∀ j, CompleteLawsOn (U j) (sampleLoss (g j) (ell j)) (H j)) :
    CompleteLawsOn (Blocks.domain ι U) (sampleLoss G Ell)
      (fun a : Sigma β => Blocks.extendLaw ι a.1 (H a.1 a.2)) := by
  have href : ReflectsBlockEquivalence (U := U) g G :=
    fun p hp q hq he => (hG p hp q hq).mp he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact Blocks.smooth_extendLaw ι a.1 ((hH a.1).1 a.2)
  · intro a
    exact proposition15_law hU a.1 (g a.1) (ell a.1) G Ell (hsep a.1)
      (hreg a.1) (compositional_preserves hG a.1) hL
      ((hH a.1).1 a.2) ((hH a.1).2.1 a.2)
  · intro p hp
    have he : (fun a : Sigma β => gradient (Blocks.extendLaw ι a.1 (H a.1 a.2)) p) =
        (fun a : Sigma β => Blocks.inject ι a.1
          (gradient (H a.1 a.2) (Blocks.block ι a.1 p))) := by
      funext a
      exact Blocks.gradient_extendLaw ι hU a.1
        (((hH a.1).1 a.2).of_le (by simp)) hp
    rw [he]
    exact Blocks.independent_injected ι _ (fun j => (hH j).2.2.1 _ (hp j))
  · intro V hV hVU h hh hc p hp
    exact proposition16_laws hU g ell G Ell hreg href hL hSep H hH hV hVU hh hc hp

/-- Theorem 17, functional symmetries. -/
theorem theorem17_symmetries
    (hU : ∀ j, IsOpen (U j))
    (g : ∀ j, Vec (ι j) → Xb j → Zb j)
    (ell : ∀ j, Zb j → Yb j → ℝ)
    (G : Blocks.Total ι → X → Z)
    (hreg : ∀ j, RegularLossOn (U j) (sampleLoss (g j) (ell j)))
    (hsep : ∀ j, SeparatesPredictions (ell j))
    (hG : CompositionallyIdentifiable (U := U) g G)
    {α : B → Type*} [∀ j, Fintype (α j)]
    (ψ : ∀ j, α j → FunctionalPartialSymmetry (U j) (g j))
    (hψ : ∀ j, CompleteFunctionalSymmetriesOn (U j) (g j) (ψ j)) :
    ∃ Ψ : Sigma α → FunctionalPartialSymmetry (Blocks.domain ι U) G,
      (∀ a, (Ψ a).generator = Blocks.extendField ι a.1 (ψ a.1 a.2).generator) ∧
      CompleteFunctionalSymmetriesOn (Blocks.domain ι U) G Ψ := by
  have hex : ∀ a : Sigma α,
      ∃ φ : FunctionalPartialSymmetry (Blocks.domain ι U) G,
        φ.generator = Blocks.extendField ι a.1 (ψ a.1 a.2).generator := by
    intro a
    obtain ⟨φ, hφ, _⟩ := proposition15_symmetry hU a.1 (g a.1) G
      (compositional_preserves hG a.1) (ψ a.1 a.2)
    exact ⟨φ, hφ⟩
  choose Ψ hΨ using hex
  refine ⟨Ψ, hΨ, ?_, ?_⟩
  · intro p hp
    have he : (fun a : Sigma α => (Ψ a).generator p) =
        (fun a : Sigma α => Blocks.inject ι a.1
          ((ψ a.1 a.2).generator (Blocks.block ι a.1 p))) := by
      funext a; rw [hΨ a]; rfl
    rw [he]
    exact Blocks.independent_injected ι _ (fun j => (hψ j).1 _ (hp j))
  · intro V hV hVU φ p hp
    have he : (fun a : Sigma α => (Ψ a).generator p) =
        (fun a : Sigma α => Blocks.extendField ι a.1 (ψ a.1 a.2).generator p) := by
      funext a; rw [hΨ a]
    rw [he]
    exact proposition16_symmetries hU g ell G hreg hsep
      (fun p hp q hq he => (hG p hp q hq).mp he) ψ hψ hV hVU φ hp

end Inheritance
end GradientFlowPaper

end -- noncomputable section


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

variable [HasMaximalSmoothLocalFlows]

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
    [HasMarcotteMatrixFactorizationCompleteness]
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
    [HasMarcotteMatrixFactorizationCompleteness]
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


/-! ## Source module: GradientFlowPaper/Polynomial.lean -/


/-!
Proposition 19 and Appendix G.2.

The paper's "finite-to-one" means finite-to-one MODULO the standard scaling
and permutation symmetries, not finite parameter fibres. Since permutations
form a finite group, they may be absorbed in a finite set of representatives;
`FiniteToOneAt` below therefore quotients by all nonzero diagonal scalings.

The paper does not further define the word "generic" in Proposition 19.
Accordingly, Stage 1 keeps genericity as an abstract predicate and records
exactly the consequences used in Appendix G.2: after excluding the finite
discrete branches, the local functional fibre is the diagonal-scaling orbit,
and its infinitesimal generators are independent. Stage 2 will derive that
regime from the precise Usevich et al. identifiability theorem rather than
silently substituting a convenient coordinate condition.
-/

noncomputable section
open Set Function
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix

namespace GradientFlowPaper
namespace PolynomialNetwork

variable [HasMaximalSmoothLocalFlows]

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

/-! The paper's proof of Proposition 19 uses the finite-to-one identifiability
result directly; no auxiliary finite evaluation grid is needed here. -/

/-- The paper deliberately leaves “generic” implicit.  Stage 1 therefore
keeps it as an abstract predicate rather than identifying it with an
invented coordinate condition.  The interface records exactly the two
consequences of genericity/finite-to-one used in Appendix G.2:
(1) local functional fibres are diagonal-scaling orbits after discrete
branches are excluded, and (2) the scaling generators are independent on
the chosen neighborhood. -/
class HasPNNGenericRegime
    (A : Architecture) (Generic : Param A → Prop) : Prop where
  local_regime :
    ∀ {p₀ : Param A}, FiniteToOneAt A p₀ → Generic p₀ →
      ∃ U : Set (Param A), IsOpen U ∧ p₀ ∈ U ∧
        (∀ p ∈ U,
          LinearIndependent ℝ (fun a : Hidden A => generator A a p)) ∧
        (∀ p ∈ U, ∀ q ∈ U,
          FunctionalEquiv (model A) p q ↔
            ∃ s : Hidden A → ℝˣ, q = diagonalGauge A s p)

/-- Standard tangent-space fact for the regular diagonal-scaling orbit.  It
is implicit in the dimension argument in Appendix G.2 and is kept explicit
as Stage-1 differential-geometric background. -/
class HasPNNScalingOrbitTangent (A : Architecture) : Prop where
  tangent_mem_span :
    ∀ {p : Param A},
      LinearIndependent ℝ (fun a : Hidden A => generator A a p) →
      ∀ {γ : ℝ → Param A} {v : Param A},
        HasDerivAt γ v 0 → γ 0 = p →
        (∀ᶠ t in 𝓝 0,
          ∃ s : Hidden A → ℝˣ, γ t = diagonalGauge A s p) →
        v ∈ Submodule.span ℝ
          (Set.range (fun a : Hidden A => generator A a p))

theorem local_scaling_identifiability
    {Generic : Param A → Prop} [HasPNNGenericRegime A Generic]
    {p₀ : Param A}
    (hfinite : FiniteToOneAt A p₀) (hgeneric : Generic p₀) :
    ∃ U : Set (Param A), IsOpen U ∧ p₀ ∈ U ∧
      (∀ p ∈ U,
        LinearIndependent ℝ (fun a : Hidden A => generator A a p)) ∧
      (∀ p ∈ U, ∀ q ∈ U,
        FunctionalEquiv (model A) p q ↔
          ∃ s : Hidden A → ℝˣ, q = diagonalGauge A s p) :=
  HasPNNGenericRegime.local_regime hfinite hgeneric

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
theorem conserved_gradient_spanned [HasPNNScalingOrbitTangent A]
    {U : Set (Param A)} (hU : IsOpen U)
    (hind : ∀ p ∈ U,
      LinearIndependent ℝ (fun a : Hidden A => generator A a p))
    (hident : ∀ p ∈ U, ∀ q ∈ U, FunctionalEquiv (model A) p q ↔
      ∃ s : Hidden A → ℝˣ, q = diagonalGauge A s p)
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
  have horbit : ∀ᶠ t in 𝓝 0,
      ∃ s : Hidden A → ℝˣ, γ t = diagonalGauge A s p := by
    filter_upwards [(ψ.open_times p).mem_nhds (ψ.zero_mem p hp)] with t ht
    apply (hident _ (hVU (ψ.target_mem ht)) p (hVU hp)).mp
    exact hψfun t p ht
  have hspan :=
    HasPNNScalingOrbitTangent.tangent_mem_span
      (hind p (hVU hp)) hγ hγ0 horbit
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

/-- Proposition 19 in the explicit generic regime described above. -/
theorem proposition19
    {Generic : Param A → Prop}
    [HasPNNGenericRegime A Generic] [HasPNNScalingOrbitTangent A]
    {Y : Type*} (ell : Output A → Y → ℝ)
    (hsep : SeparatesPredictions ell)
    (hL : RegularLossOn Set.univ (sampleLoss (model A) ell))
    {p₀ : Param A} (hfinite : FiniteToOneAt A p₀)
    (hgeneric : Generic p₀) :
    ∃ U : Set (Param A), IsOpen U ∧ p₀ ∈ U ∧
      CompleteLawsOn U (sampleLoss (model A) ell) (law A) := by
  obtain ⟨U, hU, hpU, hind, hident⟩ :=
    local_scaling_identifiability A hfinite hgeneric
  have hreg := hL.mono hU (Set.subset_univ U)
  refine ⟨U, hU, hpU, (fun a => (law_smooth A a).contDiffOn),
    (fun a => laws_conserved A ell hreg a),
    independent_laws_of_generators A hind, ?_⟩
  intro V hV hVU h hh hc p hp
  exact conserved_gradient_spanned A hU hind hident
    ell hsep hreg hV hVU hh hc p hp

theorem number_of_laws :
    Fintype.card (Hidden A) = ∑ j : Fin (A.depth - 1), A.width (j.val + 1) := by
  simp [Hidden, Fintype.card_sigma]

end PolynomialNetwork
end GradientFlowPaper

end -- noncomputable section


/-! ## Source module: GradientFlowPaper/DeepLinear.lean -/


/-!
Proposition 20 and Appendix G.3.

Only the paper's UPPER BOUND is asserted. In particular, (L-1)D² is not
claimed to be the number of independent conservation laws.

For an arbitrary separating loss, pointwise loss gradients can degenerate.
The proof therefore places gradients of smooth conservation laws in the
product map's vertical space by integrating their functional symmetries;
it does not assume W^⊥ = ker D(product) at every point.
-/

noncomputable section
open Set Function Filter
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix

namespace GradientFlowPaper
namespace DeepLinear

variable [HasMaximalSmoothLocalFlows]

abbrev Index (L D : ℕ) := Fin L × Fin D × Fin D
abbrev Param (L D : ℕ) := Vec (Index L D)

variable {L D : ℕ}

def W (p : Param L D) (j : Fin L) : Mat D D := fun a b => p (j, a, b)

def productPrefix (p : Param L D) : (j : ℕ) → j ≤ L → Mat D D
  | 0, _ => 1
  | j + 1, hj => W p ⟨j, by omega⟩ * productPrefix p j (by omega)

def product (p : Param L D) : Mat D D := productPrefix p L le_rfl

lemma W_contDiff (j : Fin L) : ContDiff ℝ ∞ (fun p : Param L D => W p j) := by
  unfold W
  fun_prop

/-- Every prefix is invertible on the full-rank stratum.  The proof descends
from the total product using multiplicativity of the determinant. -/
lemma productPrefix_isUnit_of_regular (hL : 0 < L) {p : Param L D}
    (hp : p ∈ regular) (j : ℕ) (hj : j ≤ L) :
    IsUnit (productPrefix p j hj) := by
  have htop : IsUnit (productPrefix p L le_rfl) := hp
  have hdetTop : IsUnit (Matrix.det (productPrefix p L le_rfl)) := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp htop
  have descend : ∀ n ≤ L, IsUnit (Matrix.det (productPrefix p n (by omega))) := by
    intro n hn
    induction hgap : L - n using Nat.strong_induction_on generalizing n with
    | h d ih =>
        by_cases hEq : n = L
        · subst n
          simpa using hdetTop
        · have hnlt : n < L := lt_of_le_of_ne hn hEq
          have hnext :
              IsUnit (Matrix.det (productPrefix p (n + 1) (by omega))) :=
            ih (L - (n + 1)) (by omega) (n + 1) (by omega) rfl
          rw [productPrefix, Matrix.det_mul] at hnext
          exact ((Commute.all
            (Matrix.det (W p ⟨n, by omega⟩))
            (Matrix.det (productPrefix p n (by omega)))).isUnit_mul_iff.mp hnext).2
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  convert descend j hj

def model (p : Param L D) (x : Vec (Fin D)) : Vec (Fin D) :=
  WithLp.toLp 2 ((product p).mulVec x.ofLp)

def regular : Set (Param L D) := {p | IsUnit (product p)}

/-- S₀ = S_L = I, including the L=1 case with no internal gauge factors. -/
def boundaryGauge (s : Fin (L - 1) → GL D) (j : ℕ) (hj : j ≤ L) : GL D :=
  if h : j = 0 ∨ j = L then 1 else s ⟨j - 1, by omega⟩

/-- The left-action formula in Appendix G.3. -/
def gauge (s : Fin (L - 1) → GL D) (p : Param L D) : Param L D :=
  WithLp.toLp 2 (fun a =>
    ((boundaryGauge s (a.1.val + 1) (by have := a.1.isLt; omega) : Mat D D) *
      W p a.1 *
      ((boundaryGauge s a.1.val (by have := a.1.isLt; omega))⁻¹ : GL D).val)
        a.2.1 a.2.2)

theorem product_gauge (s : Fin (L - 1) → GL D) (p : Param L D) :
    product (gauge s p) = product p := by
  have hprefix :
      ∀ j (hj : j ≤ L),
        productPrefix (gauge s p) j hj =
          (boundaryGauge s j hj : Mat D D) * productPrefix p j hj := by
    intro j
    induction j with
    | zero =>
        intro hj
        simp [productPrefix, boundaryGauge]
    | succ j ih =>
        intro hj
        have hj' : j ≤ L := by omega
        rw [productPrefix, productPrefix, ih hj']
        simp [gauge, W, boundaryGauge, Matrix.mul_assoc]
  unfold product
  rw [hprefix L le_rfl]
  simp [boundaryGauge]

theorem functionalEquiv_iff_product (p q : Param L D) :
    FunctionalEquiv model p q ↔ product p = product q := by
  constructor
  · intro he
    ext i j
    have hj := congrArg (fun x : Vec (Fin D) => x i)
      (he (EuclideanSpace.single j 1))
    simpa [model, Matrix.mulVec, dotProduct] using hj
  · intro he x
    simp [model, he]

theorem fullRank_fiber (hL : 0 < L) {p q : Param L D}
    (hp : p ∈ regular) (hq : q ∈ regular) :
    FunctionalEquiv model p q ↔ ∃ s : Fin (L - 1) → GL D, q = gauge s p := by
  constructor
  · intro he
    have hprod : product p = product q :=
      (functionalEquiv_iff_product p q).mp he
    let T : (j : ℕ) → j ≤ L → Mat D D :=
      fun j hj =>
        productPrefix q j hj * (productPrefix p j hj)⁻¹
    have hTunit : ∀ j (hj : j ≤ L), IsUnit (T j hj) := by
      intro j hj
      exact (productPrefix_isUnit_of_regular hL hq j hj).mul
        (productPrefix_isUnit_of_regular hL hp j hj).inv
    have hTzero : T 0 (by omega) = 1 := by
      simp [T, productPrefix]
    have hTtop : T L le_rfl = 1 := by
      have hpunit := productPrefix_isUnit_of_regular hL hp L le_rfl
      simp [T, product, hprod, hpunit]
    have hlayer : ∀ j (hj : j < L),
        W q ⟨j, hj⟩ =
          T (j + 1) (by omega) * W p ⟨j, hj⟩ *
            (T j (by omega))⁻¹ := by
      intro j hj
      have hprefp := productPrefix_isUnit_of_regular hL hp j (by omega)
      have hprefq := productPrefix_isUnit_of_regular hL hq j (by omega)
      have hWp :
          IsUnit (W p ⟨j, hj⟩) := by
        have hnext := productPrefix_isUnit_of_regular hL hp (j + 1) (by omega)
        rw [productPrefix] at hnext
        exact (Matrix.isUnit_iff_isUnit_det _).mpr <| by
          rw [Matrix.isUnit_iff_isUnit_det] at hnext
          rw [Matrix.det_mul] at hnext
          exact ((Commute.all _ _).isUnit_mul_iff.mp hnext).1
      simp only [T, productPrefix]
      calc
        W q ⟨j, hj⟩
            = (W q ⟨j, hj⟩ * productPrefix q j (by omega)) *
                (productPrefix q j (by omega))⁻¹ := by
                  simp [Matrix.mul_assoc, hprefq]
        _ = ((W q ⟨j, hj⟩ * productPrefix q j (by omega)) *
                (W p ⟨j, hj⟩ * productPrefix p j (by omega))⁻¹) *
              W p ⟨j, hj⟩ *
              (productPrefix q j (by omega) *
                (productPrefix p j (by omega))⁻¹)⁻¹ := by
                  simp [Matrix.mul_assoc, hprefp, hprefq, hWp]
        _ = T (j + 1) (by omega) * W p ⟨j, hj⟩ *
              (T j (by omega))⁻¹ := by rfl
    have hSint : ∀ a : Fin (L - 1), IsUnit (T (a.val + 1) (by omega)) :=
      fun a => hTunit _ _
    choose s hs using hSint
    refine ⟨s, ?_⟩
    ext a
    rcases a with ⟨j, x, y⟩
    have hj : j.val < L := j.isLt
    have hleft :
        (boundaryGauge s (j.val + 1) (by omega) : Mat D D) =
          T (j.val + 1) (by omega) := by
      by_cases htop : j.val + 1 = L
      · simp [boundaryGauge, htop, hTtop]
      · have hpos : j.val + 1 ≠ 0 := by omega
        simp [boundaryGauge, htop, hpos, hs]
    have hright :
        ((boundaryGauge s j.val (by omega))⁻¹ : GL D).val =
          (T j.val (by omega))⁻¹ := by
      by_cases hzero : j.val = 0
      · simp [boundaryGauge, hzero, hTzero]
      · have hnotTop : j.val ≠ L := by omega
        simp [boundaryGauge, hzero, hnotTop, hs]
    have hmat := hlayer j.val hj
    rw [hleft, hright] at *
    simpa [gauge, W] using congrFun₂ hmat x y
  · rintro ⟨s, rfl⟩
    exact (functionalEquiv_iff_product p (gauge s p)).mpr (product_gauge s p).symm

/-- The vertical subspace of the product map at a parameter. -/
def vertical (p : Param L D) : Submodule ℝ (Param L D) :=
  LinearMap.ker (fderiv ℝ (product (L := L) (D := D)) p).toLinearMap

theorem product_smooth : ContDiff ℝ ∞ (product (L := L) (D := D)) := by
  have hprefix :
      ∀ j (hj : j ≤ L),
        ContDiff ℝ ∞ (fun p : Param L D => productPrefix p j hj) := by
    intro j
    induction j with
    | zero =>
        intro hj
        simpa [productPrefix] using contDiff_const
    | succ j ih =>
        intro hj
        have hj' : j ≤ L := by omega
        simpa [productPrefix] using
          (W_contDiff (L := L) (D := D) ⟨j, by omega⟩).mul
            (ih hj')
  exact hprefix L le_rfl

theorem regular_isOpen : IsOpen (regular : Set (Param L D)) := by
  have hcont : Continuous (fun p : Param L D => Matrix.det (product p)) :=
    Matrix.continuous_det.comp product_smooth.continuous
  have heq : (regular : Set (Param L D)) =
      (fun p => Matrix.det (product p)) ⁻¹' ({0} : Set ℝ)ᶜ := by
    ext p
    simp [regular, Matrix.isUnit_iff_isUnit_det]
  rw [heq]
  exact isOpen_compl_singleton.preimage hcont

theorem product_derivative_surjective (hL : 0 < L) {p : Param L D}
    (hp : p ∈ regular) :
    Function.Surjective (fderiv ℝ (product (L := L) (D := D)) p) := by
  have hinv :
      IsUnit (productPrefix p (L - 1) (by omega)) :=
    productPrefix_isUnit_of_regular hL hp _ (by omega)
  intro Y
  let P : Mat D D := productPrefix p (L - 1) (by omega)
  let δ : Param L D :=
    WithLp.toLp 2 (fun a =>
      if h : a.1.val = L - 1 then (Y * P⁻¹) a.2.1 a.2.2 else 0)
  have hprefix_const : ∀ t : ℝ,
      productPrefix (p + t • δ) (L - 1) (by omega) = P := by
    intro t
    induction L with
    | zero => omega
    | succ L ih =>
        simp only [P]
        apply productPrefix_congr
        intro j hj
        ext a b
        simp [W, δ]
        have : j.val ≠ L := by omega
        simp [this]
  have hline : ∀ t : ℝ,
      product (p + t • δ) = product p + t • Y := by
    intro t
    rw [show product (p + t • δ) =
      W (p + t • δ) ⟨L - 1, by omega⟩ *
        productPrefix (p + t • δ) (L - 1) (by omega) by
          simp [product, productPrefix, hL]]
    rw [hprefix_const]
    rw [show W (p + t • δ) ⟨L - 1, by omega⟩ =
      W p ⟨L - 1, by omega⟩ + t • (Y * P⁻¹) by
        ext a b
        simp [W, δ]]
    simp [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, P, hinv]
  have hcurve :
      HasDerivAt (fun t : ℝ => product (p + t • δ)) Y 0 := by
    convert (hasDerivAt_id (x := 0)).smul_const Y |>.const_add (product p) using 1
    · ext t
      simpa [add_comm] using hline t
    · simp
  have hparam :
      HasDerivAt (fun t : ℝ => p + t • δ) δ 0 := by
    simpa using (hasDerivAt_id (x := 0)).smul_const δ |>.const_add p
  have hchain :=
    (product_smooth (L := L) (D := D)).differentiable
      (by simp) p |>.hasFDerivAt.comp_hasDerivAt 0 hparam
  exact ⟨δ, hchain.unique hcurve⟩

theorem vertical_rank (hL : 0 < L) {p : Param L D} (hp : p ∈ regular) :
    Module.finrank ℝ (vertical p) = (L - 1) * D^2 := by
  let F := (fderiv ℝ (product (L := L) (D := D)) p).toLinearMap
  have hsurj : Function.Surjective F := product_derivative_surjective hL hp
  have hrtop : LinearMap.range F = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := LinearMap.finrank_range_add_finrank_ker F
  have hpar : Module.finrank ℝ (Param L D) = L * D^2 := by
    simp [Param, Index, pow_two, mul_assoc]
  have hout : Module.finrank ℝ (Mat D D) = D^2 := by
    simp [Mat, Matrix, pow_two]
  have hk : D^2 + Module.finrank ℝ (vertical p) = L * D^2 := by
    simpa [F, vertical, hrtop, hpar, hout] using hdim
  have hLsplit : L = (L - 1) + 1 := by omega
  rw [hLsplit, Nat.add_mul] at hk
  omega

/-- Gradients of smooth conserved quantities are genuine vertical directions. -/
theorem conserved_gradient_vertical {Y : Type*} {U : Set (Param L D)}
    (ell : Vec (Fin D) → Y → ℝ) (hsep : SeparatesPredictions ell)
    (hreg : RegularLossOn U (sampleLoss model ell))
    {h : Param L D → ℝ} (hh : ContDiffOn ℝ ∞ h U)
    (hc : IsConservedOn U (sampleLoss model ell) h)
    {p : Param L D} (hp : p ∈ U) : gradient h p ∈ vertical p := by
  obtain ⟨ψ, _, hψ⟩ := proposition9 hreg (smooth_gradient_on hreg.isOpen hh)
    ((proposition2 hreg (hh.of_le (by simp))).mp hc)
  have hfun := proposition14 model ell hsep ψ hψ
  have heq : (fun t => product (ψ.toFun t p)) =ᶠ[𝓝 0] (fun _ => product p) := by
    filter_upwards [(ψ.open_times p).mem_nhds (ψ.zero_mem p hp)] with t ht
    exact (functionalEquiv_iff_product (ψ.toFun t p) p).mp (hfun t p ht)
  have hzero : HasDerivAt (fun t => product (ψ.toFun t p)) 0 0 :=
    (hasDerivAt_const 0 (product p)).congr_of_eventuallyEq heq.symm
  have hder := (product_smooth.differentiable (by simp) (ψ.toFun 0 p)).hasFDerivAt.comp_hasDerivAt
    0 (ψ.ode (ψ.zero_mem p hp))
  have he := hder.unique hzero
  change (fderiv ℝ product p) (gradient h p) = 0
  simpa only [ψ.initial p hp] using he

/-- Pointwise form of Proposition 20, requiring no extra constant-rank
assumption for the Lie completion of the loss distribution. -/
theorem independent_laws_bound (hL : 0 < L)
    {Y : Type*} {U : Set (Param L D)}
    (ell : Vec (Fin D) → Y → ℝ) (hsep : SeparatesPredictions ell)
    (hreg : RegularLossOn U (sampleLoss model ell))
    {n : ℕ} (h : Fin n → Param L D → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (hc : ∀ i, IsConservedOn U (sampleLoss model ell) (h i))
    (hind : FunctionallyIndependentOn U h)
    {p : Param L D} (hp : p ∈ U) (hrank : p ∈ regular) :
    n ≤ (L - 1) * D^2 := by
  let v : Fin n → vertical p :=
    fun i => ⟨gradient (h i) p, conserved_gradient_vertical ell hsep hreg (hh i) (hc i) hp⟩
  have hi : LinearIndependent ℝ v := (hind p hp).of_comp (vertical p).subtype
  have hb : n ≤ Module.finrank ℝ (vertical p) := by
    simpa using hi.fintype_card_le_finrank
  simpa only [vertical_rank hL hrank] using hb

/-- Proposition 20. -/
theorem proposition20 (hL : 0 < L) (hD : 0 < D)
    {Y : Type*} (ell : Vec (Fin D) → Y → ℝ) (hsep : SeparatesPredictions ell)
    (hreg : RegularLossOn (regular : Set (Param L D)) (sampleLoss model ell))
    {p₀ : Param L D} (hp₀ : p₀ ∈ regular) :
    ∃ U : Set (Param L D), IsOpen U ∧ p₀ ∈ U ∧ U ⊆ regular ∧
      ∀ (n : ℕ) (h : Fin n → Param L D → ℝ),
        (∀ i, ContDiffOn ℝ ∞ (h i) U) →
        (∀ i, IsConservedOn U (sampleLoss model ell) (h i)) →
        FunctionallyIndependentOn U h → n ≤ (L - 1) * D^2 := by
  refine ⟨regular, regular_isOpen, hp₀, Set.Subset.rfl, ?_⟩
  intro n h hh hc hind
  exact independent_laws_bound hL ell hsep hreg h hh hc hind hp₀ hp₀

end DeepLinear
end GradientFlowPaper

end -- noncomputable section


/-! ## Source module: GradientFlowPaper/Examples.lean -/


/-!
Selected appendices: the nonlinear scalar example in B.2, and Lemma 29 in H.
Appendix I's empirical training observations are not encoded as mathematical
theorems. No SGD conservation theorem is inferred from gradient-flow conservation.
-/

noncomputable section
open Set Function
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix MatrixOrder

namespace GradientFlowPaper
namespace NonlinearScalarExample

abbrev Param := Vec (Fin 2)

def model (p : Param) (x : ℝ) : ℝ := p 0 * Real.exp (2 * p 1) * x

def symmetry (t : ℝ) (p : Param) : Param :=
  WithLp.toLp 2 ![p 0 * Real.exp (-2 * t), p 1 + t]

def law (p : Param) : ℝ := -(p 0)^2 + p 1

def generator (p : Param) : Param := WithLp.toLp 2 ![-2 * p 0, 1]

theorem symmetry_functional (t : ℝ) (p : Param) :
    FunctionalEquiv model (symmetry t p) p := by
  intro x
  have he : Real.exp (-2 * t) * Real.exp (2 * (p 1 + t)) = Real.exp (2 * p 1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (p 0 * Real.exp (-2 * t)) * Real.exp (2 * (p 1 + t)) * x = _
  rw [mul_assoc (p 0), he]
  rfl

theorem law_gradient (p : Param) : gradient law p = generator p := by
  apply (InnerProductSpace.toDual ℝ Param).injective
  rw [toDual_gradient]
  ext v
  rw [← inner_gradient_left]
  change (-2 * p 0) * v 0 + v 1 =
    ⟪generator p, v⟫_ℝ
  simp [generator, inner, Fin.sum_univ_two]
  ring

end NonlinearScalarExample

namespace LearningToScale

/-- The square root in Lemma 29 is specified by its mathematical properties,
not by an unverified choice of a matrix-square-root library API. -/
def PositiveSquareRoot (A R : Mat 2 2) : Prop :=
  Matrix.PosDef R ∧ R * R = A

/-- P = (H₀ + sqrt(H₀² + 4α²I))/2 from equations (18)--(19). -/
def gramCandidate (H₀ R : Mat 2 2) : Mat 2 2 := (1 / 2 : ℝ) • (H₀ + R)

def IsOrthogonal (Q : Mat 2 2) : Prop := Qᵀ * Q = 1

lemma positiveSquareRoot_cfc {A : Mat 2 2} (hA : Matrix.PosDef A) :
    PositiveSquareRoot A (CFC.sqrt A) := by
  have hsem : Matrix.PosSemidef (CFC.sqrt A) :=
    (CFC.sqrt_nonneg A).posSemidef
  have hunit : IsUnit (CFC.sqrt A) :=
    (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).2 hA.isUnit
  have hpos : Matrix.PosDef (CFC.sqrt A) :=
    hsem.posDef_iff_isUnit.mpr hunit
  have hsq : CFC.sqrt A * CFC.sqrt A = A := by
    simpa [pow_two] using (CFC.sq_sqrt A)
  exact ⟨hpos, hsq⟩

lemma posDef_sq_add_scalar_one (H : Mat 2 2) (hH : Hᵀ = H)
    {c : ℝ} (hc : 0 < c) :
    Matrix.PosDef (H * H + c • (1 : Mat 2 2)) := by
  have hsq : Matrix.PosSemidef (H * H) := by
    have h := Matrix.posSemidef_conjTranspose_mul_self H
    simpa [star_eq_transpose, hH] using h
  have hcI : Matrix.PosDef (c • (1 : Mat 2 2)) :=
    (Matrix.PosDef.one).smul hc
  exact hsq.posSemidef_add hcI

lemma positiveSquareRoot_eq_cfc {A R : Mat 2 2}
    (hA : Matrix.PosDef A) (hR : PositiveSquareRoot A R) :
    R = CFC.sqrt A := by
  rw [eq_comm, CFC.sqrt_eq_iff A R
    hA.posSemidef.nonneg hR.1.posSemidef.nonneg]
  simpa [pow_two] using hR.2.symm

lemma positiveSquareRoot_commutes_with_base
    (H : Mat 2 2) (hH : Hᵀ = H) (α : ℝ) (hα : α ≠ 0)
    (R : Mat 2 2)
    (hR : PositiveSquareRoot
      (H * H + (4 * α^2) • (1 : Mat 2 2)) R) :
    Commute H R := by
  let A : Mat 2 2 := H * H + (4 * α^2) • (1 : Mat 2 2)
  have hA : Matrix.PosDef A := by
    dsimp [A]
    exact posDef_sq_add_scalar_one H hH
      (by positivity [sq_pos_of_ne_zero hα])
  have hReq : R = CFC.sqrt A := positiveSquareRoot_eq_cfc hA hR
  have hAH : Commute A H := by
    rw [Commute, SemiconjBy]
    dsimp [A]
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    noncomm_ring
  rw [hReq, CFC.sqrt]
  exact (hAH.cfcₙ_nnreal NNReal.sqrt).symm

lemma gramCandidate_posDef_mathlib
    (H : Mat 2 2) (hH : Hᵀ = H) (α : ℝ) (hα : α ≠ 0)
    (R : Mat 2 2)
    (hR : PositiveSquareRoot
      (H * H + (4 * α^2) • (1 : Mat 2 2)) R) :
    Matrix.PosDef (gramCandidate H R) := by
  let A : Mat 2 2 := H * H + (4 * α^2) • (1 : Mat 2 2)
  have hA : Matrix.PosDef A := by
    dsimp [A]
    exact posDef_sq_add_scalar_one H hH
      (by positivity [sq_pos_of_ne_zero hα])
  have hReq : R = CFC.sqrt A := positiveSquareRoot_eq_cfc hA hR
  have hHself : IsSelfAdjoint H := by
    simpa [star_eq_transpose] using hH
  have hcI : 0 ≤ (4 * α^2) • (1 : Mat 2 2) := by
    exact ((Matrix.PosDef.one).smul
      (by positivity [sq_pos_of_ne_zero hα])).posSemidef.nonneg
  have hsq_le : H * H ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right hcI
  have habsR : CFC.abs H ≤ R := by
    rw [hReq]
    have hs := CFC.sqrt_le_sqrt (H * H) A hsq_le
    simpa [CFC.abs, hHself.star_eq] using hs
  have hnegabs : -H ≤ CFC.abs H := by
    rw [← sub_nonneg, sub_neg_eq_add, CFC.abs_add_self H hHself]
    exact smul_nonneg (by norm_num) (CFC.posPart_nonneg H)
  have hsum_nonneg : 0 ≤ H + R := by
    exact (neg_le_iff_add_nonneg).mp (hnegabs.trans habsR)
  have hPsem : Matrix.PosSemidef (gramCandidate H R) := by
    unfold gramCandidate
    exact (smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hsum_nonneg).posSemidef
  have hcomm := positiveSquareRoot_commutes_with_base H hH α hα R hR
  have hinj : Function.Injective (gramCandidate H R).mulVec := by
    intro x y hxy
    let z := x - y
    have hzP : gramCandidate H R *ᵥ z = 0 := by
      simp [z, Matrix.mulVec_sub, hxy]
    have hzsum : (H + R) *ᵥ z = 0 := by
      have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
      simpa [gramCandidate, Matrix.smul_mulVec, hhalf] using hzP
    have hRz : R *ᵥ z = -(H *ᵥ z) := by
      simpa [Matrix.add_mulVec, eq_neg_iff_add_eq_zero] using hzsum
    have hR2z : (R * R) *ᵥ z = (H * H) *ᵥ z := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hRz]
      have hc := congrArg (fun w => w *ᵥ z) hcomm.eq
      simp only [Matrix.mulVec_mulVec] at hc
      rw [hc, hRz]
      simp
    have hcz : ((4 * α^2) • (1 : Mat 2 2)) *ᵥ z = 0 := by
      have hrsq := congrArg (fun M : Mat 2 2 => M *ᵥ z) hR.2
      simp only [Matrix.add_mulVec] at hrsq
      rw [hR2z] at hrsq
      simpa using sub_eq_zero.mp (eq_sub_iff_add_eq.mpr hrsq.symm)
    have hz : z = 0 := by
      have hc : (4 * α^2 : ℝ) ≠ 0 := by
        positivity [sq_pos_of_ne_zero hα]
      simpa [Matrix.smul_mulVec, hc] using hcz
    exact sub_eq_zero.mp hz
  exact hPsem.posDef_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)

lemma gramCandidate_quadratic_identity
    (H : Mat 2 2) (hH : Hᵀ = H) (α : ℝ) (hα : α ≠ 0)
    (R : Mat 2 2)
    (hR : PositiveSquareRoot
      (H * H + (4 * α^2) • (1 : Mat 2 2)) R) :
    (gramCandidate H R - H) * gramCandidate H R =
      α^2 • (1 : Mat 2 2) := by
  have hcomm := positiveSquareRoot_commutes_with_base H hH α hα R hR
  have hleft :
      gramCandidate H R - H = (1 / 2 : ℝ) • (R - H) := by
    unfold gramCandidate
    module
  rw [hleft]
  unfold gramCandidate
  calc
    ((1 / 2 : ℝ) • (R - H)) * ((1 / 2 : ℝ) • (H + R))
        = (1 / 4 : ℝ) • ((R - H) * (H + R)) := by
            simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
            ring
    _ = (1 / 4 : ℝ) • (R * R - H * H) := by
          congr 1
          rw [sub_mul, mul_add, mul_add, hcomm.eq]
          abel
    _ = (1 / 4 : ℝ) • ((4 * α^2) • (1 : Mat 2 2)) := by
          rw [hR.2, add_sub_cancel_left]
    _ = α^2 • (1 : Mat 2 2) := by
          rw [smul_smul]
          ring_nf

lemma gramCandidate_identity_mathlib
    (H : Mat 2 2) (hH : Hᵀ = H) (α : ℝ) (hα : α ≠ 0)
    (R : Mat 2 2)
    (hR : PositiveSquareRoot
      (H * H + (4 * α^2) • (1 : Mat 2 2)) R) :
    gramCandidate H R - α^2 • (gramCandidate H R)⁻¹ = H := by
  let P := gramCandidate H R
  have hPpos : Matrix.PosDef P := by
    dsimp [P]
    exact gramCandidate_posDef_mathlib H hH α hα R hR
  have hPunit : IsUnit P := hPpos.isUnit
  have hquad : (P - H) * P = α^2 • (1 : Mat 2 2) := by
    simpa [P] using gramCandidate_quadratic_identity H hH α hα R hR
  have hright : P - H = α^2 • P⁻¹ := by
    calc
      P - H = (P - H) * 1 := by simp
      _ = (P - H) * (P * P⁻¹) := by simp [hPunit]
      _ = ((P - H) * P) * P⁻¹ := by rw [Matrix.mul_assoc]
      _ = (α^2 • (1 : Mat 2 2)) * P⁻¹ := by rw [hquad]
      _ = α^2 • P⁻¹ := by
            simp [Algebra.smul_mul_assoc]
  dsimp [P] at hright ⊢
  abel

lemma positive_solution_unique_mathlib
    (H : Mat 2 2) (hH : Hᵀ = H) (α : ℝ) (hα : α ≠ 0)
    (P R : Mat 2 2)
    (hP : Matrix.PosDef P)
    (hPeq : P - α^2 • P⁻¹ = H)
    (hR : PositiveSquareRoot
      (H * H + (4 * α^2) • (1 : Mat 2 2)) R) :
    P = gramCandidate H R := by
  let T : Mat 2 2 := (2 : ℝ) • P - H
  have hTform : T = P + α^2 • P⁻¹ := by
    dsimp [T]
    rw [← hPeq]
    module
  have hTpos : Matrix.PosDef T := by
    rw [hTform]
    exact hP.add (hP.inv.smul (sq_pos_of_ne_zero hα))
  have hPunit : IsUnit P := hP.isUnit
  have hPinvL : P⁻¹ * P = (1 : Mat 2 2) := by simp [hPunit]
  have hPinvR : P * P⁻¹ = (1 : Mat 2 2) := by simp [hPunit]
  have hTsq :
      T * T = H * H + (4 * α^2) • (1 : Mat 2 2) := by
    rw [hTform, ← hPeq]
    simp only [add_mul, mul_add, sub_mul, mul_sub,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    rw [hPinvL, hPinvR]
    simp
    ring
  have hA :
      Matrix.PosDef (H * H + (4 * α^2) • (1 : Mat 2 2)) :=
    posDef_sq_add_scalar_one H hH
      (by positivity [sq_pos_of_ne_zero hα])
  have hTroot :
      PositiveSquareRoot
        (H * H + (4 * α^2) • (1 : Mat 2 2)) T :=
    ⟨hTpos, hTsq⟩
  have hTcfc := positiveSquareRoot_eq_cfc hA hTroot
  have hRcfc := positiveSquareRoot_eq_cfc hA hR
  have hTR : T = R := hTcfc.trans hRcfc.symm
  unfold gramCandidate
  rw [← hTR]
  dsimp [T]
  module

/-- The required positive square roots actually exist. -/
theorem lemma29_roots_exist (H₀ : Mat 2 2) (hH : H₀ᵀ = H₀)
    (α : ℝ) (hα : α ≠ 0) :
    ∃ R S : Mat 2 2,
      PositiveSquareRoot (H₀ * H₀ + (4 * α^2) • (1 : Mat 2 2)) R ∧
      PositiveSquareRoot (gramCandidate H₀ R) S := by
  have hA :
      Matrix.PosDef (H₀ * H₀ + (4 * α^2) • (1 : Mat 2 2)) := by
    exact posDef_sq_add_scalar_one H₀ hH
      (by positivity [sq_pos_of_ne_zero hα])
  let R : Mat 2 2 := CFC.sqrt
    (H₀ * H₀ + (4 * α^2) • (1 : Mat 2 2))
  have hRroot :
      PositiveSquareRoot (H₀ * H₀ + (4 * α^2) • (1 : Mat 2 2)) R := by
    exact positiveSquareRoot_cfc hA
  have hRpos := hRroot.1
  have hRsq := hRroot.2
  let P := gramCandidate H₀ R
  have hP : Matrix.PosDef P :=
    gramCandidate_posDef_mathlib H₀ hH α hα R hRroot
  let S : Mat 2 2 := CFC.sqrt P
  have hSroot : PositiveSquareRoot P S :=
    positiveSquareRoot_cfc hP
  exact ⟨R, S, ⟨hRpos, hRsq⟩, hSroot⟩

/-- Lemma 29. Supplying R and S by their unique positive-root properties
expresses the explicit formula without relying on a specific CFC interface. -/
theorem lemma29 (H₀ : Mat 2 2) (hH : H₀ᵀ = H₀)
    (α : ℝ) (hα : α ≠ 0) (R S : Mat 2 2)
    (hR : PositiveSquareRoot (H₀ * H₀ + (4 * α^2) • (1 : Mat 2 2)) R)
    (hS : PositiveSquareRoot (gramCandidate H₀ R) S)
    (U V : Mat 2 2) :
    (Uᵀ * U - Vᵀ * V = H₀ ∧ U * Vᵀ = α • (1 : Mat 2 2)) ↔
      ∃ Q : Mat 2 2, IsOrthogonal Q ∧ U = Q * S ∧ V = α • (Q * S⁻¹) := by
  have hSsymm : Sᵀ = S := hS.1.isHermitian.eq
  have hSinv : IsUnit S := hS.1.isUnit
  have hPformula :
      gramCandidate H₀ R -
          α^2 • (gramCandidate H₀ R)⁻¹ = H₀ :=
    gramCandidate_identity_mathlib H₀ hH α hα R hR
  constructor
  · rintro ⟨hbal, hprod⟩
    have hUunit : IsUnit U :=
      Matrix.isUnit_of_mul_transpose_eq_smul_one hα hprod
    have hVform : V = α • (U⁻¹)ᵀ := by
      exact Matrix.eq_smul_inv_transpose_of_mul_transpose_eq_smul_one
        hα hprod
    let P : Mat 2 2 := Uᵀ * U
    have hPpos : Matrix.PosDef P := by
      have hinj : Function.Injective U.mulVec :=
        Matrix.mulVec_injective_of_isUnit hUunit
      simpa [P, star_eq_transpose] using
        (Matrix.conjTranspose_mul_self U hinj)
    have hPeq : P - α^2 • P⁻¹ = H₀ := by
      rw [P, hVform] at hbal
      simpa [Matrix.transpose_smul, Matrix.transpose_inv,
        Matrix.mul_inv_rev, hUunit] using hbal
    have hPuniq : P = gramCandidate H₀ R :=
      positive_solution_unique_mathlib
        H₀ hH α hα P R hPpos hPeq hR
    have hgram : Uᵀ * U = S * S := by
      rw [← hS.2, ← hPuniq]
      rfl
    let Q : Mat 2 2 := U * S⁻¹
    have hQorth : IsOrthogonal Q := by
      unfold IsOrthogonal Q
      rw [Matrix.transpose_mul, Matrix.transpose_inv, hSsymm,
        Matrix.mul_assoc, ← Matrix.mul_assoc (S⁻¹)ᵀ Uᵀ U]
      rw [hgram]
      simp [hSinv]
    have hU : U = Q * S := by
      simp [Q, Matrix.mul_assoc, hSinv]
    have hV : V = α • (Q * S⁻¹) := by
      rw [hVform, hU]
      simp [Matrix.transpose_mul, hSsymm, hQorth, hSinv,
        Matrix.mul_assoc]
    exact ⟨Q, hQorth, hU, hV⟩
  · rintro ⟨Q, hQ, rfl, rfl⟩
    have hQunit : IsUnit Q := Matrix.isUnit_of_orthogonal hQ
    have hSt : Sᵀ = S := hSsymm
    constructor
    · calc
        (Q * S)ᵀ * (Q * S) -
            (α • (Q * S⁻¹))ᵀ * (α • (Q * S⁻¹))
            = S * S - α^2 • (S * S)⁻¹ := by
                simp [Matrix.transpose_mul, hSt, hQ,
                  Matrix.transpose_smul, Matrix.mul_assoc, hSinv]
        _ = gramCandidate H₀ R -
              α^2 • (gramCandidate H₀ R)⁻¹ := by
                rw [hS.2]
        _ = H₀ := hPformula
    · simp [Matrix.transpose_mul, hSt, hQ, hSinv,
        Matrix.mul_assoc, hα]

/-- The scalar conservation-law equation used in Appendix H.1. -/
theorem scalar_balanced_equation {u v α h₀ : ℝ}
    (hprod : u * v = α) (hbal : u^2 - v^2 = h₀) :
    (u^2)^2 - h₀ * u^2 - α^2 = 0 := by
  calc
    (u^2)^2 - h₀ * u^2 - α^2 =
        u^2 * (u^2 - v^2 - h₀) + ((u * v)^2 - α^2) := by ring
    _ = 0 := by rw [hbal, hprod]; ring

end LearningToScale
end GradientFlowPaper

end -- noncomputable section