import Mathlib

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
