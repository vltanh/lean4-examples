import Lean4Examples.GradientFlowPaper.Geometry

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
