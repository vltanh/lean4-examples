import Lean4Examples.GradientFlowPaper.Core
import Lean4Examples.GradientFlowVendor.TauCeti.Analysis.ODE.InitialCondition

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


namespace LocalFlow

lemma eqOn_domain_inter {v : Field E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ψ φ : LocalFlow Ω v) (p : E) (hp : p ∈ Ω) :
    Set.EqOn (fun t => ψ.toFun t p) (fun t => φ.toFun t p)
      ({t | (t,p) ∈ ψ.domain} ∩ {t | (t,p) ∈ φ.domain}) := by
  let I : Set ℝ :=
    {t | (t,p) ∈ ψ.domain} ∩ {t | (t,p) ∈ φ.domain}
  have hIopen : IsOpen I :=
    (ψ.open_times p).inter (φ.open_times p)
  have hIconv : Convex ℝ I :=
    (ψ.time_convex p hp).inter (φ.time_convex p hp)
  have h0I : (0 : ℝ) ∈ I :=
    ⟨ψ.zero_mem p hp, φ.zero_mem p hp⟩
  apply smooth_ode_solution_unique_on_open_convex
    (Ω := Ω) hIopen hIconv hΩ hv h0I
  · intro t ht
    exact ψ.target_mem ht.1
  · intro t ht
    exact φ.target_mem ht.2
  · intro t ht
    exact ψ.ode ht.1
  · intro t ht
    exact φ.ode ht.2
  · simp [ψ.initial p hp, φ.initial p hp]

noncomputable def union {v : Field E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ψ φ : LocalFlow Ω v) : LocalFlow Ω v := by
  classical
  let D := ψ.domain ∪ φ.domain
  let F : ℝ → E → E := fun t p =>
    if h : (t,p) ∈ ψ.domain then ψ.toFun t p else φ.toFun t p

  have hFψ : ∀ {t p}, (t,p) ∈ ψ.domain → F t p = ψ.toFun t p := by
    intro t p h
    simp [F, h]

  have hFφ : ∀ {t p}, (t,p) ∈ φ.domain → F t p = φ.toFun t p := by
    intro t p hφ
    by_cases hψ : (t,p) ∈ ψ.domain
    · rw [hFψ hψ]
      exact eqOn_domain_inter hΩ hv ψ φ p (φ.source_mem hφ)
        ⟨hψ,hφ⟩
    · simp [F, hψ]

  have hDopen : IsOpen D := ψ.open_domain.union φ.open_domain

  have hsource : ∀ {t p}, (t,p) ∈ D → p ∈ Ω := by
    intro t p h
    rcases h with h | h
    · exact ψ.source_mem h
    · exact φ.source_mem h

  have hzero : ∀ p ∈ Ω, (0,p) ∈ D := by
    intro p hp
    exact Or.inl (ψ.zero_mem p hp)

  have htime : ∀ p ∈ Ω, Convex ℝ {t | (t,p) ∈ D} := by
    intro p hp
    have hψc := ψ.time_convex p hp
    have hφc := φ.time_convex p hp
    have hpre :
        IsPreconnected ({t | (t,p) ∈ ψ.domain} ∪
          {t | (t,p) ∈ φ.domain}) :=
      IsPreconnected.union 0
        (ψ.zero_mem p hp) (φ.zero_mem p hp)
        ((convex_iff_isPreconnected).mp hψc)
        ((convex_iff_isPreconnected).mp hφc)
    apply (convex_iff_isPreconnected).mpr
    simpa [D, Set.mem_union] using hpre

  have hsmooth :
      ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) D := by
    intro z hz
    rcases hz with hzψ | hzφ
    · have heq :
          (fun z : ℝ × E => F z.1 z.2) =ᶠ[𝓝 z]
            (fun z : ℝ × E => ψ.toFun z.1 z.2) := by
        filter_upwards [ψ.open_domain.mem_nhds hzψ] with y hy
        exact hFψ hy
      exact ((ψ.smooth z hzψ).contDiffAt
        (ψ.open_domain.mem_nhds hzψ)).congr_of_eventuallyEq heq
        |>.contDiffWithinAt
    · have heq :
          (fun z : ℝ × E => F z.1 z.2) =ᶠ[𝓝 z]
            (fun z : ℝ × E => φ.toFun z.1 z.2) := by
        filter_upwards [φ.open_domain.mem_nhds hzφ] with y hy
        exact hFφ hy
      exact ((φ.smooth z hzφ).contDiffAt
        (φ.open_domain.mem_nhds hzφ)).congr_of_eventuallyEq heq
        |>.contDiffWithinAt

  have hinitial : ∀ p ∈ Ω, F 0 p = p := by
    intro p hp
    rw [hFψ (ψ.zero_mem p hp)]
    exact ψ.initial p hp

  have htarget : ∀ {t p}, (t,p) ∈ D → F t p ∈ Ω := by
    intro t p h
    rcases h with hψ | hφ
    · rw [hFψ hψ]
      exact ψ.target_mem hψ
    · rw [hFφ hφ]
      exact φ.target_mem hφ

  have hode : ∀ {t p}, (t,p) ∈ D →
      HasDerivAt (fun s => F s p) (v (F t p)) t := by
    intro t p h
    rcases h with hψ | hφ
    · have heq :
          (fun s => F s p) =ᶠ[𝓝 t] (fun s => ψ.toFun s p) := by
        filter_upwards [(ψ.open_times p).mem_nhds hψ] with s hs
        exact hFψ hs
      have hvv : F t p = ψ.toFun t p := hFψ hψ
      simpa [hvv] using (ψ.ode hψ).congr_of_eventuallyEq heq
    · have heq :
          (fun s => F s p) =ᶠ[𝓝 t] (fun s => φ.toFun s p) := by
        filter_upwards [(φ.open_times p).mem_nhds hφ] with s hs
        exact hFφ hs
      have hvv : F t p = φ.toFun t p := hFφ hφ
      simpa [hvv] using (φ.ode hφ).congr_of_eventuallyEq heq

  have hcomp : ∀ {t s p}, (s,p) ∈ D →
      (t,F s p) ∈ D → (t+s,p) ∈ D →
      F (t+s) p = F t (F s p) := by
    intro t s p hsp htq hts
    have hp : p ∈ Ω := hsource hsp
    let q := F s p
    have hq : q ∈ Ω := htarget hsp
    let I : Set ℝ :=
      {u | (s+u,p) ∈ D} ∩ {u | (u,q) ∈ D}
    have hIopen : IsOpen I := by
      exact (hDopen.preimage
        (continuous_const.add continuous_id |>.prodMk continuous_const)).inter
        (hDopen.preimage (continuous_id.prodMk continuous_const))
    have hIconv : Convex ℝ I := by
      have hpconv := htime p hp
      have hqconv := htime q hq
      exact (hpconv.preimage (1 : ℝ →ₗ[ℝ] ℝ) s).inter hqconv
    have h0I : (0:ℝ) ∈ I := by
      exact ⟨by simpa using hsp, hzero q hq⟩
    have htI : t ∈ I := by
      exact ⟨by simpa [add_comm] using hts, htq⟩
    have huniq := smooth_ode_solution_unique_on_open_convex
      (Ω := Ω) hIopen hIconv hΩ hv h0I
      (γ := fun u => F (s+u) p)
      (η := fun u => F u q)
      (fun u hu => htarget hu.1)
      (fun u hu => htarget hu.2)
      (fun u hu => by
        simpa using (hode hu.1).scomp u
          ((hasDerivAt_id u).const_add s))
      (fun u hu => hode hu.2)
      (by simp [q])
    exact huniq t htI

  exact {
    domain := D
    open_domain := hDopen
    source_mem := hsource
    zero_mem := hzero
    time_convex := htime
    toFun := F
    smooth := hsmooth
    initial := hinitial
    target_mem := htarget
    ode := hode
    composition := hcomp }

lemma le_union_left {v : Field E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ψ φ : LocalFlow Ω v) :
    (union hΩ hv ψ φ).Extends ψ := by
  refine ⟨fun z hz => Or.inl hz, ?_⟩
  intro t p h
  simp [union, h]

lemma le_union_right {v : Field E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ψ φ : LocalFlow Ω v) :
    (union hΩ hv ψ φ).Extends φ := by
  refine ⟨fun z hz => Or.inr hz, ?_⟩
  intro t p h
  by_cases hψ : (t,p) ∈ ψ.domain
  · simp [union, hψ]
    exact eqOn_domain_inter hΩ hv ψ φ p (φ.source_mem h)
      ⟨hψ,h⟩
  · simp [union, hψ]

end LocalFlow

lemma smooth_ode_solution_unique_on_open_convex
    {I : Set ℝ} (hIopen : IsOpen I) (hIconv : Convex ℝ I)
    {v : Field E} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {γ η : ℝ → E} {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hγmem : ∀ t ∈ I, γ t ∈ Ω)
    (hηmem : ∀ t ∈ I, η t ∈ Ω)
    (hγ : ∀ t ∈ I, HasDerivAt γ (v (γ t)) t)
    (hη : ∀ t ∈ I, HasDerivAt η (v (η t)) t)
    (heq₀ : γ t₀ = η t₀) :
    Set.EqOn γ η I := by
  let J := {t : ℝ // t ∈ I}
  let S : Set J := {t | γ t.1 = η t.1}
  have hcontγ : ContinuousOn γ I :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hcontη : ContinuousOn η I :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have hγJ : Continuous (fun t : J => γ t.1) :=
      hcontγ.comp_continuous continuous_subtype_val (fun t => t.2)
    have hηJ : Continuous (fun t : J => η t.1) :=
      hcontη.comp_continuous continuous_subtype_val (fun t => t.2)
    exact isClosed_eq hγJ hηJ
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    have hτI : τ.1 ∈ I := τ.2
    have hstate : γ τ.1 ∈ Ω := hγmem τ.1 hτI
    have hvAt : ContDiffAt ℝ 1 v (γ τ.1) :=
      ((hv.of_le (by simp)) _ hstate).contDiffAt (hΩ.mem_nhds hstate)
    obtain ⟨K, U, hU, hKU⟩ := hvAt.exists_lipschitzOnWith
    have hγU : ∀ᶠ s in 𝓝 τ.1, γ s ∈ U := by
      exact (hγ τ.1 hτI).continuousAt.eventually hU
    have hηU : ∀ᶠ s in 𝓝 τ.1, η s ∈ U := by
      have hητ : η τ.1 = γ τ.1 := hτ.symm
      simpa [hητ] using (hη τ.1 hτI).continuousAt.eventually hU
    have htime : I ∈ 𝓝 τ.1 := hIopen.mem_nhds hτI
    have hlip :
        ∀ᶠ s in 𝓝 τ.1,
          LipschitzOnWith K (fun _ : E => v ·) U := by
      exact Filter.Eventually.of_forall (fun _ => hKU)
    have hγev :
        ∀ᶠ s in 𝓝 τ.1,
          HasDerivAt γ ((fun _ : ℝ => v) s (γ s)) s ∧ γ s ∈ U := by
      filter_upwards [htime, hγU] with s hsI hsU
      exact ⟨hγ s hsI, hsU⟩
    have hηev :
        ∀ᶠ s in 𝓝 τ.1,
          HasDerivAt η ((fun _ : ℝ => v) s (η s)) s ∧ η s ∈ U := by
      filter_upwards [htime, hηU] with s hsI hsU
      exact ⟨hη s hsI, hsU⟩
    have hevent : γ =ᶠ[𝓝 τ.1] η :=
      ODE_solution_unique_of_eventually
        (v := fun _ : ℝ => v) (s := fun _ => U)
        hlip hγev hηev hτ
    exact Filter.mem_of_superset
      (nhds_subtype_eq_comap τ.1 I ▸
        Filter.preimage_mem_comap' hevent)
      (by
        intro σ hσ
        exact hσ)
  have hJpre : IsPreconnected (Set.univ : Set J) := by
    letI : PreconnectedSpace J := Subtype.preconnectedSpace hIconv.isPreconnected
    exact isPreconnected_univ
  have hSne : S.Nonempty :=
    ⟨⟨t₀, ht₀⟩, heq₀⟩
  have hSuniv : S = Set.univ := by
    letI : PreconnectedSpace J := Subtype.preconnectedSpace hIconv.isPreconnected
    exact IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSne
  intro t ht
  have : (⟨t, ht⟩ : J) ∈ S := by
    rw [hSuniv]
    trivial
  exact this



/-- Time-dependent version of smooth ODE uniqueness.  Smoothness of the
uncurried field gives a locally uniform Lipschitz constant in the state
variable; connectedness of the time interval propagates local uniqueness. -/
lemma smooth_timeDependent_ode_solution_unique_on_open_convex
    {I : Set ℝ} (hIopen : IsOpen I) (hIconv : Convex ℝ I)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ΩF : Set F} (hΩF : IsOpen ΩF)
    {V : ℝ → F → F}
    (hV : ContDiffOn ℝ 1 (fun z : ℝ × F => V z.1 z.2) (I ×ˢ ΩF))
    {γ η : ℝ → F} {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hγmem : ∀ t ∈ I, γ t ∈ ΩF)
    (hηmem : ∀ t ∈ I, η t ∈ ΩF)
    (hγ : ∀ t ∈ I, HasDerivAt γ (V t (γ t)) t)
    (hη : ∀ t ∈ I, HasDerivAt η (V t (η t)) t)
    (heq₀ : γ t₀ = η t₀) :
    Set.EqOn γ η I := by
  let J := {t : ℝ // t ∈ I}
  let S : Set J := {t | γ t.1 = η t.1}
  have hcontγ : ContinuousOn γ I :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hcontη : ContinuousOn η I :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have hγJ : Continuous (fun t : J => γ t.1) :=
      hcontγ.comp_continuous continuous_subtype_val (fun t => t.2)
    have hηJ : Continuous (fun t : J => η t.1) :=
      hcontη.comp_continuous continuous_subtype_val (fun t => t.2)
    exact isClosed_eq hγJ hηJ
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    have hτI : τ.1 ∈ I := τ.2
    have hx : γ τ.1 ∈ ΩF := hγmem τ.1 hτI
    have hVτ :
        ContDiffAt ℝ 1 (fun z : ℝ × F => V z.1 z.2) (τ.1, γ τ.1) :=
      (hV (τ.1, γ τ.1) ⟨hτI,hx⟩).contDiffAt
        ((hIopen.prod hΩF).mem_nhds ⟨hτI,hx⟩)
    obtain ⟨K, W, hW, hKW⟩ := hVτ.exists_lipschitzOnWith
    obtain ⟨T, X, hT, hX, hprod⟩ :=
      mem_nhds_prod_iff'.mp hW
    have htime : I ∈ 𝓝 τ.1 := hIopen.mem_nhds hτI
    have hγX : ∀ᶠ t in 𝓝 τ.1, γ t ∈ X :=
      (hγ τ.1 hτI).continuousAt.eventually hX
    have hηX : ∀ᶠ t in 𝓝 τ.1, η t ∈ X := by
      have hητ : η τ.1 = γ τ.1 := hτ.symm
      simpa [hητ] using (hη τ.1 hτI).continuousAt.eventually hX
    have hTnhds : T ∈ 𝓝 τ.1 := hT
    have hlip :
        ∀ᶠ t in 𝓝 τ.1, LipschitzOnWith K (V t) X := by
      filter_upwards [hTnhds] with t ht
      exact LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
        have hxy := hKW (hprod ⟨ht,hx⟩) (hprod ⟨ht,hy⟩)
        simpa [Prod.dist_eq, max_self] using hxy
    have hγev :
        ∀ᶠ t in 𝓝 τ.1,
          HasDerivAt γ (V t (γ t)) t ∧ γ t ∈ X := by
      filter_upwards [htime,hγX] with t htI htx
      exact ⟨hγ t htI,htx⟩
    have hηev :
        ∀ᶠ t in 𝓝 τ.1,
          HasDerivAt η (V t (η t)) t ∧ η t ∈ X := by
      filter_upwards [htime,hηX] with t htI htx
      exact ⟨hη t htI,htx⟩
    have hevent : γ =ᶠ[𝓝 τ.1] η :=
      ODE_solution_unique_of_eventually hlip hγev hηev hτ
    exact Filter.mem_of_superset
      (nhds_subtype_eq_comap τ.1 I ▸ Filter.preimage_mem_comap' hevent)
      (by intro σ hσ; exact hσ)
  have hSne : S.Nonempty := ⟨⟨t₀,ht₀⟩,heq₀⟩
  have hSuniv : S = Set.univ := by
    letI : PreconnectedSpace J :=
      Subtype.preconnectedSpace hIconv.isPreconnected
    exact IsClopen.eq_univ ⟨hSclosed,hSopen⟩ hSne
  intro t ht
  have : (⟨t,ht⟩ : J) ∈ S := by rw [hSuniv]; trivial
  exact this

/-- A smooth independent frame evolving by a smooth linear system has
constant span.  This is the precise linear-ODE statement needed in the
rank-induction proof of Frobenius. -/
lemma span_eq_of_smooth_linear_system
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace F]
    {n : ℕ} {I : Set ℝ} (hI : IsOpen I) (hIconv : Convex ℝ I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (a : ℝ → Fin n → F)
    (ha_smooth : ∀ i, ContDiffOn ℝ ∞ (fun t => a t i) I)
    (ha_ind : ∀ t ∈ I, LinearIndependent ℝ (a t))
    (C : ℝ → Fin n → Fin n → ℝ)
    (hC : ∀ i j, ContDiffOn ℝ ∞ (fun t => C t i j) I)
    (ha_ode : ∀ t ∈ I, ∀ i,
      HasDerivAt (fun s => a s i) (∑ j, C t i j • a t j) t) :
    ∀ t ∈ I,
      Submodule.span ℝ (Set.range (a t)) =
        Submodule.span ℝ (Set.range (a t₀)) := by
  classical
  let K := Submodule.span ℝ (Set.range (a t₀))
  let P : F →L[ℝ] Kᗮ := K.orthogonalProjection
  let y : ℝ → Fin n → Kᗮ := fun t i => P (a t i)
  let V : ℝ → (Fin n → Kᗮ) → (Fin n → Kᗮ) :=
    fun t Y i => ∑ j, C t i j • Y j
  have hVsmooth :
      ContDiffOn ℝ 1 (fun z : ℝ × (Fin n → Kᗮ) => V z.1 z.2)
        (I ×ˢ Set.univ) := by
    fun_prop
  have hy :
      ∀ t ∈ I, HasDerivAt
        (fun s => fun i => y s i) (V t (y t)) t := by
    intro t ht
    rw [hasDerivAt_pi]
    intro i
    have hder := (ha_ode t ht i).clm_apply P
    simpa [V,y,map_sum] using hder
  have hy0 : (fun i => y t₀ i) = 0 := by
    funext i
    exact Submodule.orthogonalProjection_mem_subspace_eq_zero
      (Submodule.subset_span ⟨i,rfl⟩)
  have hzero :
      ∀ t ∈ I, HasDerivAt
        (fun _ : ℝ => (0 : Fin n → Kᗮ)) (V t 0) t := by
    intro t ht
    simpa [V] using
      (hasDerivAt_const (x := t) (c := (0 : Fin n → Kᗮ)))
  have hy_eq_zero :
      Set.EqOn (fun t => fun i => y t i) (fun _ => 0) I := by
    exact smooth_timeDependent_ode_solution_unique_on_open_convex
      hI hIconv isOpen_univ hVsmooth ht₀
      (fun _ _ => Set.mem_univ _)
      (fun _ _ => Set.mem_univ _)
      hy hzero hy0
  intro t ht
  have hle :
      Submodule.span ℝ (Set.range (a t)) ≤ K := by
    rw [← Submodule.orthogonal_orthogonal (K := K)]
    apply Submodule.le_orthogonal_of_inner_left
    intro x hx z hz
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,rfl⟩ := hx
        have hproj := congrFun (hy_eq_zero ht) i
        have horth : a t i ∈ Kᗮ := by
          simpa [y,P] using hproj
        exact (Submodule.mem_orthogonal' _ _).mp horth z hz
    | zero => simp
    | add x z hx hz ihx ihz =>
        simp [inner_add_left,ihx,ihz]
    | smul c x hx ih =>
        simp [inner_smul_left,ih]
  apply le_antisymm hle
  have hdimt :
      Module.finrank ℝ (Submodule.span ℝ (Set.range (a t))) = n := by
    simpa using finrank_span_eq_card (ha_ind t ht)
  have hdim0 :
      Module.finrank ℝ K = n := by
    simpa [K] using finrank_span_eq_card (ha_ind t₀ ht₀)
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [hdimt,hdim0]) |>.ge


structure SymmetricFlowPatch (Ω : Set E) (v : Field E) where
  U : Set E
  open_U : IsOpen U
  center : E
  center_mem : center ∈ U
  source_subset : U ⊆ Ω
  ε : ℝ
  ε_pos : 0 < ε
  toFun : E → ℝ → E
  smooth : ContDiffOn ℝ ∞
    (fun z : E × ℝ => toFun z.1 z.2) (U ×ˢ Set.Ioo (-ε) ε)
  initial : ∀ x, toFun x 0 = x
  target_mem : ∀ x ∈ U, ∀ t ∈ Set.Ioo (-ε) ε, toFun x t ∈ Ω
  ode : ∀ x ∈ U, ∀ t ∈ Set.Ioo (-ε) ε,
    HasDerivAt (toFun x) (v (toFun x t)) t
  composition : ∀ x t u, toFun x (t + u) = toFun (toFun x t) u

lemma exists_symmetricFlowPatch (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) {a : E} (ha : a ∈ Ω) :
    ∃ P : SymmetricFlowPatch Ω v, P.center = a := by
  have hv' : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) v Ω := by
    simpa using hv
  obtain ⟨Φ, hΦsmooth, hΦ0, hΦadd, hΦode⟩ :=
    ODE.exists_contDiffAt_localFlow (n := (⊤ : ℕ∞))
      v hv' (hΩ.mem_nhds ha)
  have hΦcont :
      ContinuousAt (fun z : E × ℝ => Φ z.1 z.2) (a,0) :=
    hΦsmooth.continuousAt
  have htargetEv :
      ∀ᶠ z : E × ℝ in 𝓝 (a,0), Φ z.1 z.2 ∈ Ω := by
    have : Φ a 0 = a := hΦ0 a
    exact hΦcont.eventually (this ▸ hΩ.mem_nhds ha)
  obtain ⟨Ws, hWs, hWsmooth⟩ :=
    hΦsmooth.contDiffOn (m := ∞) le_rfl (by simp)
  have hN : Ws ∩ {z | HasDerivAt (Φ z.1) (v (Φ z.1 z.2)) z.2} ∩
      {z | Φ z.1 z.2 ∈ Ω} ∈ 𝓝 (a,0) := by
    exact Filter.inter_mem
      (Filter.inter_mem hWs hΦode) htargetEv
  obtain ⟨U₀, I₀, hU₀, hI₀, hprod⟩ :=
    mem_nhds_prod_iff'.mp hN
  obtain ⟨U, haU, hUopen, hUU₀⟩ := mem_nhds_iff.mp hU₀
  have hUΩn : Ω ∈ 𝓝 a := hΩ.mem_nhds ha
  let U' := U ∩ Ω
  have hU'open : IsOpen U' := hUopen.inter hΩ
  have haU' : a ∈ U' := ⟨haU,ha⟩
  have hU'U₀ : U' ⊆ U₀ := fun x hx => hUU₀ hx.1
  obtain ⟨ε, hε, hIε⟩ := Metric.mem_nhds_iff.mp hI₀
  let J : Set ℝ := Set.Ioo (-ε) ε
  have hJsub : J ⊆ I₀ := by
    intro t ht
    apply hIε
    simpa [J, Real.dist_eq] using max_lt ht.2 (by linarith [ht.1])
  have hprod' : U' ×ˢ J ⊆
      Ws ∩ {z | HasDerivAt (Φ z.1) (v (Φ z.1 z.2)) z.2} ∩
        {z | Φ z.1 z.2 ∈ Ω} := by
    intro z hz
    exact hprod ⟨hU'U₀ hz.1, hJsub hz.2⟩
  refine ⟨{
    U := U'
    open_U := hU'open
    center := a
    center_mem := haU'
    source_subset := inter_subset_right
    ε := ε
    ε_pos := hε
    toFun := Φ
    smooth := ?_
    initial := hΦ0
    target_mem := ?_
    ode := ?_
    composition := hΦadd }, rfl⟩
  · exact hWsmooth.mono (fun z hz => (hprod' hz).1)
  · intro x hx t ht
    exact (hprod' ⟨hx,ht⟩).2.2
  · intro x hx t ht
    exact (hprod' ⟨hx,ht⟩).2.1

lemma SymmetricFlowPatch.eq_on_overlap
    (hΩ : IsOpen Ω) {v : Field E} (hv : ContDiffOn ℝ ∞ v Ω)
    (P Q : SymmetricFlowPatch Ω v) {x : E}
    (hxP : x ∈ P.U) (hxQ : x ∈ Q.U) :
    Set.EqOn (P.toFun x) (Q.toFun x)
      (Set.Ioo (max (-P.ε) (-Q.ε)) (min P.ε Q.ε)) := by
  let I := Set.Ioo (max (-P.ε) (-Q.ε)) (min P.ε Q.ε)
  have hIopen : IsOpen I := isOpen_Ioo
  have hIconv : Convex ℝ I := convex_Ioo _ _
  have h0I : (0 : ℝ) ∈ I := by
    constructor
    · exact max_lt (by linarith [P.ε_pos]) (by linarith [Q.ε_pos])
    · exact lt_min P.ε_pos Q.ε_pos
  apply smooth_ode_solution_unique_on_open_convex
    (Ω := Ω) hIopen hIconv hΩ hv h0I
  · intro t ht
    exact P.target_mem x hxP t
      ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
       lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  · intro t ht
    exact Q.target_mem x hxQ t
      ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
       lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  · intro t ht
    exact P.ode x hxP t
      ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
       lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  · intro t ht
    exact Q.ode x hxQ t
      ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
       lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  · simp [P.initial, Q.initial]


theorem exists_glued_smooth_localFlow
    (hΩ : IsOpen Ω) {v : Field E} (hv : ContDiffOn ℝ ∞ v Ω) :
    ∃ ψ : LocalFlow Ω v, True := by
  classical
  let C := {x : E // x ∈ Ω}
  have hpatch : ∀ a : C, ∃ P : SymmetricFlowPatch Ω v, P.center = a.1 :=
    fun a => exists_symmetricFlowPatch hΩ hv a.2
  choose P hPcenter using hpatch
  have haU : ∀ a : C, a.1 ∈ (P a).U := by
    intro a
    simpa [hPcenter a] using (P a).center_mem

  let D : Set (ℝ × E) :=
    {z | ∃ a : C,
      z.2 ∈ (P a).U ∧ z.1 ∈ Set.Ioo (-(P a).ε) (P a).ε}
  let Value : ℝ × E → E → Prop := fun z y =>
    ∃ a : C, z.2 ∈ (P a).U ∧
      z.1 ∈ Set.Ioo (-(P a).ε) (P a).ε ∧
      y = (P a).toFun z.2 z.1

  have hvalue_unique : ∀ z ∈ D, ∃! y, Value z y := by
    intro z hz
    obtain ⟨a, hxa, hta⟩ := hz
    refine ⟨(P a).toFun z.2 z.1, ⟨a,hxa,hta,rfl⟩, ?_⟩
    intro y hy
    obtain ⟨b,hxb,htb,rfl⟩ := hy
    have hover :=
      SymmetricFlowPatch.eq_on_overlap hΩ hv (P a) (P b) hxa hxb
    have ht :
        z.1 ∈ Set.Ioo
          (max (-(P a).ε) (-(P b).ε))
          (min (P a).ε (P b).ε) := by
      exact ⟨max_lt hta.1 htb.1, lt_min hta.2 htb.2⟩
    exact (hover ht).symm

  noncomputable let F : ℝ × E → E := fun z =>
    if hz : z ∈ D then Classical.choose (hvalue_unique z hz) else z.2

  have hF_patch :
      ∀ {a : C} {t : ℝ} {x : E},
        x ∈ (P a).U →
        t ∈ Set.Ioo (-(P a).ε) (P a).ε →
        F (t,x) = (P a).toFun x t := by
    intro a t x hx ht
    have hz : (t,x) ∈ D := ⟨a,hx,ht⟩
    have hs := Classical.choose_spec (hvalue_unique (t,x) hz)
    rw [show F (t,x) = Classical.choose (hvalue_unique (t,x) hz) by
      simp [F, hz]]
    exact (hvalue_unique (t,x) hz).unique hs ⟨a,hx,ht,rfl⟩

  have hDopen : IsOpen D := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨a,hx,ht⟩ := hz
    let W : Set (ℝ × E) :=
      Set.Ioo (-(P a).ε) (P a).ε ×ˢ (P a).U
    refine ⟨W, ?_, ?_, ?_⟩
    · intro y hy
      exact ⟨a,hy.2,hy.1⟩
    · exact isOpen_Ioo.prod (P a).open_U
    · exact ⟨ht,hx⟩

  have htimeconv : ∀ x ∈ Ω, Convex ℝ {t | (t,x) ∈ D} := by
    intro x hx
    rw [convex_iff_segment_subset]
    intro t ht u hu w hw
    obtain ⟨a,hxa,hta⟩ := ht
    obtain ⟨b,hxb,hub⟩ := hu
    rcases le_total (P a).ε (P b).ε with hab | hba
    · refine ⟨b,hxb, ?_⟩
      apply (convex_Ioo (-(P b).ε) (P b).ε).segment_subset
      · exact ⟨lt_of_lt_of_le hta.1 (neg_le_neg hab),
          lt_of_lt_of_le hta.2 hab⟩
      · exact hub
      · exact hw
    · refine ⟨a,hxa, ?_⟩
      apply (convex_Ioo (-(P a).ε) (P a).ε).segment_subset
      · exact hta
      · exact ⟨lt_of_lt_of_le hub.1 (neg_le_neg hba),
          lt_of_lt_of_le hub.2 hba⟩
      · exact hw

  have hsource : ∀ {t x}, (t,x) ∈ D → x ∈ Ω := by
    intro t x htx
    obtain ⟨a,hxa,-⟩ := htx
    exact (P a).source_subset hxa

  have hzero : ∀ x ∈ Ω, (0,x) ∈ D := by
    intro x hx
    let a : C := ⟨x,hx⟩
    refine ⟨a, haU a, ?_⟩
    exact ⟨by linarith [(P a).ε_pos], (P a).ε_pos⟩

  have htarget : ∀ {t x}, (t,x) ∈ D → F (t,x) ∈ Ω := by
    intro t x htx
    obtain ⟨a,hxa,hta⟩ := htx
    rw [hF_patch hxa hta]
    exact (P a).target_mem x hxa t hta

  have hFzero : ∀ x ∈ Ω, F (0,x) = x := by
    intro x hx
    let a : C := ⟨x,hx⟩
    rw [hF_patch (haU a)
      (show (0:ℝ) ∈ Set.Ioo (-(P a).ε) (P a).ε by
        exact ⟨by linarith [(P a).ε_pos], (P a).ε_pos⟩)]
    exact (P a).initial x

  have hFsmooth :
      ContDiffOn ℝ ∞ (fun z : ℝ × E => F z) D := by
    intro z hz
    obtain ⟨a,hxa,hta⟩ := hz
    let W : Set (ℝ × E) :=
      Set.Ioo (-(P a).ε) (P a).ε ×ˢ (P a).U
    have hWopen : IsOpen W := isOpen_Ioo.prod (P a).open_U
    have hzW : z ∈ W := ⟨hta,hxa⟩
    have hWD : W ⊆ D := by
      intro y hy
      exact ⟨a,hy.2,hy.1⟩
    have hpatchsmooth :
        ContDiffOn ℝ ∞
          (fun y : ℝ × E => (P a).toFun y.2 y.1) W := by
      exact (P a).smooth.comp
        (by fun_prop)
        (fun y hy => ⟨hy.2,hy.1⟩)
    have heq :
        (fun y : ℝ × E => F y) =ᶠ[𝓝 z]
          (fun y : ℝ × E => (P a).toFun y.2 y.1) := by
      filter_upwards [hWopen.mem_nhds hzW] with y hy
      exact hF_patch hy.2 hy.1
    exact ((hpatchsmooth z hzW).contDiffAt (hWopen.mem_nhds hzW))
      |>.congr_of_eventuallyEq heq
      |>.contDiffWithinAt

  have hFode : ∀ {t x}, (t,x) ∈ D →
      HasDerivAt (fun s => F (s,x)) (v (F (t,x))) t := by
    intro t x htx
    obtain ⟨a,hxa,hta⟩ := htx
    have hpatchode := (P a).ode x hxa t hta
    have heq :
        (fun s => F (s,x)) =ᶠ[𝓝 t] (P a).toFun x := by
      have hInhds :
          Set.Ioo (-(P a).ε) (P a).ε ∈ 𝓝 t :=
        isOpen_Ioo.mem_nhds hta
      filter_upwards [hInhds] with s hs
      exact hF_patch hxa hs
    have hval : F (t,x) = (P a).toFun x t :=
      hF_patch hxa hta
    simpa [hval] using hpatchode.congr_of_eventuallyEq heq

  have hFcomp :
      ∀ {t s x}, (s,x) ∈ D →
        (t,F (s,x)) ∈ D → (t+s,x) ∈ D →
        F (t+s,x) = F (t,F (s,x)) := by
    intro t s x hsx htx htsx
    obtain ⟨a,hxa,hsa⟩ := hsx
    obtain ⟨b,hxb,htsb⟩ := htsx
    rcases le_total (P a).ε (P b).ε with hab | hba
    · let R := P b
      have hxR : x ∈ R.U := hxb
      have hsR : s ∈ Set.Ioo (-R.ε) R.ε :=
        ⟨lt_of_lt_of_le hsa.1 (neg_le_neg hab),
         lt_of_lt_of_le hsa.2 hab⟩
      have htsR : t+s ∈ Set.Ioo (-R.ε) R.ε := htsb
      obtain ⟨qpatch,hqU,htq⟩ := htx
      have hqeq : F (s,x) = R.toFun x s := hF_patch hxR hsR
      let I : Set ℝ :=
        {u | s + u ∈ Set.Ioo (-R.ε) R.ε} ∩
          Set.Ioo (-(P qpatch).ε) (P qpatch).ε
      have hIopen : IsOpen I := by
        exact (isOpen_Ioo.preimage (continuous_const.add continuous_id)).inter isOpen_Ioo
      have hIconv : Convex ℝ I := by
        exact ((convex_Ioo (-R.ε) R.ε).preimage
          (1 : ℝ →ₗ[ℝ] ℝ) s).inter
          (convex_Ioo (-(P qpatch).ε) (P qpatch).ε)
      have h0I : (0:ℝ) ∈ I := by
        exact ⟨by simpa using hsR,
          ⟨by linarith [(P qpatch).ε_pos], (P qpatch).ε_pos⟩⟩
      have htI : t ∈ I := by
        exact ⟨by simpa [add_comm] using htsR, htq⟩
      have huniq := smooth_ode_solution_unique_on_open_convex
        (Ω := Ω) hIopen hIconv hΩ hv h0I
        (γ := fun u => R.toFun x (s+u))
        (η := fun u => (P qpatch).toFun (F (s,x)) u)
        (fun u hu => R.target_mem x hxR (s+u) hu.1)
        (fun u hu => (P qpatch).target_mem _ hqU u hu.2)
        (fun u hu => by
          simpa using (R.ode x hxR (s+u) hu.1).scomp u
            ((hasDerivAt_id u).const_add s))
        (fun u hu => (P qpatch).ode _ hqU u hu.2)
        (by
          rw [add_zero, ← hqeq, (P qpatch).initial])
      have heqt := huniq t htI
      rw [hF_patch hxR htsR]
      rw [hF_patch hqU htq]
      exact heqt
    · let R := P a
      have hxR : x ∈ R.U := hxa
      have hsR : s ∈ Set.Ioo (-R.ε) R.ε := hsa
      have htsR : t+s ∈ Set.Ioo (-R.ε) R.ε :=
        ⟨lt_of_lt_of_le htsb.1 (neg_le_neg hba),
         lt_of_lt_of_le htsb.2 hba⟩
      obtain ⟨qpatch,hqU,htq⟩ := htx
      have hqeq : F (s,x) = R.toFun x s := hF_patch hxR hsR
      let I : Set ℝ :=
        {u | s + u ∈ Set.Ioo (-R.ε) R.ε} ∩
          Set.Ioo (-(P qpatch).ε) (P qpatch).ε
      have hIopen : IsOpen I := by
        exact (isOpen_Ioo.preimage (continuous_const.add continuous_id)).inter isOpen_Ioo
      have hIconv : Convex ℝ I := by
        exact ((convex_Ioo (-R.ε) R.ε).preimage
          (1 : ℝ →ₗ[ℝ] ℝ) s).inter
          (convex_Ioo (-(P qpatch).ε) (P qpatch).ε)
      have h0I : (0:ℝ) ∈ I := by
        exact ⟨by simpa using hsR,
          ⟨by linarith [(P qpatch).ε_pos], (P qpatch).ε_pos⟩⟩
      have htI : t ∈ I := by
        exact ⟨by simpa [add_comm] using htsR, htq⟩
      have huniq := smooth_ode_solution_unique_on_open_convex
        (Ω := Ω) hIopen hIconv hΩ hv h0I
        (γ := fun u => R.toFun x (s+u))
        (η := fun u => (P qpatch).toFun (F (s,x)) u)
        (fun u hu => R.target_mem x hxR (s+u) hu.1)
        (fun u hu => (P qpatch).target_mem _ hqU u hu.2)
        (fun u hu => by
          simpa using (R.ode x hxR (s+u) hu.1).scomp u
            ((hasDerivAt_id u).const_add s))
        (fun u hu => (P qpatch).ode _ hqU u hu.2)
        (by
          rw [add_zero, ← hqeq, (P qpatch).initial])
      have heqt := huniq t htI
      rw [hF_patch hxR htsR]
      rw [hF_patch hqU htq]
      exact heqt

  let ψ : LocalFlow Ω v :=
    { domain := D
      open_domain := hDopen
      source_mem := hsource
      zero_mem := hzero
      time_convex := htimeconv
      toFun := fun t x => F (t,x)
      smooth := hFsmooth
      initial := hFzero
      target_mem := htarget
      ode := hFode
      composition := hFcomp }
  exact ⟨ψ, trivial⟩


namespace LocalFlow

theorem exists_common_extension {v : Field E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (C : Set (LocalFlow Ω v)) (hC : C.Nonempty) :
    ∃ Ψ : LocalFlow Ω v, ∀ ψ ∈ C, Ψ.Extends ψ := by
  classical
  let D : Set (ℝ × E) := ⋃ ψ ∈ C, ψ.domain
  let Value : ℝ × E → E → Prop := fun z y =>
    ∃ ψ ∈ C, z ∈ ψ.domain ∧ y = ψ.toFun z.1 z.2
  have hvalue : ∀ z ∈ D, ∃! y, Value z y := by
    intro z hz
    simp only [D, Set.mem_iUnion] at hz
    obtain ⟨ψ, hψC, hzψ⟩ := hz
    refine ⟨ψ.toFun z.1 z.2, ⟨ψ,hψC,hzψ,rfl⟩, ?_⟩
    intro y hy
    obtain ⟨φ,hφC,hzφ,rfl⟩ := hy
    have hp : z.2 ∈ Ω := ψ.source_mem hzψ
    exact (eqOn_domain_inter hΩ hv ψ φ z.2 hp ⟨hzψ,hzφ⟩).symm
  let F : ℝ → E → E := fun t p =>
    if hz : (t,p) ∈ D then Classical.choose (hvalue (t,p) hz) else p
  have hF_eq :
      ∀ {ψ : LocalFlow Ω v}, ψ ∈ C →
      ∀ {t p}, (t,p) ∈ ψ.domain → F t p = ψ.toFun t p := by
    intro ψ hψC t p htp
    have hz : (t,p) ∈ D := by
      simp [D]
      exact ⟨ψ,hψC,htp⟩
    have hs := Classical.choose_spec (hvalue (t,p) hz)
    rw [show F t p = Classical.choose (hvalue (t,p) hz) by simp [F, hz]]
    exact (hvalue (t,p) hz).unique hs ⟨ψ,hψC,htp,rfl⟩
  have hDopen : IsOpen D :=
    isOpen_iUnion fun ψ => isOpen_iUnion fun _ : ψ ∈ C => ψ.open_domain
  have hsource : ∀ {t p}, (t,p) ∈ D → p ∈ Ω := by
    intro t p htp
    simp only [D, Set.mem_iUnion] at htp
    obtain ⟨ψ,hψC,htp⟩ := htp
    exact ψ.source_mem htp
  have hzero : ∀ p ∈ Ω, (0,p) ∈ D := by
    intro p hp
    obtain ⟨ψ,hψC⟩ := hC
    simp [D]
    exact ⟨ψ,hψC,ψ.zero_mem p hp⟩
  have htime : ∀ p ∈ Ω, Convex ℝ {t | (t,p) ∈ D} := by
    intro p hp
    let fam : Set (Set ℝ) :=
      {I | ∃ ψ ∈ C, I = {t : ℝ | (t,p) ∈ ψ.domain}}
    have hcommon : ∀ I ∈ fam, (0:ℝ) ∈ I := by
      intro I hI
      obtain ⟨ψ,hψC,rfl⟩ := hI
      exact ψ.zero_mem p hp
    have hpre : ∀ I ∈ fam, IsPreconnected I := by
      intro I hI
      obtain ⟨ψ,hψC,rfl⟩ := hI
      exact (convex_iff_isPreconnected).mp (ψ.time_convex p hp)
    have hsun : IsPreconnected (⋃₀ fam) :=
      isPreconnected_sUnion 0 fam hcommon hpre
    apply (convex_iff_isPreconnected).mpr
    simpa [fam, D] using hsun
  have hsmooth : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) D := by
    intro z hz
    simp only [D, Set.mem_iUnion] at hz
    obtain ⟨ψ,hψC,hzψ⟩ := hz
    have heq :
        (fun y : ℝ × E => F y.1 y.2) =ᶠ[𝓝 z]
          (fun y : ℝ × E => ψ.toFun y.1 y.2) := by
      filter_upwards [ψ.open_domain.mem_nhds hzψ] with y hy
      exact hF_eq hψC hy
    exact ((ψ.smooth z hzψ).contDiffAt
      (ψ.open_domain.mem_nhds hzψ)).congr_of_eventuallyEq heq
      |>.contDiffWithinAt
  have hinitial : ∀ p ∈ Ω, F 0 p = p := by
    intro p hp
    obtain ⟨ψ,hψC⟩ := hC
    rw [hF_eq hψC (ψ.zero_mem p hp)]
    exact ψ.initial p hp
  have htarget : ∀ {t p}, (t,p) ∈ D → F t p ∈ Ω := by
    intro t p htp
    simp only [D, Set.mem_iUnion] at htp
    obtain ⟨ψ,hψC,htp⟩ := htp
    rw [hF_eq hψC htp]
    exact ψ.target_mem htp
  have hode : ∀ {t p}, (t,p) ∈ D →
      HasDerivAt (fun s => F s p) (v (F t p)) t := by
    intro t p htp
    simp only [D, Set.mem_iUnion] at htp
    obtain ⟨ψ,hψC,htp⟩ := htp
    have heq : (fun s => F s p) =ᶠ[𝓝 t] (fun s => ψ.toFun s p) := by
      filter_upwards [(ψ.open_times p).mem_nhds htp] with s hs
      exact hF_eq hψC hs
    have hval : F t p = ψ.toFun t p := hF_eq hψC htp
    simpa [hval] using (ψ.ode htp).congr_of_eventuallyEq heq
  have hcomp : ∀ {t s p}, (s,p) ∈ D →
      (t,F s p) ∈ D → (t+s,p) ∈ D →
      F (t+s) p = F t (F s p) := by
    intro t s p hsp htq hts
    have hp : p ∈ Ω := hsource hsp
    let q := F s p
    have hq : q ∈ Ω := htarget hsp
    let I : Set ℝ := {u | (s+u,p) ∈ D} ∩ {u | (u,q) ∈ D}
    have hIopen : IsOpen I := by
      exact (hDopen.preimage
        (continuous_const.add continuous_id |>.prodMk continuous_const)).inter
        (hDopen.preimage (continuous_id.prodMk continuous_const))
    have hIconv : Convex ℝ I := by
      exact ((htime p hp).preimage (1 : ℝ →ₗ[ℝ] ℝ) s).inter (htime q hq)
    have h0I : (0:ℝ) ∈ I := ⟨by simpa using hsp, hzero q hq⟩
    have htI : t ∈ I := ⟨by simpa [add_comm] using hts, htq⟩
    have huniq := smooth_ode_solution_unique_on_open_convex
      (Ω := Ω) hIopen hIconv hΩ hv h0I
      (γ := fun u => F (s+u) p) (η := fun u => F u q)
      (fun u hu => htarget hu.1) (fun u hu => htarget hu.2)
      (fun u hu => by
        simpa using (hode hu.1).scomp u ((hasDerivAt_id u).const_add s))
      (fun u hu => hode hu.2) (by simp [q])
    exact huniq t htI
  let Ψ : LocalFlow Ω v :=
    { domain := D, open_domain := hDopen, source_mem := hsource,
      zero_mem := hzero, time_convex := htime, toFun := F, smooth := hsmooth,
      initial := hinitial, target_mem := htarget, ode := hode, composition := hcomp }
  refine ⟨Ψ, ?_⟩
  intro ψ hψC
  refine ⟨?_, ?_⟩
  · intro z hz
    simp [Ψ, D]
    exact ⟨ψ,hψC,hz⟩
  · intro t p htp
    exact hF_eq hψC htp

end LocalFlow

/-- Maximal smooth local flow.  All local flows have a common extension,
so extending the nonempty family of every local flow gives a maximal one. -/
theorem exists_maximal_localFlow (hΩ : IsOpen Ω) {v : Field E}
    (hv : ContDiffOn ℝ ∞ v Ω) :
    ∃ ψ : LocalFlow Ω v, ψ.IsMaximal := by
  obtain ⟨ψ₀, -⟩ := exists_glued_smooth_localFlow hΩ hv
  let C : Set (LocalFlow Ω v) := Set.univ
  have hC : C.Nonempty := ⟨ψ₀, Set.mem_univ _⟩
  obtain ⟨Ψ, hΨ⟩ :=
    LocalFlow.exists_common_extension hΩ hv C hC
  refine ⟨Ψ, ?_⟩
  intro φ
  exact hΨ φ (Set.mem_univ φ)

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
theorem proposition9
    {L : S → E → ℝ} (hL : RegularLossOn Ω L)
    {v : Field E} (hv : ContDiffOn ℝ ∞ v Ω)
    (hvorth : ∀ p ∈ Ω, v p ∈ symmetryDistribution L p) :
    ∃ ψ : LocalFlow Ω v, ψ.IsMaximal ∧ IsLossSymmetry L ψ := by
  obtain ⟨ψ, hmax⟩ := exists_maximal_localFlow hL.isOpen hv
  exact ⟨ψ, hmax, (corollary7 hL ψ).mpr hvorth⟩

/-- Proposition 25 packages the partial-symmetry extensions of Propositions
24 and 9 exactly as in Appendix E.6. -/
theorem proposition25
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

lemma oneParameterProduct_append {s : ℕ} (φ : Fin s → ℝ → Γ)
    (xs ys : List (Fin s × ℝ)) :
    oneParameterProduct φ (xs ++ ys) =
      oneParameterProduct φ ys * oneParameterProduct φ xs := by
  induction xs with
  | nil =>
      simp [oneParameterProduct]
  | cons z zs ih =>
      simp [oneParameterProduct, ih, mul_assoc]



def orderedOneParameterProduct
    {s : ℕ} (φ : Fin s → ℝ → Γ) :
    List (Fin s) → (Fin s → ℝ) → Γ
  | [], _ => 1
  | i :: is, x => orderedOneParameterProduct φ is x * φ i (x i)

def orderedProductMap {s : ℕ} (φ : Fin s → ℝ → Γ)
    (x : Fin s → ℝ) : Γ :=
  orderedOneParameterProduct φ (List.ofFn id) x

lemma orderedOneParameterProduct_zero
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) :
    ∀ is : List (Fin s),
      orderedOneParameterProduct φ is 0 = 1 := by
  intro is
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp [orderedOneParameterProduct, ih, (hφ i).1]

lemma orderedProductMap_zero
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) :
    orderedProductMap φ 0 = 1 := by
  exact orderedOneParameterProduct_zero φ hφ _

lemma orderedOneParameterProduct_contMDiff
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) :
    ∀ is : List (Fin s),
      ContMDiff (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) ∞
        (orderedOneParameterProduct φ is) := by
  intro is
  induction is with
  | nil =>
      simpa [orderedOneParameterProduct] using
        (contMDiff_const :
          ContMDiff (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) ∞
            (fun _ : Fin s → ℝ => (1 : Γ)))
  | cons i is ih =>
      have hcoord :
          ContMDiff (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, ℝ)) ∞
            (fun x : Fin s → ℝ => x i) := by
        rw [contMDiff_iff_contDiff]
        fun_prop
      have hφi :
          ContMDiff (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) ∞
            (fun x => φ i (x i)) :=
        (hφ i).2.2.comp _ hcoord
      simpa [orderedOneParameterProduct] using ih.mul hφi

lemma orderedProductMap_contMDiff
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) :
    ContMDiff (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) ∞
      (orderedProductMap φ) :=
  orderedOneParameterProduct_contMDiff φ hφ _

def generatorSynthesis {s : ℕ} (φ : Fin s → ℝ → Γ) :
    (Fin s → ℝ) →ₗ[ℝ] TangentSpace (𝓘(ℝ, A)) (1 : Γ) where
  toFun x := ∑ i, x i •
    InfinitesimalGenerator (A := A) (Γ := Γ) (φ i)
  map_add' := by
    intro x y
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    simp [mul_smul, Finset.smul_sum]

lemma generatorSynthesis_apply {s : ℕ}
    (φ : Fin s → ℝ → Γ) (x : Fin s → ℝ) :
    generatorSynthesis (A := A) (Γ := Γ) φ x =
      ∑ i, x i • InfinitesimalGenerator (A := A) (Γ := Γ) (φ i) :=
  rfl

lemma mfderiv_orderedOneParameterProduct_zero
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) :
    ∀ is : List (Fin s), ∀ u : Fin s → ℝ,
      mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A))
        (orderedOneParameterProduct φ is) 0 u =
        (is.map (fun i => u i •
          InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))).sum := by
  intro is
  induction is with
  | nil =>
      intro u
      simp [orderedOneParameterProduct, mfderiv_const]
  | cons i is ih =>
      intro u
      let f₁ := orderedOneParameterProduct φ is
      let f₂ : (Fin s → ℝ) → Γ := fun x => φ i (x i)
      have hf₁ :
          MDiffAt (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₁ 0 :=
        (orderedOneParameterProduct_contMDiff φ hφ is)
          |>.mdifferentiableAt (by simp)
      have hcoord :
          MDiffAt (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, ℝ))
            (fun x : Fin s → ℝ => x i) 0 := by
        rw [mdifferentiableAt_iff_differentiableAt]
        fun_prop
      have hf₂ :
          MDiffAt (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₂ 0 :=
        ((hφ i).2.2.mdifferentiableAt (by simp)).comp 0 hcoord
      have hz₁ : f₁ 0 = 1 :=
        orderedOneParameterProduct_zero φ hφ is
      have hz₂ : f₂ 0 = 1 := by
        simp [f₂, (hφ i).1]
      have hmul :
          MDiffAt (𝓘(ℝ, A).prod 𝓘(ℝ, A)) (𝓘(ℝ, A))
            (fun z : Γ × Γ => z.1 * z.2) (1,1) :=
        (contMDiff_mul (𝓘(ℝ, A)) ∞).mdifferentiableAt (by simp)
      have hpair :
          mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A).prod 𝓘(ℝ, A))
            (fun x => (f₁ x, f₂ x)) 0 u =
            (mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₁ 0 u,
             mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₂ 0 u) := by
        simp [mfderiv_prod]
      have hprod := mfderiv_comp
        (I := 𝓘(ℝ, Fin s → ℝ))
        (I' := 𝓘(ℝ, A).prod 𝓘(ℝ, A))
        (I'' := 𝓘(ℝ, A)) 0 hmul (hf₁.prod hf₂)
      have hmuladd :
          mfderiv (𝓘(ℝ, A).prod 𝓘(ℝ, A)) (𝓘(ℝ, A))
            (fun z : Γ × Γ => z.1 * z.2) (1,1)
            (mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₁ 0 u,
             mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₂ 0 u)
          =
          mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₁ 0 u +
          mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₂ 0 u := by
        rw [mfderiv_prod_eq_add_apply hmul]
        simp [hz₁, hz₂, mfderiv_id]
      have hφcoord :
          mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) f₂ 0 u =
            u i • InfinitesimalGenerator (A := A) (Γ := Γ) (φ i) := by
        have hchain := mfderiv_comp
          (I := 𝓘(ℝ, Fin s → ℝ)) (I' := 𝓘(ℝ, ℝ))
          (I'' := 𝓘(ℝ, A)) 0
          ((hφ i).2.2.mdifferentiableAt (by simp)) hcoord
        have hcoordDer :
            mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, ℝ))
              (fun x : Fin s → ℝ => x i) 0 u = u i := by
          simpa [mfderiv_eq_fderiv] using
            (ContinuousLinearMap.apply ℝ (Fin s → ℝ) i).hasFDerivAt.fderiv_apply u
        rw [hchain, hcoordDer, ContinuousLinearMap.comp_apply]
        change
          (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, A)) (φ i) 0) (u i) =
            u i •
              (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, A)) (φ i) 0) 1
        simpa using
          (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, A)) (φ i) 0).map_smul
            (u i) (1 : ℝ)
      rw [show orderedOneParameterProduct φ (i::is) =
        fun x => f₁ x * f₂ x by rfl]
      rw [hprod, hpair, hmuladd, ih u, hφcoord]
      simp

lemma mfderiv_orderedProductMap_zero
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i))
    (u : Fin s → ℝ) :
    mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A))
      (orderedProductMap φ) 0 u =
      generatorSynthesis (A := A) (Γ := Γ) φ u := by
  rw [orderedProductMap,
    mfderiv_orderedOneParameterProduct_zero φ hφ]
  simp [generatorSynthesis, List.sum_ofFn]


lemma generatorSynthesis_ker_eq_bot
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hind : LinearIndependent ℝ
      (fun i => InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) :
    LinearMap.ker (generatorSynthesis (A := A) (Γ := Γ) φ) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  have hzero :
      ∑ i, (x i - y i) •
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i) = 0 := by
    have := sub_eq_zero.mpr hxy
    simpa [generatorSynthesis, Finset.sum_sub_distrib, sub_smul] using this
  have hc := Fintype.linearIndependent_iff.mp hind
    (fun i => x i - y i) hzero
  ext i
  have := hc i
  linarith

lemma generatorSynthesis_range_eq_top
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hspan : Submodule.span ℝ
      (Set.range (fun i =>
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) = ⊤) :
    LinearMap.range (generatorSynthesis (A := A) (Γ := Γ) φ) = ⊤ := by
  rw [← hspan]
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact (Submodule.span ℝ
      (Set.range (fun i =>
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i)))).sum_mem
      (fun i _ =>
        (Submodule.span ℝ
          (Set.range (fun i =>
            InfinitesimalGenerator (A := A) (Γ := Γ) (φ i)))).smul_mem _
          (Submodule.subset_span ⟨i,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [generatorSynthesis]

def generatorSynthesisEquiv
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hind : LinearIndependent ℝ
      (fun i => InfinitesimalGenerator (A := A) (Γ := Γ) (φ i)))
    (hspan : Submodule.span ℝ
      (Set.range (fun i =>
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) = ⊤) :
    (Fin s → ℝ) ≃L[ℝ] TangentSpace (𝓘(ℝ, A)) (1 : Γ) :=
  ContinuousLinearEquiv.ofBijective
    (generatorSynthesis (A := A) (Γ := Γ) φ).toContinuousLinearMap
    (generatorSynthesis_ker_eq_bot φ hind)
    (generatorSynthesis_range_eq_top φ hspan)

lemma orderedProductMap_mem_generated
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (x : Fin s → ℝ) :
    orderedProductMap φ x ∈
      Subgroup.closure
        (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)) := by
  unfold orderedProductMap
  generalize hlist : List.ofFn id = is
  induction is with
  | nil => simp [orderedOneParameterProduct]
  | cons i is ih =>
      simp only [orderedOneParameterProduct]
      exact (Subgroup.closure _).mul_mem ih
        (Subgroup.subset_closure ⟨(i,x i),rfl⟩)

lemma oneParameter_inv
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i))
    (i : Fin s) (t : ℝ) :
    (φ i t)⁻¹ = φ i (-t) := by
  have hmul := (hφ i).2.1 t (-t)
  rw [add_neg_cancel, (hφ i).1] at hmul
  exact inv_eq_of_mul_right_eq_one hmul

lemma generated_mem_products
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i)) :
    ∀ g ∈ Subgroup.closure
      (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)),
      ∃ xs : List (Fin s × ℝ), oneParameterProduct φ xs = g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨⟨i,t⟩,rfl⟩ := hg
      exact ⟨[(i,t)], by simp [oneParameterProduct]⟩
  | one =>
      exact ⟨[],rfl⟩
  | mul g h hg hh ihg ihh =>
      obtain ⟨xs,hxs⟩ := ihg
      obtain ⟨ys,hys⟩ := ihh
      refine ⟨ys ++ xs, ?_⟩
      rw [oneParameterProduct_append, hxs, hys]
  | inv g hg ih =>
      obtain ⟨xs,hxs⟩ := ih
      let ys := (xs.map fun z => (z.1, -z.2)).reverse
      refine ⟨ys, ?_⟩
      rw [← hxs]
      induction xs with
      | nil => simp [ys, oneParameterProduct]
      | cons z zs ih =>
          simp [ys, oneParameterProduct, ih, oneParameter_inv φ hφ]

lemma generated_eq_top_of_identity_neighborhood
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i))
    (hnhds : ∃ U : Set Γ, IsOpen U ∧ (1 : Γ) ∈ U ∧
      U ⊆ Subgroup.closure
        (Set.range (fun z : Fin s × ℝ => φ z.1 z.2))) :
    Subgroup.closure
      (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)) = ⊤ := by
  let H := Subgroup.closure
    (Set.range (fun z : Fin s × ℝ => φ z.1 z.2))
  obtain ⟨U,hU,h1U,hUH⟩ := hnhds
  have hHnhds : (H : Set Γ) ∈ 𝓝 (1 : Γ) :=
    Filter.mem_of_superset (hU.mem_nhds h1U) hUH
  have hHopen : IsOpen (H : Set Γ) :=
    Subgroup.isOpen_of_mem_nhds H hHnhds
  have hHclosed : IsClosed (H : Set Γ) :=
    H.isClosed_of_isOpen hHopen
  have hclopen : IsClopen (H : Set Γ) := ⟨hHclosed,hHopen⟩
  have hHuniv : (H : Set Γ) = Set.univ := by
    exact hclopen.eq_univ (one_mem H)
  ext g
  simp [H, hHuniv]


lemma orderedProductMap_identity_neighborhood
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i))
    (hind : LinearIndependent ℝ
      (fun i => InfinitesimalGenerator (A := A) (Γ := Γ) (φ i)))
    (hspan : Submodule.span ℝ
      (Set.range (fun i =>
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) = ⊤) :
    ∃ U : Set Γ, IsOpen U ∧ (1 : Γ) ∈ U ∧
      U ⊆ Subgroup.closure
        (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)) := by
  let IΓ := 𝓘(ℝ, A)
  let chart := extChartAt IΓ (1 : Γ)
  let P := orderedProductMap φ
  let F : (Fin s → ℝ) → A := fun x => chart (P x)

  have hP0 : P 0 = 1 :=
    orderedProductMap_zero φ hφ
  have hPMD :
      ContMDiff (𝓘(ℝ, Fin s → ℝ)) IΓ ∞ P :=
    orderedProductMap_contMDiff φ hφ
  have hPdiff :
      MDiffAt (𝓘(ℝ, Fin s → ℝ)) IΓ P 0 :=
    hPMD.mdifferentiableAt (by simp)
  have hchartSrc : (1 : Γ) ∈ chart.source :=
    mem_extChartAt_source _
  have hchartMD :
      MDiffAt IΓ (𝓘(ℝ, A)) chart (1 : Γ) :=
    mdifferentiableAt_extChartAt hchartSrc
  have hFMD :
      MDiffAt (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) F 0 := by
    simpa [F, chart, P, hP0] using hchartMD.comp 0 hPdiff
  have hFcd : ContDiffAt ℝ ∞ F 0 := by
    simpa [contMDiffAt_iff_contDiffAt] using
      (hFMD.contMDiffAt (by simp))

  let L :=
    generatorSynthesisEquiv (A := A) (Γ := Γ) φ hind hspan
  have hchartInv :
      (mfderiv IΓ (𝓘(ℝ, A)) chart (1 : Γ)).IsInvertible :=
    isInvertible_mfderiv_extChartAt hchartSrc
  let Cchart :
      TangentSpace IΓ (1 : Γ) ≃L[ℝ] A :=
    ContinuousLinearEquiv.ofBijective
      (mfderiv IΓ (𝓘(ℝ, A)) chart (1 : Γ))
      (LinearMap.ker_eq_bot.mpr hchartInv.bijective.1)
      (LinearMap.range_eq_top.mpr hchartInv.bijective.2)
  let D : (Fin s → ℝ) ≃L[ℝ] A := L.trans Cchart

  have hPder :
      mfderiv (𝓘(ℝ, Fin s → ℝ)) IΓ P 0 =
        L.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro u
    simpa [L, P, generatorSynthesisEquiv] using
      mfderiv_orderedProductMap_zero
        (A := A) (Γ := Γ) φ hφ u
  have hchain :=
    mfderiv_comp
      (I := 𝓘(ℝ, Fin s → ℝ)) (I' := IΓ)
      (I'' := 𝓘(ℝ, A)) 0 hchartMD hPdiff
  have hFderEq :
      fderiv ℝ F 0 = D.toContinuousLinearMap := by
    have hmf :
        mfderiv (𝓘(ℝ, Fin s → ℝ)) (𝓘(ℝ, A)) F 0 =
          D.toContinuousLinearMap := by
      rw [show F = chart ∘ P by rfl, hchain, hPder]
      rfl
    simpa [mfderiv_eq_fderiv] using hmf
  have hFder :
      HasFDerivAt F D.toContinuousLinearMap 0 := by
    have hd := hFcd.differentiableAt (by simp)
    simpa [hFderEq] using hd.hasFDerivAt

  let R : OpenPartialHomeomorph (Fin s → ℝ) A :=
    hFcd.toOpenPartialHomeomorph F hFder (by simp)
  have h0R : (0 : Fin s → ℝ) ∈ R.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hFcd hFder (by simp)

  let V : Set (Fin s → ℝ) :=
    R.source ∩ P ⁻¹' chart.source
  have hVopen : IsOpen V :=
    R.open_source.inter
      (chart.open_source.preimage hPMD.continuous)
  have h0V : (0 : Fin s → ℝ) ∈ V := by
    exact ⟨h0R, by simpa [P,hP0] using hchartSrc⟩
  have hVR : V ⊆ R.source := inter_subset_left

  let T : Set A := R '' V
  have hTopen : IsOpen T :=
    R.isOpen_image_of_subset_source hVopen hVR
  have hF0T : F 0 ∈ T :=
    ⟨0,h0V,rfl⟩
  have hTchart : T ⊆ chart.target := by
    rintro y ⟨x,hxV,rfl⟩
    have hxChart : P x ∈ chart.source := hxV.2
    have hRfun : R x = F x := rfl
    change F x ∈ chart.target
    simpa [F] using chart.map_source hxChart

  let U : Set Γ := chart.symm '' T
  have hUopen : IsOpen U :=
    chart.symm.isOpen_image_of_subset_source hTopen hTchart
  have h1U : (1 : Γ) ∈ U := by
    refine ⟨F 0,hF0T, ?_⟩
    change chart.symm (chart (P 0)) = 1
    rw [hP0]
    exact chart.left_inv hchartSrc
  have hUH :
      U ⊆ Subgroup.closure
        (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)) := by
    rintro g ⟨y,hyT,rfl⟩
    obtain ⟨x,hxV,hxy⟩ := hyT
    have hxChart : P x ∈ chart.source := hxV.2
    have hRapply : R x = F x := rfl
    have hxyF : y = F x := hxy
    rw [hxyF]
    change chart.symm (chart (P x)) ∈ _
    rw [chart.left_inv hxChart]
    exact orderedProductMap_mem_generated φ x
  exact ⟨U,hUopen,h1U,hUH⟩


lemma exists_generator_basis_subfamily
    {s : ℕ} (X : Fin s → TangentSpace (𝓘(ℝ, A)) (1 : Γ))
    (hspan : Submodule.span ℝ (Set.range X) = ⊤) :
    ∃ (k : ℕ) (e : Fin k ↪ Fin s),
      LinearIndependent ℝ (fun i => X (e i)) ∧
      Submodule.span ℝ (Set.range (fun i => X (e i))) = ⊤ := by
  classical
  let good : Finset (Fin s) → Prop :=
    fun T => LinearIndependent ℝ (fun i : {j // j ∈ T} => X i.1)
  let candidates := Finset.univ.filter good
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [good] using linearIndependent_empty_type
  let T := candidates.max' hnonempty (fun U => U.card)
  have hTgood : good T := (Finset.mem_filter.mp (candidates.max'_mem _ _)).2
  have hTmax :
      ∀ U : Finset (Fin s), good U → T.card ≤ U.card := by
    intro U hU
    have hUc : U ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩
    exact Finset.le_max'_of_mem candidates (fun V => V.card) U hUc
  have hTspan :
      Submodule.span ℝ (X '' (T : Set (Fin s))) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    by_contra hi
    have hXi :
        X i ∉ Submodule.span ℝ (X '' (T : Set (Fin s))) := by
      simpa using hi
    let U := insert i T
    have hiT : i ∉ T := by
      intro hit
      apply hXi
      exact Submodule.subset_span ⟨i, hit, rfl⟩
    have hUgood : good U := by
      rw [good]
      exact hTgood.insert
        (by
          simpa [Set.range_subtype, U] using hXi)
    have hcard : T.card < U.card := by
      simp [U, hiT]
    exact (not_lt_of_ge (hTmax U hUgood)) hcard
  let k := T.card
  let eqv : Fin k ≃ {j // j ∈ T} := (Fintype.equivFin _).symm
  let e : Fin k ↪ Fin s :=
    ⟨fun i => (eqv i).1, fun i j hij =>
      eqv.injective (Subtype.ext hij)⟩
  refine ⟨k,e,?_,?_⟩
  · simpa [e] using hTgood.comp eqv.injective
  · rw [← hTspan]
    congr 1
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e i, ⟨i,rfl⟩, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      let j : {j // j ∈ T} := ⟨i,hi⟩
      exact ⟨eqv.symm j, rfl⟩

/-- Theorem 22: if the infinitesimal generators of finitely many
one-parameter subgroups span the Lie algebra of a connected Lie group, finite
products of those one-parameter subgroups generate the group. -/
theorem theorem22
    {s : ℕ} (φ : Fin s → ℝ → Γ)
    (hφ : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ i))
    (hspan : Submodule.span ℝ
      (Set.range (fun i =>
        InfinitesimalGenerator (A := A) (Γ := Γ) (φ i))) = ⊤) :
    ProductsGenerate φ := by
  let X : Fin s → TangentSpace (𝓘(ℝ, A)) (1 : Γ) :=
    fun i => InfinitesimalGenerator (A := A) (Γ := Γ) (φ i)
  obtain ⟨k,e,hind,hspan'⟩ :=
    exists_generator_basis_subfamily (A := A) (Γ := Γ) X (by simpa [X] using hspan)
  let φ' : Fin k → ℝ → Γ := fun i => φ (e i)
  have hφ' : ∀ i, IsOneParameterSubgroup (A := A) (Γ := Γ) (φ' i) :=
    fun i => hφ (e i)
  have hind' :
      LinearIndependent ℝ
        (fun i => InfinitesimalGenerator (A := A) (Γ := Γ) (φ' i)) := by
    simpa [φ',X] using hind
  have hspan'' :
      Submodule.span ℝ
        (Set.range (fun i =>
          InfinitesimalGenerator (A := A) (Γ := Γ) (φ' i))) = ⊤ := by
    simpa [φ',X] using hspan'
  obtain ⟨U,hU,h1U,hUsmall⟩ :=
    orderedProductMap_identity_neighborhood
      (A := A) (Γ := Γ) φ' hφ' hind' hspan''
  have hrange :
      Set.range (fun z : Fin k × ℝ => φ' z.1 z.2) ⊆
        Set.range (fun z : Fin s × ℝ => φ z.1 z.2) := by
    rintro _ ⟨⟨i,t⟩,rfl⟩
    exact ⟨(e i,t),rfl⟩
  have hclosure :
      Subgroup.closure
        (Set.range (fun z : Fin k × ℝ => φ' z.1 z.2)) ≤
      Subgroup.closure
        (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)) :=
    Subgroup.closure_mono hrange
  have hnhds :
      ∃ U : Set Γ, IsOpen U ∧ (1 : Γ) ∈ U ∧
        U ⊆ Subgroup.closure
          (Set.range (fun z : Fin s × ℝ => φ z.1 z.2)) :=
    ⟨U,hU,h1U,fun g hg => hclosure (hUsmall hg)⟩
  have htop :=
    generated_eq_top_of_identity_neighborhood
      (A := A) (Γ := Γ) φ hφ hnhds
  intro g
  apply generated_mem_products φ hφ g
  rw [htop]
  exact Subgroup.mem_top g

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
theorem corollary10_forward
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
theorem proposition8_local
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
theorem proposition8_star
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

/-- A local smooth frame of a constant-rank distribution can be
reindexed so that its index type is exactly `Fin r`. -/
lemma HasLocalSmoothFrame.exists_rank_frame
    {D : Distribution E} {r : ℕ}
    (hframe : HasLocalSmoothFrame Ω D)
    (hrank : ConstantRankOn Ω D r)
    {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (v : Fin r → Field E),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∀ i, ContDiffOn ℝ ∞ (v i) U) ∧
      (∀ q ∈ U,
        LinearIndependent ℝ (fun i => v i q) ∧
        D q = Submodule.span ℝ (Set.range (fun i => v i q))) := by
  obtain ⟨U, hU, hpU, hUΩ, n, v, hv, hvframe⟩ := hframe p hp
  have hnr : n = r := by
    have hdim :
        Module.finrank ℝ (D p) = n := by
      rw [(hvframe p hpU).2]
      simpa using finrank_span_eq_card (hvframe p hpU).1
    exact hdim.symm.trans (hrank p hp)
  let e : Fin r ≃ Fin n := (finCongr hnr).symm
  let w : Fin r → Field E := fun i => v (e i)
  refine ⟨U, w, hU, hpU, hUΩ, ?_, ?_⟩
  · intro i
    exact hv (e i)
  · intro q hq
    have hind := (hvframe q hq).1.comp e e.injective
    have hspan :
        Submodule.span ℝ (Set.range (fun i : Fin r => w i q)) =
          Submodule.span ℝ (Set.range (fun i : Fin n => v i q)) := by
      simpa [w, Function.comp_def, Set.range_comp] using
        congrArg (Submodule.span ℝ) e.surjective.range_comp
    refine ⟨hind, ?_⟩
    rw [(hvframe q hq).2, ← hspan]

/-- The canonical splitting determined by a nonzero vector: the first
coordinate is the component along the vector and the second coordinate is its
orthogonal complement. -/
noncomputable def lineOrthogonalEquiv (u : E) (hu : u ≠ 0) :
    ℝ × (ℝ ∙ u)ᗮ ≃L[ℝ] E := by
  let den : ℝ := ⟪u, u⟫_ℝ
  have hden : den ≠ 0 := by
    dsimp [den]
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  let forward : ℝ × (ℝ ∙ u)ᗮ →ₗ[ℝ] E :=
    { toFun := fun z => z.1 • u + z.2.1
      map_add' := by
        intro x y
        simp [add_smul, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c x
        simp [smul_add, mul_smul] }
  let backward : E →ₗ[ℝ] ℝ × (ℝ ∙ u)ᗮ :=
    { toFun := fun x =>
        let a := ⟪u, x⟫_ℝ / den
        (a, ⟨x - a • u, by
          rw [Submodule.mem_orthogonal']
          intro y hy
          rw [Submodule.mem_span_singleton] at hy
          obtain ⟨c, rfl⟩ := hy
          simp only [inner_smul_left, inner_sub_right, real_inner_smul_right]
          field_simp [den, hden]
          ring⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp [den, inner_add_right, add_div]
        · apply Subtype.ext
          simp [den, inner_add_right, add_div, add_smul, sub_eq_add_neg]
          abel
      map_smul' := by
        intro c x
        apply Prod.ext
        · simp [den, real_inner_smul_right, mul_div_assoc]
        · apply Subtype.ext
          simp [den, real_inner_smul_right, smul_sub, mul_smul, mul_div_assoc] }
  let e : ℝ × (ℝ ∙ u)ᗮ ≃ₗ[ℝ] E :=
    { toLinearMap := forward
      invFun := backward
      left_inv := by
        rintro ⟨a,z⟩
        apply Prod.ext
        · have hz : ⟪u, (z : E)⟫_ℝ = 0 := by
            exact (Submodule.mem_orthogonal' _ _).mp z.2 u
              (Submodule.mem_span_singleton_self u)
          simp [forward, backward, den, hz, hden,
            real_inner_smul_right]
        · apply Subtype.ext
          have hz : ⟪u, (z : E)⟫_ℝ = 0 := by
            exact (Submodule.mem_orthogonal' _ _).mp z.2 u
              (Submodule.mem_span_singleton_self u)
          simp [forward, backward, den, hz, hden,
            real_inner_smul_right]
      right_inv := by
        intro x
        simp [forward, backward, den, hden] }
  exact e.toContinuousLinearEquiv

@[simp]
lemma lineOrthogonalEquiv_apply (u : E) (hu : u ≠ 0)
    (z : ℝ × (ℝ ∙ u)ᗮ) :
    lineOrthogonalEquiv u hu z = z.1 • u + z.2.1 := by
  rfl

/-- A smooth nonvanishing vector field admits local coordinates whose
first coordinate line is its flow.  The transverse model is the orthogonal
complement of the field value at the base point. -/
theorem exists_oneField_flowBox
    (hΩ : IsOpen Ω) {v : Field E} (hv : ContDiffOn ℝ ∞ v Ω)
    {p : E} (hp : p ∈ Ω) (hvp : v p ≠ 0) :
    ∃ (e : OpenPartialHomeomorph (ℝ × (ℝ ∙ v p)ᗮ) E)
      (U : Set (ℝ × (ℝ ∙ v p)ᗮ)),
      IsOpen U ∧ (0,0) ∈ U ∧ U ⊆ e.source ∧
      e (0,0) = p ∧ IsOpen (e '' U) ∧ e '' U ⊆ Ω ∧
      ContDiffOn ℝ ∞ e U ∧ ContDiffOn ℝ ∞ e.symm (e '' U) ∧
      (∀ z ∈ U, (fderiv ℝ e z).IsInvertible) ∧
      (∀ z ∈ U,
        (fderiv ℝ e z) (1,0) = v (e z)) := by
  obtain ⟨P, hPc⟩ := exists_symmetricFlowPatch hΩ hv hp
  subst hPc
  let H : Submodule ℝ E := (ℝ ∙ v p)ᗮ
  let χ : ℝ × H → E := fun z => P.toFun (p + z.2.1) z.1
  have h0time : (0 : ℝ) ∈ Set.Ioo (-P.ε) P.ε := by
    constructor <;> linarith [P.ε_pos]
  have hχ0 : χ (0,0) = p := by
    simp [χ, P.initial]
  have hχsmoothAt : ContDiffAt ℝ ∞ χ (0,0) := by
    have hbase :
        ContDiffAt ℝ ∞
          (fun z : ℝ × H => (p + z.2.1, z.1)) (0,0) := by
      fun_prop
    have hP :
        ContDiffAt ℝ ∞
          (fun z : E × ℝ => P.toFun z.1 z.2) (p,0) :=
      (P.smooth (p,0) ⟨P.center_mem, h0time⟩).contDiffAt
        ((P.open_U.prod isOpen_Ioo).mem_nhds
          ⟨P.center_mem, h0time⟩)
    simpa [χ] using hP.comp (0,0) hbase
  have hχdiff : DifferentiableAt ℝ χ (0,0) :=
    hχsmoothAt.differentiableAt (by simp)
  have htime :
      (fderiv ℝ χ (0,0)) (1,0) = v p := by
    have hline :
        HasDerivAt (fun t : ℝ => χ (t,0)) (v p) 0 := by
      simpa [χ, P.initial] using
        P.ode p P.center_mem 0 h0time
    have hinc :
        HasDerivAt (fun t : ℝ => ((t, (0 : H)) : ℝ × H)) (1,0) 0 := by
      fun_prop
    have hchain :=
      hχdiff.hasFDerivAt.comp_hasDerivAt 0 hinc
    exact hchain.unique hline
  have htrans :
      ∀ z : H, (fderiv ℝ χ (0,0)) (0,z) = z.1 := by
    intro z
    have hslice :
        (fun y : H => χ (0,y)) = fun y => p + y.1 := by
      funext y
      simp [χ, P.initial]
    have hinc :
        HasFDerivAt (fun y : H => ((0,y) : ℝ × H))
          (ContinuousLinearMap.inr ℝ ℝ H) 0 := by
      fun_prop
    have hchain := hχdiff.hasFDerivAt.comp 0 hinc
    have hright :
        HasFDerivAt (fun y : H => p + y.1)
          (Submodule.subtypeL H) 0 := by
      fun_prop
    rw [hslice] at hchain
    have heq := hchain.unique hright
    have := congrArg (fun T : H →L[ℝ] E => T z) heq
    simpa [ContinuousLinearMap.comp_apply] using this
  have hder :
      fderiv ℝ χ (0,0) =
        (lineOrthogonalEquiv (v p) hvp :
          ℝ × H →L[ℝ] E) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,z⟩
    have hsplit :
        ((a,z) : ℝ × H) =
          a • ((1,0) : ℝ × H) + (0,z) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, htime, htrans]
    simp [lineOrthogonalEquiv_apply, H]
  have hχder :
      HasFDerivAt χ
        (lineOrthogonalEquiv (v p) hvp : ℝ × H →L[ℝ] E) (0,0) := by
    rw [← hder]
    exact hχdiff.hasFDerivAt
  let e : OpenPartialHomeomorph (ℝ × H) E :=
    hχsmoothAt.toOpenPartialHomeomorph χ hχder (by simp)
  have h0source : (0,0) ∈ e.source :=
    hχsmoothAt.mem_toOpenPartialHomeomorph_source hχder (by simp)
  have he0 : e (0,0) = p := by
    simpa [e] using hχ0
  have hfderiv_cont :
      ContinuousAt (fderiv ℝ χ) (0,0) :=
    hχsmoothAt.continuousAt_fderiv (by simp)
  have hinv0 : (fderiv ℝ χ (0,0)).IsInvertible := by
    rw [hder]
    exact ContinuousLinearMap.isInvertible_equiv
  have hinv_event :
      ∀ᶠ z in 𝓝 ((0,0) : ℝ × H),
        (fderiv ℝ χ z).IsInvertible :=
    hfderiv_cont.eventually hinv0.eventually_nhds
  let good : Set (ℝ × H) :=
    e.source ∩
      {z | p + z.2.1 ∈ P.U} ∩
      {z | z.1 ∈ Set.Ioo (-P.ε) P.ε} ∩
      χ ⁻¹' Ω ∩
      {z | (fderiv ℝ χ z).IsInvertible}
  have hgood : good ∈ 𝓝 ((0,0) : ℝ × H) := by
    refine Filter.inter_mem
      (Filter.inter_mem
        (Filter.inter_mem
          (Filter.inter_mem
            (e.open_source.mem_nhds h0source)
            ?_) ?_) ?_) hinv_event
    · exact (by
        have hc : ContinuousAt (fun z : ℝ × H => p + z.2.1) (0,0) := by fun_prop
        exact hc.eventually (by simpa using P.center_mem))
    · exact (continuousAt_fst.eventually
        (isOpen_Ioo.mem_nhds h0time))
    · have hc : ContinuousAt χ (0,0) := hχsmoothAt.continuousAt
      exact hc.eventually (by simpa [hχ0] using hΩ.mem_nhds hp)
  obtain ⟨U, hUgood, hU, h0U⟩ := mem_nhds_iff.mp hgood
  have hUsource : U ⊆ e.source := fun z hz => (hUgood hz).1
  have hUflow :
      ∀ z ∈ U, p + z.2.1 ∈ P.U ∧
        z.1 ∈ Set.Ioo (-P.ε) P.ε := by
    intro z hz
    exact ⟨(hUgood hz).2.1, (hUgood hz).2.2.1⟩
  have hUΩ : e '' U ⊆ Ω := by
    rintro _ ⟨z,hz,rfl⟩
    have := (hUgood hz).2.2.2.1
    simpa [e] using this
  have himgOpen : IsOpen (e '' U) :=
    e.isOpen_image_of_subset_source hU hUsource
  have hesmooth : ContDiffOn ℝ ∞ e U := by
    intro z hz
    have hdom := hUflow z hz
    have hP :
        ContDiffAt ℝ ∞
          (fun q : E × ℝ => P.toFun q.1 q.2)
          (p + z.2.1, z.1) :=
      (P.smooth _ hdom).contDiffAt
        ((P.open_U.prod isOpen_Ioo).mem_nhds hdom)
    have hbase :
        ContDiffAt ℝ ∞
          (fun y : ℝ × H => (p + y.2.1, y.1)) z := by
      fun_prop
    simpa [e, χ] using hP.comp z hbase
  have heinv :
      ∀ z ∈ U, (fderiv ℝ e z).IsInvertible := by
    intro z hz
    have hz' := (hUgood hz).2.2.2.2
    simpa [e] using hz'
  have hesymm : ContDiffOn ℝ ∞ e.symm (e '' U) := by
    rintro y ⟨z,hz,rfl⟩
    have hzs : z ∈ e.source := hUsource hz
    have hzt : e z ∈ e.target := e.mapsTo hzs
    have hez : ContDiffAt ℝ ∞ e z :=
      (hesmooth z hz).contDiffAt (hU.mem_nhds hz)
    rcases heinv z hz with ⟨d, hd⟩
    have hderz :
        HasFDerivAt e (d : (ℝ × H) →L[ℝ] E) z := by
      rw [hd]
      exact hez.differentiableAt (by simp) |>.hasFDerivAt
    exact (e.contDiffAt_symm hzt hderz hez).contDiffWithinAt
  have htime_all :
      ∀ z ∈ U, (fderiv ℝ e z) (1,0) = v (e z) := by
    intro z hz
    have hdom := hUflow z hz
    have hdiff : DifferentiableAt ℝ χ z :=
      (hesmooth z hz).differentiableWithinAt.differentiableAt
        (hU.mem_nhds hz)
    have hline :
        HasDerivAt (fun t : ℝ => χ (t,z.2))
          (v (χ z)) z.1 := by
      simpa [χ] using
        P.ode (p + z.2.1) hdom.1 z.1 hdom.2
    have hinc :
        HasDerivAt (fun t : ℝ => ((t,z.2) : ℝ × H)) (1,0) z.1 := by
      fun_prop
    have hchain := hdiff.hasFDerivAt.comp_hasDerivAt z.1 hinc
    have := hchain.unique hline
    simpa [e] using this
  refine ⟨e, U, hU, h0U, hUsource, ?_, himgOpen, hUΩ,
    hesmooth, hesymm, heinv, htime_all⟩
  simpa [e] using hχ0


/-! ### Differential transport through a smooth local chart -/

def chartPullbackField
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph F E) (v : Field E) : F → F :=
  fun z => fderiv ℝ e.symm (e z) (v (e z))

def chartPullbackDistribution
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph F E) (D : Distribution E) : Distribution F :=
  fun z => (D (e z)).comap (fderiv ℝ e z).toLinearMap

lemma fderiv_symm_comp_fderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (e : OpenPartialHomeomorph F E)
    {U : Set F} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e U)
    (hes : ContDiffOn ℝ ∞ e.symm (e '' U))
    {z : F} (hz : z ∈ U) (x : F) :
    fderiv ℝ e.symm (e z) (fderiv ℝ e z x) = x := by
  have hze : e z ∈ e '' U := ⟨z,hz,rfl⟩
  have hde : DifferentiableAt ℝ e z :=
    (he z hz).contDiffAt (hU.mem_nhds hz)
      |>.differentiableAt (by simp)
  have hdes : DifferentiableAt ℝ e.symm (e z) :=
    (hes (e z) hze).contDiffAt
      ((e.isOpen_image_of_subset_source hU hUs).mem_nhds hze)
      |>.differentiableAt (by simp)
  have hcomp :=
    hdes.hasFDerivAt.comp z hde.hasFDerivAt
  have hlocal :
      (fun y => e.symm (e y)) =ᶠ[𝓝 z] fun y => y := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact e.left_inv (hUs hy)
  have hid :
      HasFDerivAt (fun y : F => y) (1 : F →L[ℝ] F) z :=
    hasFDerivAt_id z
  have heq :
      (fderiv ℝ e.symm (e z)).comp (fderiv ℝ e z) =
        (1 : F →L[ℝ] F) := by
    exact (hcomp.congr_of_eventuallyEq hlocal).unique hid
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : F →L[ℝ] F => T x) heq

lemma fderiv_comp_fderiv_symm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (e : OpenPartialHomeomorph F E)
    {U : Set F} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e U)
    (hes : ContDiffOn ℝ ∞ e.symm (e '' U))
    {z : F} (hz : z ∈ U) (x : E) :
    fderiv ℝ e z (fderiv ℝ e.symm (e z) x) = x := by
  have hze : e z ∈ e '' U := ⟨z,hz,rfl⟩
  have hde : DifferentiableAt ℝ e z :=
    (he z hz).contDiffAt (hU.mem_nhds hz)
      |>.differentiableAt (by simp)
  have hdes : DifferentiableAt ℝ e.symm (e z) :=
    (hes (e z) hze).contDiffAt
      ((e.isOpen_image_of_subset_source hU hUs).mem_nhds hze)
      |>.differentiableAt (by simp)
  have hcomp :=
    hde.hasFDerivAt.comp (e z) hdes.hasFDerivAt
  have htarget : e z ∈ e.target := e.mapsTo (hUs hz)
  have hlocal :
      (fun y => e (e.symm y)) =ᶠ[𝓝 (e z)] fun y => y := by
    filter_upwards [e.open_target.mem_nhds htarget] with y hy
    exact e.right_inv hy
  have hid :
      HasFDerivAt (fun y : E => y) (1 : E →L[ℝ] E) (e z) :=
    hasFDerivAt_id (e z)
  have heq :
      (fderiv ℝ e z).comp (fderiv ℝ e.symm (e z)) =
        (1 : E →L[ℝ] E) := by
    simpa [e.left_inv (hUs hz)] using
      (hcomp.congr_of_eventuallyEq hlocal).unique hid
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : E →L[ℝ] E => T x) heq

lemma chartPullbackField_push
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (e : OpenPartialHomeomorph F E)
    {U : Set F} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e U)
    (hes : ContDiffOn ℝ ∞ e.symm (e '' U))
    (v : Field E) {z : F} (hz : z ∈ U) :
    fderiv ℝ e z (chartPullbackField e v z) = v (e z) := by
  exact fderiv_comp_fderiv_symm e hU hUs he hes hz _

lemma chartPullbackField_smooth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace F]
    (e : OpenPartialHomeomorph F E)
    {U : Set F} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e U)
    (hes : ContDiffOn ℝ ∞ e.symm (e '' U))
    {v : Field E} (hv : ContDiffOn ℝ ∞ v (e '' U)) :
    ContDiffOn ℝ ∞ (chartPullbackField e v) U := by
  unfold chartPullbackField
  have hdes :
      ContDiffOn ℝ ∞ (fderiv ℝ e.symm) (e '' U) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen
      (e.isOpen_image_of_subset_source hU hUs)).mp hes).2
  fun_prop

/-- Lie brackets commute with pullback by a smooth local diffeomorphism. -/
lemma chartPullbackField_lieBracket
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace F]
    (e : OpenPartialHomeomorph F E)
    {U : Set F} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e U)
    (hes : ContDiffOn ℝ ∞ e.symm (e '' U))
    {v w : Field E}
    (hv : ContDiffOn ℝ ∞ v (e '' U))
    (hw : ContDiffOn ℝ ∞ w (e '' U)) :
    EqOn
      (chartPullbackField e (lieBracket v w))
      (lieBracket (chartPullbackField e v) (chartPullbackField e w)) U := by
  intro z hz
  have hpbv := chartPullbackField_smooth e hU hUs he hes hv
  have hpbw := chartPullbackField_smooth e hU hUs he hes hw
  have hde : DifferentiableAt ℝ e z :=
    (he z hz).contDiffAt (hU.mem_nhds hz)
      |>.differentiableAt (by simp)
  have hnat :
      fderiv ℝ e z
        (lieBracket (chartPullbackField e v)
          (chartPullbackField e w) z) =
        lieBracket v w (e z) := by
    -- Differentiate the two identities
    -- de·e^*v = v∘e and de·e^*w = w∘e.  The Hessian terms of e
    -- cancel after antisymmetrization, leaving naturality of the bracket.
    have hvpush :
        (fun y => fderiv ℝ e y (chartPullbackField e v y)) =ᶠ[𝓝 z]
          (fun y => v (e y)) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact chartPullbackField_push e hU hUs he hes v hy
    have hwpush :
        (fun y => fderiv ℝ e y (chartPullbackField e w y)) =ᶠ[𝓝 z]
          (fun y => w (e y)) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact chartPullbackField_push e hU hUs he hes w hy
    have hveq := hvpush.fderiv_eq
    have hweq := hwpush.fderiv_eq
    simp only [lieBracket] at *
    -- This is the standard second-derivative cancellation in the
    -- coordinate-invariance proof of the Lie bracket.
    simpa [ContinuousLinearMap.comp_apply] using
      sub_eq_sub_iff_add_eq_add.mp <| by
        rw [hveq,hweq]
        simp [fderiv_comp, hde,
          (hv (e z) ⟨z,hz,rfl⟩).differentiableWithinAt,
          (hw (e z) ⟨z,hz,rfl⟩).differentiableWithinAt]
  apply (fderiv ℝ e z).injective_of_isInvertible
  rw [chartPullbackField_push e hU hUs he hes]
  exact hnat

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

lemma LieWordOn.smooth {U : Set E} {D : Distribution E} {v : Field E}
    (hv : LieWordOn U D v) : ContDiffOn ℝ ∞ v U := by
  induction hv with
  | basic v hv => exact hv.1
  | add hv hw ihv ihw => exact ihv.add ihw
  | smul a ha hv ih => exact ha.smul ih
  | bracket hv hw ihv ihw =>
      simpa [lieBracket] using ihv.lieBracket_vectorField ihw (by simp)

lemma LieWordOn.mono {U V : Set E} {D : Distribution E} {v : Field E}
    (hVU : V ⊆ U) (hv : LieWordOn U D v) : LieWordOn V D v := by
  induction hv with
  | basic v hv =>
      exact LieWordOn.basic v
        ⟨hv.1.mono hVU, fun q hq => hv.2 q (hVU hq)⟩
  | add hv hw ihv ihw => exact LieWordOn.add ihv ihw
  | smul a ha hv ih => exact LieWordOn.smul a (ha.mono hVU) ih
  | bracket hv hw ihv ihw => exact LieWordOn.bracket ihv ihw

lemma LieWordOn.neg {U : Set E} {D : Distribution E} {v : Field E}
    (hv : LieWordOn U D v) : LieWordOn U D (fun q => -v q) := by
  simpa using LieWordOn.smul (D := D) (fun _ : E => (-1 : ℝ))
    contDiff_const.contDiffOn hv

lemma LieWordOn.sub {U : Set E} {D : Distribution E} {v w : Field E}
    (hv : LieWordOn U D v) (hw : LieWordOn U D w) :
    LieWordOn U D (fun q => v q - w q) := by
  simpa [sub_eq_add_neg] using LieWordOn.add hv hw.neg

lemma LieWordOn.sum {U : Set E} {D : Distribution E} {ι : Type*}
    (s : Finset ι) {v : ι → Field E}
    (hv : ∀ i ∈ s, LieWordOn U D (v i)) :
    LieWordOn U D (fun q => ∑ i ∈ s, v i q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using LieWordOn.smul (D := D) (fun _ : E => (0 : ℝ))
        contDiff_const.contDiffOn
        (LieWordOn.basic (fun _ => 0)
          ⟨contDiff_const.contDiffOn, fun q hq => (D q).zero_mem⟩)
  | @insert i s hi ih =>
      have hvi := hv i (Finset.mem_insert_self _ _)
      have hvs : ∀ j ∈ s, LieWordOn U D (v j) :=
        fun j hj => hv j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using LieWordOn.add hvi (ih hvs)

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

/-- If the Lie completion has a smooth local frame, then near every
point it admits a frame consisting of actual local Lie words in the original
distribution. Finite-dimensionality lets us choose a basis from the germ
generators at the base point; constant local rank and openness of linear
independence propagate that basis to a neighborhood. -/
lemma exists_local_lieWord_frame {D : Distribution E}
    (hD : HasLocalSmoothFrame Ω (lieCompletion Ω D))
    {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (n : ℕ) (v : Fin n → Field E),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∀ i, LieWordOn U D (v i)) ∧
      (∀ q ∈ U,
        LinearIndependent ℝ (fun i => v i q) ∧
        lieCompletion Ω D q =
          Submodule.span ℝ (Set.range (fun i => v i q))) := by
  obtain ⟨Wf, hWf, hpWf, hWfΩ, m, e, he, heframe⟩ := hD p hp
  let G : Set E := {a | ∃ (W : Set E) (w : Field E),
    IsOpen W ∧ p ∈ W ∧ W ⊆ Ω ∧ LieWordOn W D w ∧ w p = a}
  have hcompletion_p :
      lieCompletion Ω D p = Submodule.span ℝ G := by
    rfl
  obtain ⟨b, hbG, hbspan, hbli⟩ := exists_linearIndependent ℝ G
  have hbfinite : b.Finite := hbli.set_finite_of_isNoetherian
  letI : Fintype b := hbfinite.fintype
  have hwitness :
      ∀ x : b, ∃ (W : Set E) (w : Field E),
        IsOpen W ∧ p ∈ W ∧ W ⊆ Ω ∧ LieWordOn W D w ∧ w p = x.1 := by
    intro x
    exact hbG x.property
  choose W w hW hpW hWΩ hw hwp using hwitness
  let W₀ : Set E := Wf ∩ ⋂ x : b, W x
  have hW₀ : IsOpen W₀ := by
    apply hWf.inter
    apply isOpen_iInter_of_finite
    exact hW
  have hpW₀ : p ∈ W₀ := by
    refine ⟨hpWf, ?_⟩
    simp only [mem_iInter]
    exact hpW
  have hW₀Ω : W₀ ⊆ Ω := fun _ hq => hWfΩ hq.1
  let eb : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  let g : Fin (Fintype.card b) → Field E := fun i => w (eb i)
  have hgp :
      LinearIndependent ℝ (fun i : Fin (Fintype.card b) => g i p) := by
    have h := hbli.comp eb eb.injective
    simpa [g, Function.comp_def, hwp] using h
  have hspanp :
      Submodule.span ℝ
          (Set.range (fun i : Fin (Fintype.card b) => g i p)) =
        lieCompletion Ω D p := by
    rw [hcompletion_p]
    have hrange :
        Set.range (fun i : Fin (Fintype.card b) => g i p) = b := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        simpa [g, hwp] using (eb i).property
      · intro hz
        let z' : b := ⟨z, hz⟩
        obtain ⟨i, rfl⟩ := eb.surjective z'
        exact ⟨i, by simp [g, hwp]⟩
    rw [hrange, hbspan]
  have hcard : Fintype.card b = m := by
    have hleft :
        Module.finrank ℝ
            (Submodule.span ℝ
              (Set.range (fun i : Fin (Fintype.card b) => g i p))) =
          Fintype.card b := by
      simpa using finrank_span_eq_card hgp
    have hright :
        Module.finrank ℝ (lieCompletion Ω D p) = m := by
      rw [(heframe p hpWf).2]
      simpa using finrank_span_eq_card (heframe p hpWf).1
    rw [hspanp] at hleft
    omega
  have hg_smooth_W₀ :
      ∀ i, ContDiffOn ℝ ∞ (g i) W₀ := by
    intro i
    have hsub : W₀ ⊆ W (eb i) := by
      intro q hq
      exact mem_iInter.mp hq.2 (eb i)
    exact (hw (eb i)).smooth.mono hsub
  have hg_cont :
      ContinuousAt
        (fun q => fun i : Fin (Fintype.card b) => g i q) p := by
    rw [continuousAt_pi]
    intro i
    exact ((hg_smooth_W₀ i p hpW₀).contDiffAt
      (hW₀.mem_nhds hpW₀)).continuousAt
  have hg_ind_eventually :
      ∀ᶠ q in 𝓝 p,
        LinearIndependent ℝ (fun i : Fin (Fintype.card b) => g i q) :=
    hg_cont (LinearIndependent.eventually hgp)
  have hgood :
      W₀ ∩
        {q | LinearIndependent ℝ
          (fun i : Fin (Fintype.card b) => g i q)} ∈ 𝓝 p :=
    inter_mem (hW₀.mem_nhds hpW₀) hg_ind_eventually
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgood
  have hUW₀ : U ⊆ W₀ := fun q hq => (hUsub hq).1
  have hUΩ : U ⊆ Ω := hUW₀.trans hW₀Ω
  have hg_ind :
      ∀ q ∈ U, LinearIndependent ℝ
        (fun i : Fin (Fintype.card b) => g i q) :=
    fun q hq => (hUsub hq).2
  have hg_word : ∀ i, LieWordOn U D (g i) := by
    intro i
    have hsub : U ⊆ W (eb i) := by
      intro q hq
      exact mem_iInter.mp (hUW₀ hq).2 (eb i)
    exact (hw (eb i)).mono hsub
  have hg_span :
      ∀ q ∈ U,
        lieCompletion Ω D q =
          Submodule.span ℝ
            (Set.range (fun i : Fin (Fintype.card b) => g i q)) := by
    intro q hq
    have hle :
        Submodule.span ℝ
            (Set.range (fun i : Fin (Fintype.card b) => g i q)) ≤
          lieCompletion Ω D q := by
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      apply Submodule.subset_span
      exact ⟨U, g i, hU, hq, hUΩ, hg_word i, rfl⟩
    apply le_antisymm
    · apply Submodule.eq_of_le_of_finrank_eq hle
      · rw [finrank_span_eq_card (hg_ind q hq), Fintype.card_fin]
        have hqWf : q ∈ Wf := (hUW₀ hq).1
        have hdimq :
            Module.finrank ℝ (lieCompletion Ω D q) = m := by
          rw [(heframe q hqWf).2]
          simpa using finrank_span_eq_card (heframe q hqWf).1
        simpa [hcard] using hdimq.symm
      · infer_instance
    · exact hle
  exact ⟨U, Fintype.card b, g, hU, hpU, hUΩ, hg_word,
    fun q hq => ⟨hg_ind q hq, hg_span q hq⟩⟩

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


/-- A local submersion whose fibres are exactly the leaves of a distribution.
This is the coordinate form of the hard direction of Frobenius. -/
structure FrobeniusSubmersionAt
    (Ω : Set E) (D : Distribution E) (r : ℕ) (p : E) where
  k : ℕ
  dim_eq : r + k = Module.finrank ℝ E
  U : Set E
  H : E → Vec (Fin k)
  isOpen_U : IsOpen U
  mem_U : p ∈ U
  subset_U : U ⊆ Ω
  smooth_H : ContDiffOn ℝ ∞ H U
  surjective_fderiv :
    ∀ q ∈ U, Function.Surjective (fderiv ℝ H q)
  ker_fderiv :
    ∀ q ∈ U, (fderiv ℝ H q).ker = D q

/-- Scalar coordinate functions of a Frobenius submersion. -/
def FrobeniusSubmersionAt.integral
    {D : Distribution E} {r : ℕ} {p : E}
    (F : FrobeniusSubmersionAt Ω D r p) (i : Fin F.k) : E → ℝ :=
  fun q => F.H q i

lemma FrobeniusSubmersionAt.integral_smooth
    {D : Distribution E} {r : ℕ} {p : E}
    (F : FrobeniusSubmersionAt Ω D r p) (i : Fin F.k) :
    ContDiffOn ℝ ∞ (F.integral i) F.U := by
  exact (contDiff_apply ℝ i).comp_contDiffOn F.smooth_H

lemma FrobeniusSubmersionAt.fderiv_integral
    {D : Distribution E} {r : ℕ} {p q x : E}
    (F : FrobeniusSubmersionAt Ω D r p)
    (hq : q ∈ F.U) (i : Fin F.k) :
    fderiv ℝ (F.integral i) q x = (fderiv ℝ F.H q x) i := by
  have hH : DifferentiableAt ℝ F.H q :=
    (F.smooth_H q hq).contDiffAt (F.isOpen_U.mem_nhds hq)
      |>.differentiableAt (by simp)
  simpa [FrobeniusSubmersionAt.integral] using
    (ContinuousLinearMap.apply ℝ (Vec (Fin F.k)) i).comp_hasFDerivAt
      q hH.hasFDerivAt

/-- The coordinate gradients of a Frobenius submersion are independent. -/
lemma FrobeniusSubmersionAt.gradients_independent
    {D : Distribution E} {r : ℕ} {p q : E}
    (F : FrobeniusSubmersionAt Ω D r p) (hq : q ∈ F.U) :
    LinearIndependent ℝ (fun i : Fin F.k => gradient (F.integral i) q) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  let eᵢ : Vec (Fin F.k) :=
    WithLp.toLp 2 (fun j => if j = i then (1 : ℝ) else 0)
  obtain ⟨x, hx⟩ := F.surjective_fderiv q hq eᵢ
  have hinner := congrArg
    (fun y : E => ⟪y, x⟫_ℝ) hsum
  simp only [inner_sum_left, real_inner_smul_left, inner_zero_left] at hinner
  have hcoord :
      ∀ j : Fin F.k,
        ⟪gradient (F.integral j) q, x⟫_ℝ =
          if j = i then 1 else 0 := by
    intro j
    rw [inner_gradient_left]
    rw [F.fderiv_integral hq]
    rw [hx]
    simp [eᵢ]
  simp_rw [hcoord] at hinner
  simpa using hinner

/-- The gradients of the transverse coordinates span the orthogonal
complement of the distribution. -/
lemma FrobeniusSubmersionAt.gradient_span
    {D : Distribution E} {r : ℕ} {p q : E}
    (F : FrobeniusSubmersionAt Ω D r p)
    (hrank : ConstantRankOn Ω D r) (hq : q ∈ F.U) :
    Submodule.span ℝ
        (Set.range (fun i : Fin F.k => gradient (F.integral i) q)) =
      (D q)ᗮ := by
  have hle :
      Submodule.span ℝ
          (Set.range (fun i : Fin F.k => gradient (F.integral i) q)) ≤
        (D q)ᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro x hx
    rw [inner_gradient_left, F.fderiv_integral hq]
    have hxker : x ∈ (fderiv ℝ F.H q).ker := by
      rw [F.ker_fderiv q hq]
      exact hx
    rw [ContinuousLinearMap.mem_ker] at hxker
    rw [hxker]
    simp
  apply Submodule.eq_of_le_of_finrank_eq hle
  · rw [finrank_span_eq_card (F.gradients_independent hq), Fintype.card_fin]
    have hdim := (D q).finrank_add_finrank_orthogonal
    have hrq := hrank q (F.subset_U hq)
    omega
  · infer_instance



/-- Rank-indexed Frobenius submersion property, quantified over the ambient
finite-dimensional Euclidean space so the induction may pass to a transverse
hyperplane. -/
def FrobeniusSubmersionProperty (r : ℕ) : Prop :=
  ∀ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace F]
    {ΩF : Set F} {DF : Distribution F},
    IsOpen ΩF →
    HasLocalSmoothFrame ΩF DF →
    ConstantRankOn ΩF DF r →
    InvolutiveOn ΩF DF →
    ∀ {p : F}, p ∈ ΩF →
      FrobeniusSubmersionAt ΩF DF r p

/-- Rank-zero Frobenius is just linear coordinates: a zero-dimensional
distribution is the zero subspace, and the standard orthonormal
representation is a submersion with trivial kernel. -/
theorem exists_frobeniusSubmersionAt_rank_zero
    {D : Distribution E}
    (hΩ : IsOpen Ω) (hrank : ConstantRankOn Ω D 0)
    {p : E} (hp : p ∈ Ω) :
    FrobeniusSubmersionAt Ω D 0 p := by
  let k := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let H : E → Vec (Fin k) := b.repr
  have hDzero : ∀ q ∈ Ω, D q = ⊥ := by
    intro q hq
    rw [← Submodule.finrank_eq_zero]
    exact hrank q hq
  have hHsmooth : ContDiff ℝ ∞ H := by
    exact b.repr.toContinuousLinearEquiv.contDiff
  refine
    { k := k
      dim_eq := by simp [k]
      U := Ω
      H := H
      isOpen_U := hΩ
      mem_U := hp
      subset_U := Set.Subset.rfl
      smooth_H := hHsmooth.contDiffOn
      surjective_fderiv := ?_
      ker_fderiv := ?_ }
  · intro q hq
    have hf :
        fderiv ℝ H q = b.repr.toContinuousLinearEquiv := by
      simpa [H] using b.repr.toContinuousLinearEquiv.hasFDerivAt.fderiv
    rw [hf]
    exact b.repr.surjective
  · intro q hq
    have hf :
        fderiv ℝ H q = b.repr.toContinuousLinearEquiv := by
      simpa [H] using b.repr.toContinuousLinearEquiv.hasFDerivAt.fderiv
    rw [hf, hDzero q hq]
    exact LinearMap.ker_eq_bot.mpr b.repr.injective


lemma frobeniusSubmersionProperty_zero :
    FrobeniusSubmersionProperty 0 := by
  intro F _ _ _ _ ΩF DF hΩ hframe hrank hinv p hp
  exact exists_frobeniusSubmersionAt_rank_zero hΩ hrank hp


/-- A Frobenius submersion immediately supplies the exact family of first
integrals used by Theorem 21. -/
theorem FrobeniusSubmersionAt.firstIntegrals
    {D : Distribution E} {r : ℕ} {p : E}
    (F : FrobeniusSubmersionAt Ω D r p)
    (hrank : ConstantRankOn Ω D r) :
    ∃ (U : Set E) (h : Fin (Module.finrank ℝ E - r) → E → ℝ),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∀ i, ContDiffOn ℝ ∞ (h i) U) ∧
      FunctionallyIndependentOn U h ∧
      (∀ q ∈ U,
        Submodule.span ℝ (Set.range (fun i => gradient (h i) q)) = (D q)ᗮ) := by
  have hk : F.k = Module.finrank ℝ E - r := by
    omega
  subst F.k
  refine ⟨F.U, F.integral, F.isOpen_U, F.mem_U, F.subset_U,
    F.integral_smooth, ?_, ?_⟩
  · intro q hq
    exact F.gradients_independent hq
  · intro q hq
    exact F.gradient_span hrank hq


/-- Parameterized Gram--Schmidt for a smooth family of vectors.  Unlike
`pointwiseGramSchmidt_smooth`, the parameter space and vector space may be
different. -/
def familyGramSchmidt
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} (f : Fin n → X → F) (i : Fin n) : X → F :=
  fun x => InnerProductSpace.gramSchmidt ℝ (fun j => f j x) i

lemma familyGramSchmidt_smooth
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} {U : Set X} (f : Fin n → X → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hind : ∀ x ∈ U, LinearIndependent ℝ (fun i => f i x)) :
    ∀ i, ContDiffOn ℝ ∞ (familyGramSchmidt f i) U := by
  intro i
  apply wellFounded_lt.induction i
  intro i ih
  have hformula :
      familyGramSchmidt f i =
        fun x => f i x -
          ∑ j in Finset.Iio i,
            (⟪familyGramSchmidt f j x, f i x⟫_ℝ /
                ⟪familyGramSchmidt f j x,
                  familyGramSchmidt f j x⟫_ℝ) •
              familyGramSchmidt f j x := by
    funext x
    have hgs :=
      InnerProductSpace.gramSchmidt_def'' ℝ (fun j : Fin n => f j x) i
    simp only [familyGramSchmidt] at *
    simp only [← real_inner_self_eq_norm_sq] at hgs
    exact (eq_sub_iff_add_eq).2 hgs.symm
  rw [hformula]
  apply (hf i).sub
  apply ContDiffOn.sum
  intro j hj
  have hji : j < i := Finset.mem_Iio.mp hj
  have hgj : ContDiffOn ℝ ∞ (familyGramSchmidt f j) U :=
    ih j hji
  have hnum :
      ContDiffOn ℝ ∞
        (fun x => ⟪familyGramSchmidt f j x, f i x⟫_ℝ) U :=
    hgj.inner ℝ (hf i)
  have hden :
      ContDiffOn ℝ ∞
        (fun x => ⟪familyGramSchmidt f j x,
          familyGramSchmidt f j x⟫_ℝ) U :=
    hgj.inner ℝ hgj
  have hden_ne :
      ∀ x ∈ U,
        ⟪familyGramSchmidt f j x,
          familyGramSchmidt f j x⟫_ℝ ≠ 0 := by
    intro x hx
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr <|
      InnerProductSpace.gramSchmidt_ne_zero j (hind x hx))
  exact (hnum.div hden hden_ne).smul hgj

/-- Pointwise Gram--Schmidt for a family of smooth vector fields. -/
def pointwiseGramSchmidt {n : ℕ} (f : Fin n → Field E) (i : Fin n) : Field E :=
  fun q => InnerProductSpace.gramSchmidt ℝ (fun j => f j q) i

/-- Gram--Schmidt depends smoothly on the base point as long as the input
family remains linearly independent. The proof uses the triangular recursive
formula and replaces the squared norm denominator by the smooth inner product. -/
lemma pointwiseGramSchmidt_smooth {n : ℕ} {U : Set E}
    (f : Fin n → Field E)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hind : ∀ q ∈ U, LinearIndependent ℝ (fun i => f i q)) :
    ∀ i, ContDiffOn ℝ ∞ (pointwiseGramSchmidt f i) U := by
  intro i
  apply wellFounded_lt.induction i
  intro i ih
  have hformula :
      pointwiseGramSchmidt f i =
        fun q => f i q -
          ∑ j in Finset.Iio i,
            (⟪pointwiseGramSchmidt f j q, f i q⟫_ℝ /
                ⟪pointwiseGramSchmidt f j q,
                  pointwiseGramSchmidt f j q⟫_ℝ) •
              pointwiseGramSchmidt f j q := by
    funext q
    have hgs :=
      InnerProductSpace.gramSchmidt_def'' ℝ (fun j : Fin n => f j q) i
    simp only [pointwiseGramSchmidt] at *
    simp only [← real_inner_self_eq_norm_sq] at hgs
    exact (eq_sub_iff_add_eq).2 hgs.symm
  rw [hformula]
  apply (hf i).sub
  apply ContDiffOn.sum
  intro j hj
  have hji : j < i := Finset.mem_Iio.mp hj
  have hgj : ContDiffOn ℝ ∞ (pointwiseGramSchmidt f j) U :=
    ih j hji
  have hnum :
      ContDiffOn ℝ ∞
        (fun q => ⟪pointwiseGramSchmidt f j q, f i q⟫_ℝ) U :=
    hgj.inner ℝ (hf i)
  have hden :
      ContDiffOn ℝ ∞
        (fun q => ⟪pointwiseGramSchmidt f j q,
          pointwiseGramSchmidt f j q⟫_ℝ) U :=
    hgj.inner ℝ hgj
  have hden_ne :
      ∀ q ∈ U,
        ⟪pointwiseGramSchmidt f j q,
          pointwiseGramSchmidt f j q⟫_ℝ ≠ 0 := by
    intro q hq
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr <|
      InnerProductSpace.gramSchmidt_ne_zero j (hind q hq))
  exact (hnum.div hden hden_ne).smul hgj

/-- Pointwise Gram--Schmidt stays inside the smooth Lie module:
each orthogonalized field is obtained from earlier ones by smooth scalar
multiples and finite sums. -/
lemma pointwiseGramSchmidt_lieWord {n : ℕ} {U : Set E} {D : Distribution E}
    (f : Fin n → Field E)
    (hf : ∀ i, LieWordOn U D (f i))
    (hind : ∀ q ∈ U, LinearIndependent ℝ (fun i => f i q)) :
    ∀ i, LieWordOn U D (pointwiseGramSchmidt f i) := by
  intro i
  apply wellFounded_lt.induction i
  intro i ih
  have hsmooth : ∀ j, ContDiffOn ℝ ∞ (pointwiseGramSchmidt f j) U :=
    pointwiseGramSchmidt_smooth f (fun j => (hf j).smooth) hind
  have hformula :
      pointwiseGramSchmidt f i =
        fun q => f i q -
          ∑ j in Finset.Iio i,
            (⟪pointwiseGramSchmidt f j q, f i q⟫_ℝ /
                ⟪pointwiseGramSchmidt f j q,
                  pointwiseGramSchmidt f j q⟫_ℝ) •
              pointwiseGramSchmidt f j q := by
    funext q
    have hgs :=
      InnerProductSpace.gramSchmidt_def'' ℝ (fun j : Fin n => f j q) i
    simp only [pointwiseGramSchmidt] at *
    simp only [← real_inner_self_eq_norm_sq] at hgs
    exact (eq_sub_iff_add_eq).2 hgs.symm
  rw [hformula]
  apply (hf i).sub
  apply LieWordOn.sum (Finset.Iio i)
  intro j hj
  have hji : j < i := Finset.mem_Iio.mp hj
  have hgj := ih j hji
  have hnum :
      ContDiffOn ℝ ∞
        (fun q => ⟪pointwiseGramSchmidt f j q, f i q⟫_ℝ) U :=
    (hsmooth j).inner ℝ (hf i).smooth
  have hden :
      ContDiffOn ℝ ∞
        (fun q => ⟪pointwiseGramSchmidt f j q,
          pointwiseGramSchmidt f j q⟫_ℝ) U :=
    (hsmooth j).inner ℝ (hsmooth j)
  have hden_ne :
      ∀ q ∈ U,
        ⟪pointwiseGramSchmidt f j q,
          pointwiseGramSchmidt f j q⟫_ℝ ≠ 0 := by
    intro q hq
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr <|
      InnerProductSpace.gramSchmidt_ne_zero j (hind q hq))
  exact LieWordOn.smul
    (hnum.div hden hden_ne) hgj

/-- Expansion in a finite orthogonal nonzero family. This is the
unnormalized orthogonal-basis formula used to obtain smooth coefficients for
local sections of the Lie completion. -/
lemma eq_sum_inner_div_self_smul_of_mem_span_orthogonal
    {n : ℕ} (g : Fin n → E)
    (horth : ∀ {i j : Fin n}, i ≠ j → ⟪g i, g j⟫_ℝ = 0)
    (hne : ∀ i, g i ≠ 0) {z : E}
    (hz : z ∈ Submodule.span ℝ (Set.range g)) :
    z = ∑ i : Fin n, (⟪g i, z⟫_ℝ / ⟪g i, g i⟫_ℝ) • g i := by
  let w : E := ∑ i : Fin n, (⟪g i, z⟫_ℝ / ⟪g i, g i⟫_ℝ) • g i
  have hw : w ∈ Submodule.span ℝ (Set.range g) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  have hzw : z - w ∈ Submodule.span ℝ (Set.range g) :=
    Submodule.sub_mem _ hz hw
  have hzworth : z - w ∈ (Submodule.span ℝ (Set.range g))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        have hden : ⟪g j, g j⟫_ℝ ≠ 0 := by
          rw [real_inner_self_eq_norm_sq]
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne j))
        simp only [w, inner_sub_left, inner_sum_left, real_inner_smul_left]
        rw [Finset.sum_eq_single j]
        · rw [real_inner_comm z (g j), div_mul_cancel₀ _ hden, sub_self]
        · intro i hi hij
          rw [horth hij]
          simp
        · simp
    | zero => simp
    | add x y hx hy ihx ihy =>
        simp [inner_add_right, ihx, ihy]
    | smul a x hx ih =>
        simp [inner_smul_right, ih]
  have hzero : z - w = 0 := by
    have hmem :
        z - w ∈
          Submodule.span ℝ (Set.range g) ⊓
            (Submodule.span ℝ (Set.range g))ᗮ :=
      ⟨hzw, hzworth⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hmem
    exact hmem
  exact sub_eq_zero.mp hzero

/-- A smooth local section of the Lie completion can be replaced, on
the neighborhood, by an actual Lie word. Orthogonalizing a Lie-word frame
gives smooth orthogonal coordinates, and the usual inner-product expansion
has smooth coefficients. -/
lemma exists_lieWord_representation
    {D : Distribution E} {U : Set E} {n : ℕ}
    (g : Fin n → Field E)
    (hgword : ∀ i, LieWordOn U D (g i))
    (hgind : ∀ q ∈ U, LinearIndependent ℝ (fun i => g i q))
    (hgspan : ∀ q ∈ U,
      lieCompletion Ω D q =
        Submodule.span ℝ (Set.range (fun i => g i q)))
    {z : Field E} (hzsmooth : ContDiffOn ℝ ∞ z U)
    (hzmem : ∀ q ∈ U, z q ∈ lieCompletion Ω D q) :
    ∃ z' : Field E, LieWordOn U D z' ∧ EqOn z' z U := by
  let gs : Fin n → Field E := fun i => pointwiseGramSchmidt g i
  have hgsword : ∀ i, LieWordOn U D (gs i) := by
    intro i
    exact pointwiseGramSchmidt_lieWord g hgword hgind i
  have hgssmooth : ∀ i, ContDiffOn ℝ ∞ (gs i) U :=
    fun i => (hgsword i).smooth
  let c : Fin n → E → ℝ := fun i q =>
    ⟪gs i q, z q⟫_ℝ / ⟪gs i q, gs i q⟫_ℝ
  have hden_ne :
      ∀ i q, q ∈ U → ⟪gs i q, gs i q⟫_ℝ ≠ 0 := by
    intro i q hq
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr <| by
      simpa [gs, pointwiseGramSchmidt] using
        InnerProductSpace.gramSchmidt_ne_zero i (hgind q hq))
  have hc : ∀ i, ContDiffOn ℝ ∞ (c i) U := by
    intro i
    exact ((hgssmooth i).inner ℝ hzsmooth).div
      ((hgssmooth i).inner ℝ (hgssmooth i))
      (fun q hq => hden_ne i q hq)
  let z' : Field E := fun q => ∑ i : Fin n, c i q • gs i q
  have hzword : LieWordOn U D z' := by
    dsimp [z']
    apply LieWordOn.sum Finset.univ
    intro i hi
    exact LieWordOn.smul (hc i) (hgsword i)
  refine ⟨z', hzword, ?_⟩
  intro q hq
  have hzspan :
      z q ∈
        Submodule.span ℝ
          (Set.range (fun i : Fin n => gs i q)) := by
    have hzq := hzmem q hq
    rw [hgspan q hq] at hzq
    rw [show
      Submodule.span ℝ (Set.range (fun i : Fin n => gs i q)) =
        Submodule.span ℝ (Set.range (fun i : Fin n => g i q)) by
          simpa [gs, pointwiseGramSchmidt] using
            InnerProductSpace.span_gramSchmidt ℝ (fun i : Fin n => g i q)]
    exact hzq
  have hexpand :=
    eq_sum_inner_div_self_smul_of_mem_span_orthogonal
      (fun i : Fin n => gs i q)
      (fun {i j} hij => by
        simpa [gs, pointwiseGramSchmidt] using
          InnerProductSpace.gramSchmidt_orthogonal ℝ
            (fun a : Fin n => g a q) hij)
      (fun i => by
        simpa [gs, pointwiseGramSchmidt] using
          InnerProductSpace.gramSchmidt_ne_zero i (hgind q hq))
      hzspan
  simpa [z', c] using hexpand.symm

/-- Differential-geometric background still needed by Theorem 12.
The easy direction of Frobenius is proved below; this interface now contains
only the local-existence ingredients that require a genuine Frobenius/constant-
rank construction, plus the smooth orthogonal-complement frame. -/
class HasFrobeniusBackground
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] : Prop where
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

/-- Complete integrability implies involutivity directly: local first
integrals annihilate the distribution, so the Lie bracket of two local
sections annihilates all of their gradients as well. -/
lemma locallyCompletelyIntegrable_involutive
    {D : Distribution E} (hΩ : IsOpen Ω)
    (hint : LocallyCompletelyIntegrableOn Ω D) :
    InvolutiveOn Ω D := by
  intro U hU hUΩ v w hv hw p hp
  obtain ⟨W, m, h, hW, hpW, hWΩ, hh, hframe⟩ :=
    hint p (hUΩ hp)
  let V : Set E := U ∩ W
  have hV : IsOpen V := hU.inter hW
  have hpV : p ∈ V := ⟨hp, hpW⟩
  have hvV : IsSectionOn V D v :=
    ⟨hv.1.mono inter_subset_left, fun q hq => hv.2 q hq.1⟩
  have hwV : IsSectionOn V D w :=
    ⟨hw.1.mono inter_subset_left, fun q hq => hw.2 q hq.1⟩
  have hann :
      ∀ i : Fin m, ∀ q ∈ V,
        ⟪gradient (h i) q, v q⟫_ℝ = 0 ∧
        ⟪gradient (h i) q, w q⟫_ℝ = 0 := by
    intro i q hq
    have hgi :
        gradient (h i) q ∈ (D q)ᗮ := by
      rw [← (hframe q hq.2).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    constructor
    · exact (Submodule.mem_orthogonal' _ _).mp hgi _ (hvV.2 q hq)
    · exact (Submodule.mem_orthogonal' _ _).mp hgi _ (hwV.2 q hq)
  have hbracket_orth :
      ∀ i : Fin m, ⟪gradient (h i) p, lieBracket v w p⟫_ℝ = 0 := by
    intro i
    have hhi : ContDiffAt ℝ ∞ (h i) p :=
      (hh i p hpW).contDiffAt (hW.mem_nhds hpW)
    have hvp : DifferentiableAt ℝ v p :=
      (hvV.1 p hpV).contDiffAt (hV.mem_nhds hpV) |>.differentiableAt (by simp)
    have hwp : DifferentiableAt ℝ w p :=
      (hwV.1 p hpV).contDiffAt (hV.mem_nhds hpV) |>.differentiableAt (by simp)
    have hzv :
        (fun x => fderiv ℝ (h i) x (v x)) =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hpV] with x hx
      rw [← inner_gradient_left]
      exact (hann i x hx).1
    have hzw :
        (fun x => fderiv ℝ (h i) x (w x)) =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hpV] with x hx
      rw [← inner_gradient_left]
      exact (hann i x hx).2
    have hbr := fderiv_apply_lieBracket
      (f := h i) hhi (by simp) hvp hwp
    rw [hzv.fderiv_eq, hzw.fderiv_eq] at hbr
    simp at hbr
    rw [← inner_gradient_left]
    simpa [lieBracket] using hbr
  rw [← Submodule.orthogonal_orthogonal (K := D p)]
  rw [Submodule.mem_orthogonal']
  intro z hz
  rw [← (hframe p hpW).2] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      simpa [real_inner_comm] using hbracket_orth i
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp [inner_add_right, ihx, ihy]
  | smul a x hx ih =>
      simp [inner_smul_right, ih]

/-- Theorem 21 (Frobenius), in the local complete-integrability form
reviewed in Appendix A. The integrable-to-involutive implication is elementary;
the reverse implication is exactly the local first-integral construction. -/
theorem theorem21 [HasFrobeniusBackground E]
    {D : Distribution E} {r : ℕ}
    (hΩ : IsOpen Ω) (hframe : HasLocalSmoothFrame Ω D)
    (hrank : ConstantRankOn Ω D r) :
    LocallyCompletelyIntegrableOn Ω D ↔ InvolutiveOn Ω D := by
  constructor
  · exact locallyCompletelyIntegrable_involutive hΩ
  · intro hinv p hp
    obtain ⟨U, h, hU, hpU, hUΩ, hh, hind, hspan⟩ :=
      HasFrobeniusBackground.firstIntegrals hΩ hframe hrank hinv hp
    exact ⟨U, Module.finrank ℝ E - r, h, hU, hpU, hUΩ, hh,
      fun q hq => ⟨hind q hq, hspan q hq⟩⟩

/-- The Lie completion is involutive whenever it is a smooth
constant-rank distribution. A local Lie-word frame represents every smooth
section by a Lie word on a smaller neighborhood, so the bracket is again one
of the generators of the completion. -/
lemma lieCompletion_involutive
    {D : Distribution E}
    (hD : HasLocalSmoothFrame Ω (lieCompletion Ω D)) :
    InvolutiveOn Ω (lieCompletion Ω D) := by
  intro V hV hVΩ v w hv hw p hp
  obtain ⟨U, n, g, hU, hpU, hUΩ, hgword, hgframe⟩ :=
    exists_local_lieWord_frame hD (hVΩ hp)
  let W : Set E := V ∩ U
  have hW : IsOpen W := hV.inter hU
  have hpW : p ∈ W := ⟨hp, hpU⟩
  have hWΩ : W ⊆ Ω := fun q hq => hUΩ hq.2
  have hgwordW : ∀ i, LieWordOn W D (g i) :=
    fun i => (hgword i).mono inter_subset_right
  have hgindW : ∀ q ∈ W, LinearIndependent ℝ (fun i => g i q) :=
    fun q hq => (hgframe q hq.2).1
  have hgspanW : ∀ q ∈ W,
      lieCompletion Ω D q =
        Submodule.span ℝ (Set.range (fun i => g i q)) :=
    fun q hq => (hgframe q hq.2).2
  obtain ⟨v', hvword, hveq⟩ :=
    exists_lieWord_representation (Ω := Ω) g hgwordW hgindW hgspanW
      (hv.1.mono inter_subset_left)
      (fun q hq => hv.2 q hq.1)
  obtain ⟨w', hwword, hweq⟩ :=
    exists_lieWord_representation (Ω := Ω) g hgwordW hgindW hgspanW
      (hw.1.mono inter_subset_left)
      (fun q hq => hw.2 q hq.1)
  have hbrword : LieWordOn W D (lieBracket v' w') :=
    LieWordOn.bracket hvword hwword
  have hbrmem :
      lieBracket v' w' p ∈ lieCompletion Ω D p := by
    apply Submodule.subset_span
    exact ⟨W, lieBracket v' w', hW, hpW, hWΩ, hbrword, rfl⟩
  have hvev : v' =ᶠ[𝓝 p] v :=
    hveq.eventuallyEq_of_mem (hW.mem_nhds hpW)
  have hwev : w' =ᶠ[𝓝 p] w :=
    hweq.eventuallyEq_of_mem (hW.mem_nhds hpW)
  have hbr_eq : lieBracket v w p = lieBracket v' w' p := by
    simp only [lieBracket]
    rw [← hvev.fderiv_eq, ← hwev.fderiv_eq,
      ← hveq hpW, ← hweq hpW]
  rw [hbr_eq]
  exact hbrmem

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
      (∀ q ∈ U, Submodule.span ℝ (Set.range (fun i => gradient (h i) q)) = (D q)ᗮ) := by
  obtain ⟨U, m, h, hU, hpU, hUΩ, hh, hbasis⟩ :=
    ((theorem21 hΩ hframe hrank).mpr hinv) p hp
  have hm : m = Module.finrank ℝ E - r := by
    have hind := (hbasis p hpU).1
    have hspan := (hbasis p hpU).2
    calc
      m = Module.finrank ℝ
          (Submodule.span ℝ (Set.range (fun i => gradient (h i) p))) :=
        (finrank_span_eq_card hind).symm
      _ = Module.finrank ℝ (D p)ᗮ := by rw [hspan]
      _ = Module.finrank ℝ E - r := by
        have hsum := (D p).finrank_add_finrank_orthogonal
        rw [hrank p (hUΩ hpU)] at hsum
        omega
  subst m
  refine ⟨U, h, hU, hpU, hUΩ, hh, ?_, ?_⟩
  · intro q hq
    exact (hbasis q hq).1
  · intro q hq
    exact (hbasis q hq).2

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

/-- A constant-rank smooth distribution has a smooth local frame for
its orthogonal complement. Starting with a local frame for the distribution,
extend its value at the base point by a basis of the orthogonal complement,
shrink to where the combined family stays independent, and apply pointwise
Gram--Schmidt. -/
lemma orthogonal_local_frame
    {D : Distribution E} {r : ℕ}
    (hΩ : IsOpen Ω) (hframe : HasLocalSmoothFrame Ω D)
    (hrank : ConstantRankOn Ω D r) {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (v : Fin (Module.finrank ℝ E - r) → Field E),
      IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧
      (∀ i, ContDiffOn ℝ ∞ (v i) U) ∧
      (∀ q ∈ U, LinearIndependent ℝ (fun i => v i q) ∧
        Submodule.span ℝ (Set.range (fun i => v i q)) = (D q)ᗮ) := by
  obtain ⟨W, hW, hpW, hWΩ, n, u, hu, huframe⟩ := hframe p hp
  let k := Module.finrank ℝ E - r
  have hcomp : Module.finrank ℝ (D p)ᗮ = k := by
    have hdim := (D p).finrank_add_finrank_orthogonal
    have hrp := hrank p hp
    dsimp [k]
    omega
  let b : Basis (Fin k) ℝ (D p)ᗮ :=
    (Module.finBasis ℝ (D p)ᗮ).reindex (finCongr hcomp.symm)
  have hb :
      LinearIndependent ℝ (fun j : Fin k => ((b j : (D p)ᗮ) : E)) := by
    exact b.linearIndependent.map' ((D p)ᗮ).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.coe_injective)
  have hright :
      Submodule.span ℝ
          (Set.range (fun j : Fin k => ((b j : (D p)ᗮ) : E)) ≤ (D p)ᗮ := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact (b j).property
  have hdisj :
      Disjoint
        (Submodule.span ℝ (Set.range (fun i : Fin n => u i p)))
        (Submodule.span ℝ
          (Set.range (fun j : Fin k => ((b j : (D p)ᗮ) : E))) := by
    rw [← (huframe p hpW).2]
    exact (D p).orthogonal_disjoint.mono le_rfl hright
  have hsum :
      LinearIndependent ℝ
        (Sum.elim (fun i : Fin n => u i p)
          (fun j : Fin k => ((b j : (D p)ᗮ) : E)) : Fin n ⊕ Fin k → E) :=
    (huframe p hpW).1.sum_type hb hdisj
  let combined : Fin (n + k) → Field E :=
    fun i q =>
      (finSumFinEquiv.symm i).elim
        (fun a => u a q)
        (fun j => ((b j : (D p)ᗮ) : E))
  have hcombined_p :
      LinearIndependent ℝ (fun i : Fin (n + k) => combined i p) := by
    simpa [combined, Function.comp_def] using
      hsum.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
  have hcombined_cont :
      ContinuousAt (fun q => fun i : Fin (n + k) => combined i q) p := by
    rw [continuousAt_pi]
    intro i
    rcases hidx : finSumFinEquiv.symm i with a | j
    · simpa [combined, hidx] using
        ((hu a p hpW).contDiffAt (hW.mem_nhds hpW)).continuousAt
    · simpa [combined, hidx] using (continuousAt_const : ContinuousAt (fun _ : E =>
        ((b j : (D p)ᗮ) : E)) p)
  have hind_eventually :
      ∀ᶠ q in 𝓝 p,
        LinearIndependent ℝ (fun i : Fin (n + k) => combined i q) :=
    hcombined_cont (LinearIndependent.eventually hcombined_p)
  have hgood :
      W ∩ {q | LinearIndependent ℝ (fun i : Fin (n + k) => combined i q)} ∈ 𝓝 p :=
    inter_mem (hW.mem_nhds hpW) hind_eventually
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgood
  have hUW : U ⊆ W := fun q hq => (hUsub hq).1
  have hUΩ : U ⊆ Ω := hUW.trans hWΩ
  have hcombined_ind :
      ∀ q ∈ U, LinearIndependent ℝ (fun i : Fin (n + k) => combined i q) :=
    fun q hq => (hUsub hq).2
  have hcombined_smooth :
      ∀ i, ContDiffOn ℝ ∞ (combined i) U := by
    intro i
    rcases hidx : finSumFinEquiv.symm i with a | j
    · simpa [combined, hidx] using (hu a).mono hUW
    · simpa [combined, hidx] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E => ((b j : (D p)ᗮ) : E))).contDiffOn
  let v : Fin k → Field E :=
    fun j => pointwiseGramSchmidt combined (Fin.natAdd n j)
  have hv_smooth : ∀ j, ContDiffOn ℝ ∞ (v j) U := by
    intro j
    exact pointwiseGramSchmidt_smooth combined hcombined_smooth hcombined_ind
      (Fin.natAdd n j)
  have hv_ind :
      ∀ q ∈ U, LinearIndependent ℝ (fun j : Fin k => v j q) := by
    intro q hq
    have hall :=
      InnerProductSpace.gramSchmidt_linearIndependent (hcombined_ind q hq)
    simpa [v, pointwiseGramSchmidt] using
      hall.comp (Fin.natAdd n) (Fin.natAdd_injective k n)
  have hv_orth :
      ∀ q ∈ U, ∀ j : Fin k, v j q ∈ (D q)ᗮ := by
    intro q hq j
    rw [Submodule.mem_orthogonal']
    intro z hz
    rw [(huframe q (hUW hq)).2] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        have hlt : Fin.castAdd k a < Fin.natAdd n j := by
          omega
        have hortho :=
          InnerProductSpace.gramSchmidt_inv_triangular ℝ
            (fun i : Fin (n + k) => combined i q) hlt
        simpa [v, pointwiseGramSchmidt, combined] using hortho
    | zero => simp
    | add x y hx hy ihx ihy =>
        simp [inner_add_right, ihx, ihy]
    | smul a x hx ih =>
        simp [inner_smul_right, ih]
  have hv_span :
      ∀ q ∈ U,
        Submodule.span ℝ (Set.range (fun j : Fin k => v j q)) = (D q)ᗮ := by
    intro q hq
    have hle :
        Submodule.span ℝ (Set.range (fun j : Fin k => v j q)) ≤ (D q)ᗮ := by
      apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      exact hv_orth q hq j
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card (hv_ind q hq), Fintype.card_fin]
    have hdim := (D q).finrank_add_finrank_orthogonal
    have hrq := hrank q (hUΩ hq)
    dsimp [k]
    omega
  exact ⟨U, v, hU, hpU, hUΩ, hv_smooth,
    fun q hq => ⟨hv_ind q hq, hv_span q hq⟩⟩

/-- Theorem 12(i)--(ii). `rLie` is the paper's barred r, distinct from r. -/
theorem theorem12 [HasFrobeniusBackground E]
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
