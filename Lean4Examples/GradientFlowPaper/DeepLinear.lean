import Lean4Examples.GradientFlowPaper.MatrixFactorization

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
