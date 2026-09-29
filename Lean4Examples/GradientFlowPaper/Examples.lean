import Lean4Examples.GradientFlowPaper.MatrixFactorization

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
