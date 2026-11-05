module

public import SHEStochastic.MatrixSqrtSmooth
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixSqrtDerivative
open Matrix Filter SHE.FiniteTransport
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A spectral lower bound passes to the actual positive square root.
The scalar comparison matrix is identified through the same CFC calculus. -/
theorem lower (A : Matrix d d ℝ) (r : ℝ) (hr : 0≤r) (hA : r^2 • (1:Matrix d d ℝ)≤A) :
    r • (1:Matrix d d ℝ)≤CFC.sqrt A := by
  have hn : 0≤A := (smul_nonneg (sq_nonneg r) (zero_le_one : (0:Matrix d d ℝ)≤1)).trans hA
  have hspec : ∀ t ∈ spectrum ℝ A, r^2≤t :=
    (algebraMap_le_iff_le_spectrum hn.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hA)
  have hh := algebraMap_le_cfc Real.sqrt r A (fun t ht ↦
    (Real.le_sqrt hr ((sq_nonneg r).trans (hspec t ht))).mpr (hspec t ht))
      Real.continuous_sqrt.continuousOn hn.isSelfAdjoint
  rw [CFC.sqrt_eq_real_sqrt A hn,cfcₙ_eq_cfc]
  simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem quadratic_lower (A : Matrix d d ℝ) (r : ℝ) (hr : 0≤r)
    (hA : r^2 • (1:Matrix d d ℝ)≤A) (v : d → ℝ) :
    r*vectorSq v≤v ⬝ᵥ (CFC.sqrt A*ᵥv) := by
  have hp : (CFC.sqrt A-r • (1:Matrix d d ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (lower A r hr hA))
  have hh := hp.dotProduct_mulVec_nonneg v
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul] at hh
  have he : v ⬝ᵥ v=vectorSq v := by simp only [dotProduct,vectorSq,pow_two]
  rw [he,smul_eq_mul] at hh
  linarith

/-- The derivative of the actual square root solves the Sylvester
identity. Smoothness and the identity are derived from the CFC square relation. -/
theorem sylvester {A : E → Matrix d d ℝ} {x : E}
    (hA : ContDiffAt ℝ 1 A x) (hp : (A x).PosDef)
    (he : ∀ᶠ y in 𝓝 x, 0≤A y) (v : E) :
    CFC.sqrt (A x)*fderiv ℝ (fun y ↦ CFC.sqrt (A y)) x v+
      fderiv ℝ (fun y ↦ CFC.sqrt (A y)) x v*CFC.sqrt (A x)=fderiv ℝ A x v := by
  have hs := MatrixSqrtSmooth.comp hA hp he
  have hd := (hs.differentiableAt (by norm_num)).hasFDerivAt
  have hsq := (MatrixSylvesterSmooth.hasFDerivAt_square (CFC.sqrt (A x))).comp x hd
  have hrel : (fun y ↦ CFC.sqrt (A y)*CFC.sqrt (A y))=ᶠ[𝓝 x] A :=
    he.mono fun y hy ↦ CFC.sqrt_mul_sqrt_self (A y) hy
  have hh := (hsq.congr_of_eventuallyEq hrel.symm).unique ((hA.differentiableAt (by norm_num)).hasFDerivAt)
  exact congrArg (fun L : E →L[ℝ] Matrix d d ℝ ↦ L v) hh

/-- The actual first derivative has a dimension-independent Frobenius
bound controlled solely by the lower covariance eigenvalue. -/
theorem bound {A : E → Matrix d d ℝ} {x : E}
    (hA : ContDiffAt ℝ 1 A x) (hp : (A x).PosDef)
    (he : ∀ᶠ y in 𝓝 x, 0≤A y) (r : ℝ) (hr : 0≤r)
    (hLo : r^2 • (1:Matrix d d ℝ)≤A x) (v : E) :
    (2*r)^2*frobeniusSq (fderiv ℝ (fun y ↦ CFC.sqrt (A y)) x v)≤frobeniusSq (fderiv ℝ A x v) := by
  have hs : (CFC.sqrt (A x))ᵀ=CFC.sqrt (A x) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (A x)).posSemidef.isHermitian.eq
  have hh := MatrixSylvesterFrobenius.lower (CFC.sqrt (A x)) (CFC.sqrt (A x))
    (fderiv ℝ (fun y ↦ CFC.sqrt (A y)) x v) r r (by linarith)
    (quadratic_lower (A x) r hr hLo) (by rw [hs]; exact quadratic_lower (A x) r hr hLo)
  rw [sylvester hA hp he v] at hh
  convert hh using 1 <;> ring

end SHEStochastic.MatrixSqrtDerivative
