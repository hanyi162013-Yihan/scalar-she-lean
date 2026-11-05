module

public import SHEStochastic.NativeMatrixSquareRealization
public import SHEStochastic.MatrixMildCovarianceCongruence
public import SHEStochastic.MatrixFourierNoiseRows
public import SHEStochastic.MatrixFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixEqualCovarianceRotation
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (G K : MatrixNonlinearCoefficient.Coefficient d) (hCov : ∀ z,G.covariance z=K.covariance z)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)

/-- The original square factor is placed over exactly the reference
covariance profile, retaining its actual spatial coefficient. -/
def data (p : ℝ≥0×Ω) : MatrixSquareCoefficient.Data (NativeMatrixEquation.profile F K U hU p) where
  value := (NativeMatrixEquation.data F G U hU p).value
  measurable := (NativeMatrixEquation.data F G U hU p).measurable
  bound := (NativeMatrixEquation.data F G U hU p).bound
  norm_bound := (NativeMatrixEquation.data F G U hU p).norm_bound
  covariance_ae := by
    filter_upwards [(NativeMatrixEquation.data F G U hU p).covariance_ae,
      MatrixMildCovarianceCongruence.profile_ae F G K hCov U hU p] with x hg hk
    exact hg.trans hk

/-- One predictable unitary carries original-square noise rows to the
reference-square rows; it is independent of every terminal horizon. -/
def rotation (p : ℝ≥0×Ω) : Input (d := d) →ₗᵢ[ℝ] Input (d := d) :=
  (NativeMatrixCoefficient.isometry (NativeMatrixEquation.profile F K U hU)
    (NativeMatrixEquation.data F K U hU) p).comp
      (NativeMatrixSquareRealization.forward (NativeMatrixEquation.profile F K U hU) (data F G K hCov U hU) p)

private theorem measurable_comp {Z : Type*} [MeasurableSpace Z]
    (A B : Z → Input (d := d) →ₗᵢ[ℝ] Input (d := d))
    (ha : Measurable (fun z : Z×Input (d := d) => A z.1 z.2))
    (hb : Measurable (fun z : Z×Input (d := d) => B z.1 z.2)) :
    Measurable (fun z : Z×Input (d := d) => (A z.1).comp (B z.1) z.2) :=
  ha.comp (measurable_fst.prodMk hb)

set_option backward.isDefEq.respectTransparency true in
theorem measurable :
    @Measurable ((ℝ≥0×Ω)×Input (d := d)) (Input (d := d))
      (F.predictable.prod (borel _)) (borel _) (fun z => rotation F G K hCov U hU z.1 z.2) := by
  have hdata : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (data F G K hCov U hU z.1).value z.2) := by
    change @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance
      (fun z => (NativeMatrixEquation.data F G U hU z.1).value z.2)
    exact NativeMatrixEquation.coefficient_measurable F G U hU
  have hf := NativeMatrixSquareRealization.measurable F (NativeMatrixEquation.profile F K U hU)
    (data F G K hCov U hU) (NativeMatrixEquation.profile_measurable F K U hU)
    hdata
  have hi := NativeMatrixCoefficient.measurable F (NativeMatrixEquation.profile F K U hU)
    (NativeMatrixEquation.data F K U hU) (NativeMatrixEquation.profile_measurable F K U hU)
    (NativeMatrixEquation.coefficient_measurable F K U hU)
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact measurable_comp
    (NativeMatrixCoefficient.isometry (NativeMatrixEquation.profile F K U hU) (NativeMatrixEquation.data F K U hU))
    (NativeMatrixSquareRealization.forward (NativeMatrixEquation.profile F K U hU) (data F G K hCov U hU)) hi hf

theorem factor (p : ℝ≥0×Ω) (v : Physical (d := d)) :
    rotation F G K hCov U hU p ((data F G K hCov U hU p).factor.adjoint v)=
      (NativeMatrixEquation.data F K U hU p).factor.adjoint v := by
  change (NativeMatrixEquation.data F K U hU p).rotation.symm
    ((data F G K hCov U hU p).rotation ((data F G K hCov U hU p).factor.adjoint v))=_
  rw [←(data F G K hCov U hU p).reconstruct_adjoint v,LinearIsometryEquiv.apply_symm_apply]
  exact (NativeMatrixEquation.data F K U hU p).reconstruct_adjoint v

/-- The unitary identifies the actual Fourier noise rows on any finite
horizon; no small-time analytic heat estimate is needed. -/
theorem row {C β D γ : ℝ≥0} (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1)
    (hK : HolderWith D γ K.value) (hγ : 0<γ) (hγ1 : γ≤1)
    (H : ℝ≥0) (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0×Ω) :
    rotation F G K hCov U hU p (MatrixFourierInput.row H G hG hβ hβ1 U i a n p)=
      MatrixFourierInput.row H K hK hγ hγ1 U i a n p := by
  unfold MatrixFourierInput.row
  rw [map_smul,←MatrixFourierNoiseRows.factor_test G hG hβ hβ1 (data F G K hCov U hU p) (U p)
    (NativeMatrixEquation.coefficient_ae F G U hU p) i a n,factor,
    MatrixFourierNoiseRows.factor_test K hK hγ hγ1 (NativeMatrixEquation.data F K U hU p) (U p)
      (NativeMatrixEquation.coefficient_ae F K U hU p) i a n]

end SHEStochastic.MatrixEqualCovarianceRotation
