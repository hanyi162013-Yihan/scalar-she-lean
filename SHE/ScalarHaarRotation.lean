module
public import SHE.ScalarHaarSplitting
public import SHE.SmoothApproximation
public import SHE.PredictableScalarField
public import SHE.NoiseSplittingMeasurable
public import SHE.HaarInnovationInverse
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ScalarHaarRotation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance (ell M : ℝ) : MeasurableSpace (EllipticField ell M) := Subtype.instMeasurableSpace
local instance (ell M : ℝ) : BorelSpace (EllipticField ell M) := by infer_instance
variable (D : SmoothApproximation.ScalarData)

def amplitude : ℝ := ScalarReduction.additiveAmplitude D.lower

theorem amplitude_pos : 0 < amplitude D := by
  exact div_pos D.lower_pos (by norm_num)

def scalar (u : RealL2) (y : UnitAddCircle) : ℝ :=
  D.coefficient (PredictableScalarField.unitField (fun u : RealL2 => u) (u,y))

theorem scalar_joint : Measurable (Function.uncurry (scalar D)) :=
  (ScalarReduction.holder_continuous D.exponent_pos D.holder_nonneg D.holder_bound).measurable.comp
    (PredictableScalarField.unitField_measurable measurable_id)

theorem scalar_measurable (u : RealL2) : AEStronglyMeasurable (scalar D u) haarAddCircle :=
  ((scalar_joint D).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem scalar_gap (u : RealL2) : ∀ᵐy∂haarAddCircle, amplitude D ≤ |scalar D u y| := by
  apply ae_of_all
  intro y
  have hb := (D.bounds (PredictableScalarField.unitField (fun u : RealL2 => u) (u,y))).1
  change D.lower/2 ≤ _
  exact (by linarith [D.lower_pos] : D.lower/2 ≤ D.lower).trans hb

theorem scalar_bound (u : RealL2) : ∀ᵐy∂haarAddCircle, |scalar D u y| ≤ D.upper :=
  ae_of_all _ (fun y => (D.bounds _).2)

def residual (u : RealL2) : EllipticField D.ell D.cap :=
  NonlinearHaarIntegrand.coefficientField D.residualCoefficient D.residual_continuous.measurable
    D.ell D.cap D.ell_pos D.residual_bounds u

theorem residual_measurable : Measurable (residual D) :=
  NonlinearHaarIntegrand.coefficientField_measurable D.residual_continuous.measurable D.ell_pos
    D.residual_bounds D.beta_pos D.holderConstant_nonneg D.residual_holder

theorem residual_variance (u : RealL2) :
    ∀ᵐy∂haarAddCircle, ((residual D u).1 y).re = (scalar D u y)^2-(amplitude D)^2 := by
  filter_upwards [CoefficientFields.coefficient_ae D.residualCoefficient D.residual_continuous.measurable
    D.cap (NonlinearHaarIntegrand.absBound D.ell_pos D.residual_bounds) u,
    PredictableScalarField.unitField_ae (fun u : RealL2 => u) u] with y hf hu
  change (CoefficientFields.coefficient D.residualCoefficient D.residual_continuous.measurable
    D.cap (NonlinearHaarIntegrand.absBound D.ell_pos D.residual_bounds) u y).re = _
  rw [hf]
  dsimp only [scalar]
  rw [hu]
  rfl

def rotation (u : RealL2) : Both RealHaarInput ≃ₗᵢ[ℝ] Both RealL2 :=
  ScalarHaarSplitting.rotation D.ell_pos (residual D u) (scalar D u) (scalar_measurable D u)
    (amplitude D) (amplitude_pos D) (scalar_gap D u)

end SHE.ScalarHaarRotation
