module

public import SHE.FullResidualInterpolatedWeightedMoments
public import SHE.JointInterpolationFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace SHE.ActualInterpolatedMeanFields
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance fullResidualInterpolatedWeightedLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance fullResidualInterpolatedWeightedLocal12 : MeasurableSpace RealL2 := borel _
local instance fullResidualInterpolatedWeightedLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal14 : MeasurableSpace CircleL2 := borel _
local instance fullResidualInterpolatedWeightedLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance fullResidualInterpolatedWeightedLocal17 : MeasurableSpace RealHaarInput := borel _
local instance fullResidualInterpolatedWeightedLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullResidualInterpolatedWeightedLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) X 1)


/-- The literal actual joint theta mean is jointly Borel in the sample
and original physical history, before any spatial sections are taken. -/
theorem actual_mean_measurable (k : ℕ) (q : ℝ≥0) :
    Measurable (fun z : Ω×History X k=>FullResidualInterpolatedWeightedMoments.actualMean
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q z.1 z.2) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  exact JointInterpolationAlgebra.current_variable_measurable (carrier L k).observations
    Λ q θ (S.first q) (S.second q) hU hV

end SHE.ActualInterpolatedMeanFields
