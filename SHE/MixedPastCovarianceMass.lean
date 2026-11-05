module

public import SHE.MixedPastCovarianceInputMoments
public import SHE.PointwiseSignedGaussianWord
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastCovarianceMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceMass_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceMass_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceMass_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceMass_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceMass_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceMass_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile

variable (θ : ℝ)

local instance mixedPastCovarianceMass_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceMass_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

/-- The true full-residual canonical score mass is measurable in the
observed past, despite varying Gaussian rank and covariance. The signed
profile input is only required to be jointly past measurable; no
conditional Gaussian law or selection of generalized inverses is used. -/
theorem past_measurable (νX : Measure X) [SFinite νX]
    (P : CanonicalCovariance.ProfileParameters) (v q : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (row : X→State n) (hrow : Measurable row) (e : Ω×X→ℝ)
    (he : @Measurable (Ω×X) ℝ ((𝓕 v).prod ‹MeasurableSpace X›) inferInstance e) :
    Measurable[𝓕 v] (fun ω=>∫ x,|e (ω,x)| *scoreVariance
      (ControlledFixedReserve.covariance P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (fixedProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) lo hi)
        σ target center ((q:ℝ)-(v:ℝ)) θ) (row x) ∂νX) := by
  have hU := MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hdir := MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  letI : MeasurableSpace Ω := 𝓕 v
  have hB := VaryingControlledGaussianFields.residual_covariance_measurable P Λ θ ((q:ℝ)-(v:ℝ))
    _ _ hU hdir σ target center lo hi
  have hV := scoreVariance_measurable.comp ((hB.comp measurable_fst).prodMk (hrow.comp measurable_snd))
  exact (((continuous_abs.measurable.comp he).mul hV).stronglyMeasurable.integral_prod_right').measurable

end SHE.MixedPastCovarianceMass

