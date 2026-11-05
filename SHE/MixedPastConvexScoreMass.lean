module

public import SHE.StoppedRandomScoreMass
public import SHE.BoundedResidualFields
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

namespace SHE.MixedPastConvexScoreMass
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

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

def value (P : CanonicalCovariance.ProfileParameters) (v : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (q : ℝ)
    (lo hi : Fin r→ℝ) (θ η ζ : ℝ) : Ω→ℝ :=
  StoppedRandomScoreMass.mass σ target center q
    (fun z=>BoundedWindowDecomposition.residual P Λ (U v z.1) (Dir v z.1) lo hi
      (BoundedWindowDecomposition.convexProfile P Λ (U v z.1) (Dir v z.1) θ η ζ) z.2)
    (fun z=>ControlledProfile.profile P Λ (U v z.1) (Dir v z.1) (θ,z.2)-
      ControlledProfile.profile P Λ (U v z.1) (Dir v z.1) (η,z.2))

/-- The real convex-law finite profile-difference score mass is measurable
in the observed past, before choosing any current native offset. -/
theorem past_measurable (P : CanonicalCovariance.ProfileParameters) (v : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (q : ℝ)
    (lo hi : Fin r→ℝ) (θ η ζ : ℝ) :
    Measurable[𝓕 v] (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P v σ target center q lo hi θ η ζ) := by
  have hu := MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hd := MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  letI : MeasurableSpace Ω := 𝓕 v
  have hc := (BoundedResidualFields.convexProfile_measurable P Λ θ η ζ _ _ hu hd).sub
    (VaryingControlledGaussianFields.fixed_profile_measurable P Λ _ _ hu hd lo hi)
  have he := (VaryingControlledGaussianFields.profile_measurable P Λ θ _ _ hu hd).sub
    (VaryingControlledGaussianFields.profile_measurable P Λ η _ _ hu hd)
  exact StoppedRandomScoreMass.mass_measurable σ target center q _ _ hc he

/-- All required past-mass powers are integrable through singular terminal
covariance and zero newest future age. Only the dimension/floor cap is
used here; the quantitative remainder keeps its actual score mass. -/
theorem power_integrable (P : CanonicalCovariance.ProfileParameters) (v : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (θ η : ℝ) {ζ : ℝ} (hζ : 0≤ζ) (hζ1 : ζ≤1) (k : ℕ) :
    Integrable (fun ω=>(value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P v σ target center q lo hi θ η ζ ω)^k) μ := by
  have hu := (MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hc := (BoundedResidualFields.convexProfile_measurable P Λ θ η ζ _ _ hu hd).sub
    (VaryingControlledGaussianFields.fixed_profile_measurable P Λ _ _ hu hd lo hi)
  have he := (VaryingControlledGaussianFields.profile_measurable P Λ θ _ _ hu hd).sub
    (VaryingControlledGaussianFields.profile_measurable P Λ η _ _ hu hd)
  apply StoppedRandomScoreMass.mass_pow_integrable μ σ target center hages q _ _ hc he
    (half_pos P.lower_pos)
    (fun ω z=>BoundedWindowDecomposition.residual_bounds P Λ (U v ω) (Dir v ω) lo hi hdisjoint _
      (BoundedWindowDecomposition.convexProfile_bounds P Λ (U v ω) (Dir v ω) θ η hζ hζ1) z)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) P.upper_nonneg) _ k
  intro ω z
  have hb (a : ℝ) : |ControlledProfile.profile P Λ (U v ω) (Dir v ω) (a,z)|≤P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans
      (ControlledProfile.profile_bounds P Λ (U v ω) (Dir v ω) (a,z)).1)]
    exact (ControlledProfile.profile_bounds P Λ (U v ω) (Dir v ω) (a,z)).2
  have hs : |ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ,z)-
      ControlledProfile.profile P Λ (U v ω) (Dir v ω) (η,z)|≤
      |ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ,z)|+
        |ControlledProfile.profile P Λ (U v ω) (Dir v ω) (η,z)| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ,z)) 0
        (ControlledProfile.profile P Λ (U v ω) (Dir v ω) (η,z))
  exact hs.trans ((add_le_add (hb θ) (hb η)).trans_eq (by ring))

end SHE.MixedPastConvexScoreMass
