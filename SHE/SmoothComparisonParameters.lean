module

public import SHE.ControlledSmoothLimit
public import SHE.MovingComparisonDecay
public import SHE.MovingComparisonRoughEnergy
public import SHE.HilbertSquareMass
public import SHE.MovingMarkFrequencyBudget
public import SHE.MovingComparisonField
public import SHE.ThreeLegEnergyIntegration
public import SHE.MovingComparisonSection
public import SHE.MovingMarkRootGlobalEnergy
public import SHE.MovingMeanGlobalL2
public import SHE.NegativeThreeLeg
public import SHE.MixedPastMeanRootL1
public import SHE.MovingRootThreeLeg
public import SHE.MovingMeanRootRealization
public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.SmoothComparisonParameters
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance smoothComparisonParameters_realSigma : MeasurableSpace RealL2 := borel _
local instance smoothComparisonParameters_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance smoothComparisonParameters_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance smoothComparisonParameters_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance smoothComparisonParameters_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance smoothComparisonParameters_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance smoothComparisonParameters_circleSigma : MeasurableSpace CircleL2 := borel _
local instance smoothComparisonParameters_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance smoothComparisonParameters_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance smoothComparisonParameters_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]

open SmoothApproximation ScalarData ControlledSmoothLimit GaussianProfile SmoothCylinders
variable (D : ScalarData) {T0 : ℝ} (hT0 : 0<T0) (hT1 : T0≤1)
variable (hsmall : contractionConstant D.ell D.holderConstant D.beta*T0^(D.beta/4)≤1/2)

abbrev smooth (n : ℕ) : CanonicalCovariance.ProfileParameters:=smoothTotalParameters D hT0 hT1 hsmall n
abbrev rough : CanonicalCovariance.ProfileParameters:=roughTotalParameters D hT0 hT1 hsmall

theorem common_numbers (n : ℕ) :
    ((smooth D hT0 hT1 hsmall n).lower,(smooth D hT0 hT1 hsmall n).upper,
      (smooth D hT0 hT1 hsmall n).holder,(smooth D hT0 hT1 hsmall n).exponent,
        (smooth D hT0 hT1 hsmall n).horizon)=
    ((rough D hT0 hT1 hsmall).lower,(rough D hT0 hT1 hsmall).upper,
      (rough D hT0 hT1 hsmall).holder,(rough D hT0 hT1 hsmall).exponent,
        (rough D hT0 hT1 hsmall).horizon) := rfl

theorem smooth_bounded (n : ℕ) : BoundedSmooth (smooth D hT0 hT1 hsmall n).coefficient := by
  change BoundedSmooth (fun z=>(TotalSmoothLimit.amplitude D)^2+D.smoothCoefficient n z)
  simpa only [sub_neg_eq_add,add_comm] using
    (D.smooth_boundedSmooth n).sub (BoundedSmooth.const (-((TotalSmoothLimit.amplitude D)^2)))

/-- The entire actual rough-comparison constant is uniform in the
coefficient smoothing index, not just its ellipticity or Hölder pieces. -/
theorem decayCost_eq (n : ℕ) (h : ℝ≥0) (k : ℕ) (ρ χ : ℝ) (p : ℕ)
    (Babs B0 : ℝ≥0) (ε η : ℝ) :
    MovingComparisonDecay.decayCost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (smooth D hT0 hT1 hsmall n) h k ρ χ p Babs B0 ε η=
    MovingComparisonDecay.decayCost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (rough D hT0 hT1 hsmall) h k ρ χ p Babs B0 ε η := by
  rfl

theorem cost_eq (n : ℕ) (h : ℝ≥0) (k : ℕ) (mass ρ χ : ℝ) (p : ℕ)
    (Babs B0 : ℝ≥0) (ε η : ℝ) :
    MovingComparisonL2.cost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (smooth D hT0 hT1 hsmall n) h k mass ρ χ p Babs B0 ε η=
    MovingComparisonL2.cost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (rough D hT0 hT1 hsmall) h k mass ρ χ p Babs B0 ε η := by
  rfl

theorem controlled_profile_error (n : ℕ) (u d : CircleL2) (θ : ℝ) (z : ControlledProfile.Domain) :
    |ControlledProfile.profile (smooth D hT0 hT1 hsmall n) Λ u d (θ,z)-
      ControlledProfile.profile (rough D hT0 hT1 hsmall) Λ u d (θ,z)|≤SmoothReferenceLimit.error D n :=
  ControlledSmoothLimit.total_profile_error D hT0 hT1 hsmall n Λ u d θ z

end SHE.SmoothComparisonParameters



