module

public import SHE.NativeNegativeRealization
public import SHE.MovingComparisonFrequency
public import SHE.MovingComparisonGlobal
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

namespace SHE.MovingComparisonHilbert
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonHilbert_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonHilbert_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonHilbert_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonHilbert_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonHilbert_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonHilbert_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonHilbert_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonHilbert_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonHilbert_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonHilbert_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

local notation "End"=>MovingComparisonSection.endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "CF"=>MovingMarkRootTheta.covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BF"=>MovingMarkRootTheta.baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "MF"=>MovingMeanPhysicalField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

def scalarField (k : ℕ) (z : (ℝ×(ℝ×Ω))×HeatCircle) : ℂ:=
  Complex.ofReal (MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm k (z.1.1,(z.1.2.1,(z.1.2.2,z.2))))
local notation "Scalar"=>scalarField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

def field (k : ℕ) (mass ρ : ℝ) (z : ℝ×(ℝ×Ω)) : CircleL2:=
  NativeNegativeRealization.value mass ρ (Scalar k) z
local notation "Out"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem scalarField_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (Scalar k) :=
  Complex.continuous_ofReal.measurable.comp
    ((MovingComparisonField.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm hΛ hsmall k).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
          (measurable_fst.snd.snd.prodMk measurable_snd))))

theorem field_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (mass ρ : ℝ) : Measurable (Out k mass ρ) :=
  NativeNegativeRealization.value_measurable mass ρ _
    (scalarField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ hsmall k)

theorem field_norm_sq (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (z : ℝ×(ℝ×Ω)) :
    ‖Out k mass ρ z‖^2=MovingComparisonField.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k mass ρ z:=
  NativeNegativeRealization.value_norm_sq mass ρ hmass _ z

theorem field_fourier (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (z : ℝ×(ℝ×Ω))
    (hs : Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x=>Scalar k (z,x)) n‖^2)) (n : ℤ) :
    fourierCoeff (Out k mass ρ z) n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x=>Scalar k (z,x)) n :=
  NativeNegativeRealization.value_fourier mass ρ hmass _ z hs n

end SHE.MovingComparisonHilbert

