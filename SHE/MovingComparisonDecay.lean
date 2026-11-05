module

public import SHE.MovingComparisonL2
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

namespace SHE.MovingComparisonDecay
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonDecay_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonDecay_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonDecay_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonDecay_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonDecay_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonDecay_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonDecay_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonDecay_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonDecay_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonDecay_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

def decayCost (k : ℕ) (ρ χ : ℝ) (p : ℕ) (Babs B0 : ℝ≥0) (ε η : ℝ) : ℝ:=
    let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)
    let Ccov:=(PastCovarianceRMS.coefficient P k CG)^2*
      PastMeanTimeFactors.assignmentFrequencyConstant P (fraction P*P.lower) (uniformConstant 1) k 0 h (MarkedProfileTimeFactors.freshDegree P) 1 η*Mglobal
    let Cbase:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
      (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*
      PastBaselineNativeBudget.frequencyConstant P (fraction P*P.lower) (uniformConstant 1) k h η*Mglobal
    let N:=(2*p)*(k+2)
    let CGm:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let Km:=PastMeanRMS.coefficient P k ρ (((CD+CGm)/2)^(1/(p:ℝ)))
    let Cmean:=(Km*(4:ℝ)^ε)^2*
      PastMeanTimeFactors.assignmentFrequencyConstant P (fraction P*P.lower) (uniformConstant 1)
        k ρ h (1/2-ε) 1 η*Mglobal^χ*(H:ℝ)^(1-χ)
    3*(|Ccov|+|Cbase|)+3*|Cmean|

theorem mixed_decay {L ρ ε : ℝ} (hL : 1≤L) (hερ : 2*ε≤ρ) (x y z : ℝ) :
    |3*L^(-ρ)*(x+y)+3*L^(-2*ε)*z|≤
      L^(-2*ε)*(3*(|x|+|y|)+3*|z|) := by
  have ha : 0≤3*L^(-ρ):=by positivity
  have hb : 0≤3*L^(-2*ε):=by positivity
  have hp : L^(-ρ)≤L^(-2*ε):=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc
    _≤|3*L^(-ρ)*(x+y)|+|3*L^(-2*ε)*z|:=abs_add_le _ _
    _=3*L^(-ρ)*|x+y|+3*L^(-2*ε)*|z|:=by
      rw [abs_mul,abs_of_nonneg ha,abs_mul,abs_of_nonneg hb]
    _≤3*L^(-ρ)*(|x|+|y|)+3*L^(-2*ε)*|z|:=
      add_le_add (mul_le_mul_of_nonneg_left (abs_add_le x y) ha) le_rfl
    _≤3*L^(-2*ε)*(|x|+|y|)+3*L^(-2*ε)*|z|:=by
      gcongr
    _=_:=by ring

theorem cost_decay (hΛ : 1≤Λ) (k : ℕ) (ρ χ : ℝ) (p : ℕ) (Babs B0 : ℝ≥0)
    (ε η : ℝ) (hερ : 2*ε≤ρ) :
    MovingComparisonL2.cost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
      k Λ ρ χ p Babs B0 ε η≤Λ^(-2*ε)*
        decayCost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h k ρ χ p Babs B0 ε η := by
  let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  let CG:=MixedPastWordMoments.momentConstant P k k 1
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)
  let Ccov:=(PastCovarianceRMS.coefficient P k CG)^2*
    PastMeanTimeFactors.assignmentFrequencyConstant P (fraction P*P.lower) (uniformConstant 1)
      k 0 h (MarkedProfileTimeFactors.freshDegree P) 1 η*Mglobal
  let Cbase:=MixedPastBaselineRMS.momentConstant P k
    ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
    (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*
    PastBaselineNativeBudget.frequencyConstant P (fraction P*P.lower) (uniformConstant 1) k h η*Mglobal
  let N:=(2*p)*(k+2)
  let CGm:=MixedPastWordMoments.momentConstant P k k (2*p)
    ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
  let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
  let Km:=PastMeanRMS.coefficient P k ρ (((CD+CGm)/2)^(1/(p:ℝ)))
  let Cmean:=(Km*(4:ℝ)^ε)^2*
    PastMeanTimeFactors.assignmentFrequencyConstant P (fraction P*P.lower) (uniformConstant 1)
      k ρ h (1/2-ε) 1 η*Mglobal^χ*(H:ℝ)^(1-χ)
  have he:=mixed_decay hΛ hερ Ccov Cbase Cmean
  convert! he using 1 <;> dsimp only [MovingComparisonL2.cost,decayCost]
  congr 1
  ring

end SHE.MovingComparisonDecay
