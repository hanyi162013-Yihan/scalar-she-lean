module

public import SHE.MovingComparisonGlobal
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

namespace SHE.MovingComparisonFrequency
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonFrequency_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonFrequency_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonFrequency_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonFrequency_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonFrequency_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonFrequency_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonFrequency_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonFrequency_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonFrequency_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonFrequency_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

include hIJ₀ hIJ₁ in
/-- Actual all-depth finite reference-tree three-leg comparison. The
literal endpoint difference is measured in massive spatial Fourier
energy; all original history and theta averages precede the square.
Covariance/baseline retain the true global input energy linearly, while
the correlated mean retains its Lambda decay and input power. -/
theorem actual_frequency_comparison (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1) (hh : 0<h)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0<ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0 : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ε : ℝ) (hε : 0≤ε) (hερ : 2*ε<ρ) (η : ℝ) (hη : 0<η) :
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
    let Cmean:=(Km*(4:ℝ)^ε)^2*Λ^(-2*ε)*
      PastMeanTimeFactors.assignmentFrequencyConstant P (fraction P*P.lower) (uniformConstant 1)
        k ρ h (1/2-ε) 1 η*Mglobal^χ*(H:ℝ)^(1-χ)
    (∫⁻ z,ENNReal.ofReal (MovingComparisonField.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k mass ρ z)
      ∂(volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod ((volume.restrict (Ioc (0:ℝ) (h:ℝ))).prod μ))≤
        ENNReal.ofReal (A0^2*(1+ν)^η*(3*mass^(-ρ)*(Ccov+Cbase)+3*Cmean)) := by
  intro Mglobal CG Ccov Cbase N CGm CD Km Cmean
  have hglobal:=MovingComparisonGlobal.actual_product_comparison 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hh hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder
    Bpast Babs B0 hBDGpast hBDGabs hBDG mass ρ hmass hρ hρhalf ε hε hερ
  have hT : (h:ℝ)≤1:=hspan.trans P.horizon_le_one
  have hM : 0≤Mglobal:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  let Kc:=PastCovarianceRMS.coefficient P k CG
  let Kb:=MixedPastBaselineRMS.momentConstant P k
    ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
      (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2
  let Kmean:=(Km*(4:ℝ)^ε)^2*Λ^(-2*ε)*Mglobal^χ*(H:ℝ)^(1-χ)
  have hKb : 0≤Kb:=mul_nonneg (MixedPastBaselineRMS.momentConstant_nonneg P k _) (sq_nonneg _)
  have hKm : 0≤Kmean:=by dsimp only [Kmean];positivity
  have hcov:=MovingProfileBudget.covarianceMass_frequency P (fraction P*P.lower) (uniformConstant 1)
    k h A0 ν η (by exact_mod_cast hh) hT hν.le hη
  have hbase:=MovingProfileBudget.baselineMass_frequency P (fraction P*P.lower) (uniformConstant 1)
    k h A0 ν η (by exact_mod_cast hh) hT hν.le hη
  have hmean:=PastMeanTimeFactors.assignmentMass_frequency_bound P (fraction P*P.lower) (uniformConstant 1)
    k ρ h (1/2-ε) A0 η (by linarith) h.2 hT hη hν.le
  rw [PastMeanTimeFactors.assignmentFrequencyConstant_amplitude] at hmean
  have hc : Kc^2*MovingProfileBudget.covarianceMass P (fraction P*P.lower) (uniformConstant 1) k h A0 ν*Mglobal≤
      A0^2*(1+ν)^η*Ccov := by
    have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcov (sq_nonneg Kc)) hM
    convert! he using 1 <;> dsimp only [Ccov,Kc] <;> ring
  have hb : Kb*MovingProfileBudget.baselineMass P (fraction P*P.lower) (uniformConstant 1) k h A0 ν*Mglobal≤
      A0^2*(1+ν)^η*Cbase := by
    have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hKb) hM
    convert! he using 1 <;> dsimp only [Cbase,Kb] <;> ring
  have hm : (Km*(4:ℝ)^ε)^2*Λ^(-2*ε)*
      PastMeanTimeFactors.assignmentMass P (fraction P*P.lower) (uniformConstant 1) k ρ h (1/2-ε) A0 ν*
        Mglobal^χ*(H:ℝ)^(1-χ)≤A0^2*(1+ν)^η*Cmean := by
    have he:=mul_le_mul_of_nonneg_left hmean hKm
    convert! he using 1 <;> dsimp only [Kmean,Cmean] <;> ring
  apply hglobal.trans
  apply ENNReal.ofReal_le_ofReal
  have he:=add_le_add (mul_le_mul_of_nonneg_left (add_le_add hc hb)
    (show 0≤3*mass^(-ρ) by positivity)) (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤3))
  convert! he using 1 <;> (try dsimp only [Kc,Kb]) <;> ring

end SHE.MovingComparisonFrequency
