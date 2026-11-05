module

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

namespace SHE.MovingComparisonEnergy
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

def endpointEnergy (k : ℕ) (mass ρ : ℝ) (v s : ℝ) (ω : Ω) : ℝ:=
  if MovingMeanPhysicalField.valid H h v s then
    NativeFourierAverage.scalarEnergy mass ρ (fun x=>Complex.ofReal (End k v.toNNReal s.toNNReal (ω,x))) else 0
local notation "EE"=>endpointEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Actual all-depth finite reference-tree three-leg comparison. The
literal endpoint difference is measured in massive spatial Fourier
energy; all original history and theta averages precede the square.
Covariance/baseline retain the true global input energy linearly, while
the correlated mean retains its Lambda decay and input power. -/
theorem actual_global_comparison (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (ε : ℝ) (hε : 0≤ε) (hερ : 2*ε<ρ) :
    let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)
    let Ccov:=(PastCovarianceRMS.coefficient P k CG)^2*
      MovingProfileBudget.covarianceMass P (fraction P*P.lower) (uniformConstant 1) k h A0 ν*Mglobal
    let Cbase:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
      (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*
      MovingProfileBudget.baselineMass P (fraction P*P.lower) (uniformConstant 1) k h A0 ν*Mglobal
    let N:=(2*p)*(k+2)
    let CGm:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let Km:=PastMeanRMS.coefficient P k ρ (((CD+CGm)/2)^(1/(p:ℝ)))
    let Cmean:=(Km*(4:ℝ)^ε)^2*Λ^(-2*ε)*
      PastMeanTimeFactors.assignmentMass P (fraction P*P.lower) (uniformConstant 1)
        k ρ h (1/2-ε) A0 ν*Mglobal^χ*(H:ℝ)^(1-χ)
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) (h:ℝ),
      ∫⁻ ω,ENNReal.ofReal (EE k mass ρ v s ω) ∂μ)≤
        ENNReal.ofReal (3*mass^(-ρ)*(Ccov+Cbase)+3*Cmean) := by
  intro Mglobal CG Ccov Cbase N CGm CD Km Cmean
  let α:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
  let β:=volume.restrict (Ioc (0:ℝ) (h:ℝ))
  have hc:=MovingMarkRootGlobalEnergy.covariance_global_L2 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hh hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet Bpast hBDGpast Babs hBDGabs
  have hb:=MovingMarkRootGlobalEnergy.baseline_global_L2 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hh hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet Bpast hBDGpast Babs hBDGabs
  have hm:=MovingMeanGlobalL2.actual_global_L2 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hh Bpast hBDGpast
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν.le hjet
    χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf ε hε hερ
  have hCm:=MovingMarkRootTheta.covarianceField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P P.coefficient haP h Z htarget hstop F hF hFm hΛ.le hsmallPoint k
  have hBm:=MovingMarkRootTheta.baselineField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P P.coefficient haP h Z htarget hstop F hF hFm hΛ.le hsmallPoint k
  have hMm:=MovingMeanPhysicalField.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hΛ.le k mass ρ hmass hρ.le
  have hsection : ∀ v s,∀ᵐ ω ∂μ,EE k mass ρ v s ω≤
      (3*mass^(-ρ))*((∫ x,‖CF k (v,(s,(ω,x)))‖^2 ∂haarAddCircle)+
        (∫ x,‖BF k (v,(s,(ω,x)))‖^2 ∂haarAddCircle))+
          3*‖MF k mass ρ hmass hρ.le (v,(s,ω))‖^2 := by
    intro v s
    by_cases hv : MovingMeanPhysicalField.valid H h v s
    · have hvH : v.toNNReal+h≤H := by exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) by rw [Real.toNNReal_of_nonneg hv.1];exact hv.2.2.2)
      have hs : (0:ℝ≥0)<s.toNNReal:=by exact_mod_cast (show (0:ℝ)<(s.toNNReal:ℝ) by rw [Real.toNNReal_of_nonneg hv.2.1.le];exact hv.2.1)
      have hsh : s.toNNReal<h:=by exact_mod_cast (show (s.toNNReal:ℝ)<(h:ℝ) by rw [Real.toNNReal_of_nonneg hv.2.1.le];exact hv.2.2.1)
      have he:=MovingComparisonSection.actual_comparison 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
        hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν.le hjet
        χ hχ0 hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG mass ρ hmass hρ hρhalf
        v.toNNReal s.toNNReal hvH hs hsh
      filter_upwards [he] with ω hω
      simpa only [endpointEnergy,if_pos hv,MovingMarkRootTheta.covarianceField,
        MovingMarkRootTheta.baselineField,MovingMeanPhysicalField.field,Real.norm_eq_abs,
        mul_add,mul_assoc] using hω.2
    · exact ae_of_all _ (fun ω=>by rw [endpointEnergy,if_neg hv];positivity)
  have hi:=ThreeLegEnergyIntegration.from_sections α β μ
    (fun z=>‖CF k z‖^2) (fun z=>‖BF k z‖^2) (fun z=>‖MF k mass ρ hmass hρ.le z‖^2)
    (hCm.norm.pow_const 2) (hBm.norm.pow_const 2) (hMm.norm.pow_const 2)
    hc.1 hb.1 hm.1 (fun _=>sq_nonneg _) (fun _=>sq_nonneg _) (fun _=>sq_nonneg _)
    (3*mass^(-ρ)) 3 (by positivity) (by norm_num) (EE k mass ρ) hsection
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hcB : (∫ z,‖CF k z‖^2 ∂α.prod (β.prod (μ.prod haarAddCircle)))≤Ccov:=hc.2
  have hbB : (∫ z,‖BF k z‖^2 ∂α.prod (β.prod (μ.prod haarAddCircle)))≤Cbase:=hb.2
  have hmB : (∫ z,‖MF k mass ρ hmass hρ.le z‖^2 ∂α.prod (β.prod μ))≤Cmean:=hm.2
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hcB hbB) (by positivity))
    (mul_le_mul_of_nonneg_left hmB (by norm_num))

end SHE.MovingComparisonEnergy

