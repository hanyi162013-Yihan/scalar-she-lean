module

public import SHE.MixedNativePairedReferenceEnergy
public import SHE.PastReferenceBandFrequency
public import SHE.PastReferenceEnergy
public import SHE.MixedNativePairedReferenceHilbert
public import SHE.PastReferenceComparisonSection
public import SHE.PastReferenceMeanTheta
public import SHE.PastReferenceThreeLeg
public import SHE.PastReferenceMeanRealization
public import SHE.PastReferenceCovarianceSection
public import SHE.PastReferenceBaselineSection
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

namespace SHE.MixedNativePairedReferenceRate
open Real
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonSection_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonSection_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonSection_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonSection_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonSection_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonSection_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonSection_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonSection_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonSection_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonSection_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

def endpointDifference (k : ℕ) (v s : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 1 (v+s) z-
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 0 (v+s) z

local notation "End"=>endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x i,(Z.observations x i).stop≤(h:ℝ))
variable (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
local notation "RS" v=>(fun x=>by
  change (Z.observations x 0).stop+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [le_antisymm (hrootStop x 0) (hstop x 0),NNReal.coe_add,add_comm])
local notation "RT" v=>(fun x=>by
  change (Z.observations x 0).target+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [hrootTarget x 0,NNReal.coe_add,add_comm])
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Ref"=>MixedNativePairedReferenceEnergy.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ
include haP htarget hnull hJ hAs hL in
/-- The actual past endpoint is included in the sharp three-leg energy
bound. Only the positive root span is used; there is no singular
current-increment estimate at zero. -/
theorem actual_band_energy (hA:P.coefficient=(fun z=>κ+aV z))(hlocal:StandardTerminalPastLocality J)
    (hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(k:ℕ)
    (hfresh:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (A ν:ℝ)(hAmp:0≤A)(hν:1≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤(A*ν^(-P.exponent))*ν^j)
    (χ:ℝ)(hχ0:0≤χ)(hχ1:χ<1)(p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (hρpos:0<ρ)(hρhalf:ρ<1/2)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)
    (v:ℝ≥0)(hvH:v+h≤H)(hh:0<h)
    (hwindow:(h:ℝ)=NativeBandFrequencyRates.window P.exponent ν)(η:ℝ)(hη:0<η):
    let ell0:=fraction P*P.lower
    let Cs:=PhysicalScoreChain.uniformConstant 1
    let Tc:=TerminalCovarianceBudget.constant P ell0 Cs k η
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)
    let Ccov:=(PastCovarianceRMS.coefficient P k CG)^2*(Tc/MarkedProfileTimeFactors.freshDegree P)^2
    let Cbase:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
      (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*BaselineOriginalGain.unitCoefficient P^2*(Tc/(3/4:ℝ))^2
    let N:=(2*p)*(k+2)
    let CGm:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let Km:=PastMeanRMS.coefficient P k ρ (((CD+CGm)/2)^(1/(p:ℝ)))
    let Cmean:=Km^2*((4:ℝ)^ε)^2*(Tc/(1/2-ε))^2
    let Ev:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
    (∫⁻ω,ENNReal.ofReal (‖Ref k (v,ω)‖^2) ∂μ)≤
      ENNReal.ofReal (3*A^2*(2:ℝ)^(2*η)*
        (Λ^(-ρ)*Ev*(Ccov*ν^(-PastReferenceBandFrequency.covarianceDegree P.exponent k η)+
          Cbase*ν^(-PastReferenceBandFrequency.baselineDegree P.exponent k η))+
        Λ^(-2*ε)*Cmean*Ev^χ*ν^(-PastReferenceBandFrequency.meanDegree P.exponent ρ ε k η))):=by
  intro ell0 Cs Tc CG Ccov Cbase N CGm CD Km Cmean Ev
  have hνp:0<ν:=zero_lt_one.trans_le hν
  have hell0:0<ell0:=mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hCs:∀j,0≤Cs j:=fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le
  have hEv:0≤Ev:=integral_nonneg (fun _=>sq_nonneg _)
  have he:=MixedNativePairedReferenceEnergy.actual_past_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ hA hlocal hH hsmallPoint hsmallL2
    hages hcenter hspan k hfresh hold (A*ν^(-P.exponent)) ν
    (mul_nonneg hAmp (rpow_nonneg hνp.le _)) (zero_le_one.trans hν) hjet χ hχ0 hχ1 p hp horder
    Bpast Babs B0 hBDGpast hBDGabs hBDG hρpos hρhalf ε hε hεhalf v hvH hh
  have hcB:=PastReferenceBandFrequency.weighted_square_bound P hell0 Cs hCs k
    (MarkedProfileTimeFactors.freshDegree_pos P) hη hAmp hν 0
  have hbB:=PastReferenceBandFrequency.weighted_square_bound P hell0 Cs hCs k
    (by norm_num:(0:ℝ)<3/4) hη hAmp hν 0
  have hmB:=PastReferenceBandFrequency.weighted_square_bound P hell0 Cs hCs k
    (by linarith:(0:ℝ)<1/2-ε) hη hAmp hν ρ
  rw [←hwindow] at hcB hbB hmB
  simp only [rpow_zero,one_mul,PastReferenceBandFrequency.covariance_degree,
    MarkedProfileTimeFactors.freshDegree] at hcB
  simp only [rpow_zero,one_mul,PastReferenceBandFrequency.baseline_degree] at hbB
  rw [PastReferenceBandFrequency.mean_degree] at hmB
  let Bc:=MovingProfileBudget.covariance P ell0 Cs k h (A*ν^(-P.exponent)) ν 0
  let Bb:=MovingProfileBudget.baseline P ell0 Cs k h (A*ν^(-P.exponent)) ν 0
  let Bm:=QuarterRMSTimeFactors.oldTimeBudget P ell0 Cs k h 0 (1/2-ε) (A*ν^(-P.exponent)) ν
  let Rc:=A^2*(Tc/MarkedProfileTimeFactors.freshDegree P)^2*(2:ℝ)^(2*η)*
    ν^(-PastReferenceBandFrequency.covarianceDegree P.exponent k η)
  let Rb:=A^2*(Tc/(3/4:ℝ))^2*(2:ℝ)^(2*η)*
    ν^(-PastReferenceBandFrequency.baselineDegree P.exponent k η)
  let Rm:=A^2*(Tc/(1/2-ε))^2*(2:ℝ)^(2*η)*
    ν^(-PastReferenceBandFrequency.meanDegree P.exponent ρ ε k η)
  have hcR:Bc^2≤Rc:=by
    simpa only [Bc,Rc,Tc,MovingProfileBudget.covariance,MarkedProfileTimeFactors.freshDegree] using hcB
  have hbR:Bb^2≤BaselineOriginalGain.unitCoefficient P^2*Rb:=by
    by_cases hk:k=0
    · simp only [Bb,MovingProfileBudget.baseline,if_pos hk,zero_pow (by decide:(2:ℕ)≠0)]
      dsimp only [Rb]
      positivity
    · rw [show Bb=BaselineOriginalGain.unitCoefficient P*
        QuarterRMSTimeFactors.oldTimeBudget P ell0 Cs k h 0 (3/4:ℝ) (A*ν^(-P.exponent)) ν by
          simp only [Bb,MovingProfileBudget.baseline,if_neg hk],mul_pow]
      exact mul_le_mul_of_nonneg_left hbB (sq_nonneg _)
  have hmR:(h:ℝ)^ρ*Bm^2≤Rm:=hmB
  let Cv:=PastCovarianceRMS.coefficient P k CG
  let Cb:=MixedPastBaselineRMS.momentConstant P k
    ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
    (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2
  have hCb:0≤Cb:=mul_nonneg (MixedPastBaselineRMS.momentConstant_nonneg P k _) (sq_nonneg _)
  have hcS:=mul_le_mul_of_nonneg_left hcR (mul_nonneg (sq_nonneg Cv) hEv)
  have hbS:=mul_le_mul_of_nonneg_left hbR (mul_nonneg hCb hEv)
  have hmS:=mul_le_mul_of_nonneg_left hmR
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg Km) (rpow_nonneg hEv χ))
      (sq_nonneg ((4:ℝ)^ε))) (rpow_nonneg (zero_le_one.trans hL) (-2*ε)))
  have hhR:0<(h:ℝ):=by exact_mod_cast hh
  have hhsq:((h:ℝ)^(ρ/2))^2=(h:ℝ)^ρ:=by
    rw [←rpow_mul_natCast hhR.le]
    congr 1
    ring
  have hEsq:(Ev^(χ/2))^2=Ev^χ:=by
    rw [←rpow_mul_natCast hEv]
    congr 1
    ring
  have hLsq:(Λ^(-ε))^2=Λ^(-2*ε):=by
    rw [←rpow_mul_natCast (zero_le_one.trans hL)]
    congr 1
    ring
  have hMean:(Km*(h:ℝ)^(ρ/2)*Ev^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*Bm)^2≤
      (Km^2*Ev^χ*((4:ℝ)^ε)^2*Λ^(-2*ε))*Rm:=by
    convert! hmS using 1 <;> simp only [mul_pow,hhsq,hEsq,hLsq] <;> ring
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hsum:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hcS hbS)
      (rpow_nonneg (zero_le_one.trans hL) (-ρ))) hMean) (by norm_num:(0:ℝ)≤3)
  convert! hsum using 1 <;>
    dsimp only [Cv,Cb,Bc,Bb,Bm,Rc,Rb,Rm,Ccov,Cbase,Cmean,CG,CGm,CD,Km,N,ell0,Cs,Tc,Ev] <;>
    ring

end SHE.MixedNativePairedReferenceRate
