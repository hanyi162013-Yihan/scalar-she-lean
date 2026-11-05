module

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

namespace SHE.PastReferenceEnergy
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

include hIJ₀ hIJ₁ in
/-- The actual past endpoint is included in the sharp three-leg energy
bound. Only the positive root span is used; there is no singular
current-increment estimate at zero. -/
theorem actual_section_energy (hlocal:StandardTerminalPastLocality J)(hΛ:0<Λ)
    (hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(k:ℕ)
    (hfresh:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ:ℝ)(hχ0:0≤χ)(hχ1:χ<1)(p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)
    (v s:ℝ≥0)(hvH:v+h≤H)(hs:0≤s)(hsh:s<h):
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)
    let Ev:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
    let Ccov:=(PastCovarianceRMS.coefficient P k CG)^2*
      (MovingProfileBudget.covariance P (fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1) k h A0 ν s)^2*Ev
    let Cbase:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
      (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*
      (MovingProfileBudget.baseline P (fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1) k h A0 ν s)^2*Ev
    let N:=(2*p)*(k+2)
    let CGm:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let Km:=PastMeanRMS.coefficient P k ρ (((CD+CGm)/2)^(1/(p:ℝ)))
    let Eq:=∫ω,‖S.second (v+s) ω-S.first (v+s) ω‖^2 ∂μ
    let Cmean:=(Km*((h:ℝ)-s)^(ρ/2)*Eq^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
      QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1)
        k h s (1/2-ε) A0 ν)^2
    (∫⁻ω,ENNReal.ofReal (NativeFourierAverage.scalarEnergy mass ρ
      (fun x=>Complex.ofReal (End k v s (ω,x)))) ∂μ)≤
      ENNReal.ofReal (3*(mass^(-ρ)*(Ccov+Cbase)+Cmean)):=by
  intro CG Ev Ccov Cbase N CGm CD Km Eq Cmean
  have hc:=PastReferenceCovarianceSection.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet
    Bpast hBDGpast Babs hBDGabs v s hvH hs hsh
  have hb:=PastReferenceBaselineSection.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet
    Bpast hBDGpast Babs hBDGabs v s hvH hs hsh
  have hm:=PastReferenceMeanTheta.actual_theta_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf ε hε hεhalf v s hvH hs hsh
  have he:=PastReferenceComparisonSection.actual_comparison 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    χ hχ0 hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG mass ρ hmass hρ hρhalf v s hvH hs hsh
  let c:Ω→ℝ:=fun ω=>∫x,|CT k (v,(s,(ω,x)))|^2 ∂AddCircle.haarAddCircle
  let b':Ω→ℝ:=fun ω=>∫x,|BT k (v,(s,(ω,x)))|^2 ∂AddCircle.haarAddCircle
  let m:Ω→ℝ:=fun ω=>‖Avg k mass ρ hmass hρ.le (v,(s,ω))‖^2
  have hci:Integrable c μ:=hc.1.integral_prod_left
  have hbi:Integrable b' μ:=hb.1.integral_prod_left
  have hmi:Integrable m μ:=hm.1
  let U:Ω→ℝ:=fun ω=>3*(mass^(-ρ)*(c ω+b' ω)+m ω)
  have hui:Integrable U μ:=(((hci.add hbi).const_mul (mass^(-ρ))).add hmi).const_mul 3
  have hu0:∀ω,0≤U ω:=by
    intro ω
    dsimp [U,c,b',m]
    positivity
  calc
    _≤∫⁻ω,ENNReal.ofReal (U ω) ∂μ:=lintegral_mono_ae
      (he.mono (fun ω hω=>ENNReal.ofReal_le_ofReal hω.2))
    _=ENNReal.ofReal (∫ω,U ω ∂μ):=(ofReal_integral_eq_lintegral_ofReal hui (ae_of_all _ hu0)).symm
    _≤_:=by
      apply ENNReal.ofReal_le_ofReal
      have hcB:(∫ω,c ω ∂μ)≤Ccov:=by rw [←integral_prod _ hc.1];exact hc.2
      have hbB:(∫ω,b' ω ∂μ)≤Cbase:=by rw [←integral_prod _ hb.1];exact hb.2
      have hmB:(∫ω,m ω ∂μ)≤Cmean:=hm.2
      change (∫ω,3*(mass^(-ρ)*(c ω+b' ω)+m ω) ∂μ)≤_
      have hsum:Integrable (fun ω=>mass^(-ρ)*(c ω+b' ω)) μ:=by
        simpa only [Pi.add_apply] using (hci.add hbi).const_mul (mass^(-ρ))
      have hadd:(∫ω,c ω+b' ω ∂μ)=(∫ω,c ω ∂μ)+(∫ω,b' ω ∂μ):=by
        simpa only [Pi.add_apply] using integral_add hci hbi
      rw [integral_const_mul,integral_add hsum hmi,integral_const_mul,hadd]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hcB hbB) (by positivity)) hmB) (by norm_num)

end SHE.PastReferenceEnergy

