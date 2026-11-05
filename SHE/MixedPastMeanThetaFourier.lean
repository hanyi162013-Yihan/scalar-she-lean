module

public import SHE.MixedPastMeanThetaMass
public import SHE.MixedPastMeanAverageFourier
public import SHE.MixedNativeRootThreeLeg
public import SHE.MeanThetaAverage

public import SHE.FamilyMeanCoordinates
public import SHE.MixedPastMeanLegIdentity
public import SHE.NativeFourierAverage
public import SHE.MixedPastMeanSupport
public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget
public import SHE.MixedPastMeanFirstMoment
public import SHE.MixedPastBaselineFTCIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanThetaFourier
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanThetaFourier_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanThetaFourier_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanThetaFourier_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanThetaFourier_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanThetaFourier_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanThetaFourier_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanThetaFourier_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanThetaFourier_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanThetaFourier_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

local notation "Input"=>MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leg"=>MixedPastMeanLegIdentity.leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

local instance mixedPastMeanThetaFourier_secondCountable : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

def weightedAverage (k : ℕ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) (ω : Ω) : CircleL2:=
  ∫ θ,MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k
    (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) θ q mass ρ hmass hρ ω
    ∂MeanThetaAverage.thetaMeasure

include hIJ₀ hIJ₁ in
/-- Full interpolation and original history averaging preserve the exact
physical Fourier realization. Scalar L¹ and Hilbert integrability are
derived from actual moments before either average is exchanged. -/
theorem actual_theta_fourier (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (B0 Babs : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    ∀ᵐ ω ∂μ,∀ n,
      fourierCoeff (weightedAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k q mass ρ hmass hρ.le ω) n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff
        (fun x=>Complex.ofReal (MixedNativeRootThreeLeg.meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k q (ω,x))) n := by
  let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
  let V : ℝ×Ω→CircleL2:=fun z=>MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k old z.1 q mass ρ hmass hρ.le z.2
  let Raw:=MixedNativeRootLegMass.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  let G : ℝ×(Ω×HeatCircle)→ℝ:=fun z=>rootAverage (Ref (0,(0,0))) k (fun a=>Raw (z.1,a)) z.2
  have hVm : Measurable V:=MixedPastMeanFields.average_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ.le k old q mass ρ hmass hρ.le
  have hRaw :=MixedPastMeanThetaMass.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  have hGm : Measurable G:=thetaRootAverage_measurable (Ref (0,(0,0))) k Raw hRaw
  have hRawi:=MixedPastMeanThetaMass.actual_theta_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ.le hages hrootStop hrootTarget
    hspan k hfresh hold A0 ν hA0 hν hjet Babs hBDGabs q hvq hqb hqH hq1
  have hGi : Integrable G (MeanThetaAverage.thetaMeasure.prod (μ.prod haarAddCircle)):=
    thetaRootAverage_integrable (Ref (0,(0,0))) k MeanThetaAverage.thetaMeasure μ Raw hRawi
  let N:=(2*p)*(k+2)
  let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
    ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
  let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
  let C:=((CD+CG)/2)^(1/(p:ℝ))
  let K:=PastMeanRMS.coefficient P k ρ C*((b:ℝ)-q)^(ρ/2)
  let E:=∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ
  let RMS:=K*E^(χ/2)*((4:ℝ)^(0:ℝ)*Λ^(-(0:ℝ)))*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      k ((b:ℝ)-v) ((q:ℝ)-v) (1/2-(0:ℝ)) A0 ν
  have hs : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun ω=>‖V (θ,ω)‖^2) μ ∧ (∫ ω,‖V (θ,ω)‖^2 ∂μ)≤|RMS|^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=(MixedPastMeanAverage.actual_averaged_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget hcenter
      hspan k hfresh hold θ htθ A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 hBDG
      mass ρ hmass hρ hρhalf 0 (by rfl) (by norm_num) q hvq hqb hqH hq1).2
    simpa only [V,MixedPastMeanFields.average,old,N,CG,CD,C,K,E,RMS,sq_abs] using hh
  have hVi : Integrable V (MeanThetaAverage.thetaMeasure.prod μ):=
    (HilbertParameterAverage.energy μ MeanThetaAverage.thetaMeasure V hVm (fun _=>|RMS|)
      measurable_const (integrable_const _) (fun _=>abs_nonneg _) (hs.mono (fun _ h=>h.1))
      (hs.mono (fun _ h=>h.2))).1
  have hc : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,∀ᵐ ω ∂μ,∀ n,fourierCoeff (V (θ,ω)) n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x=>Complex.ofReal (G (θ,(ω,x)))) n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    exact MixedPastMeanAverageFourier.actual_average_fourier 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget hcenter
      hspan k hfresh hold θ htθ A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 Babs hBDG hBDGabs
      mass ρ hmass hρ hρhalf q hvq hqb hqH hq1
  have havg:=NativeFourierAverage.parameter_average_of_sections_ae MeanThetaAverage.thetaMeasure μ V
    (fun z=>Complex.ofReal (G z)) hVm (Complex.continuous_ofReal.measurable.comp hGm) hVi
    (Complex.ofRealCLM.integrable_comp hGi) (fun n=>(((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)) hc
  have hiθ : ∀ᵐ ω ∂μ,∀ᵐ x ∂haarAddCircle,Integrable (fun θ=>G (θ,(ω,x))) MeanThetaAverage.thetaMeasure:=
    Measure.ae_ae_of_ae_prod hGi.swap.prod_right_ae
  filter_upwards [havg,hiθ] with ω hω hiω n
  rw [show weightedAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q mass ρ hmass hρ.le ω=
      ∫ θ,V (θ,ω) ∂MeanThetaAverage.thetaMeasure from rfl,hω n]
  congr 1
  apply congrFun (fourierCoeff_congr_ae ?_) n
  filter_upwards [hiω] with x hx
  exact Complex.ofRealCLM.integral_comp_comm hx

end SHE.MixedPastMeanThetaFourier
