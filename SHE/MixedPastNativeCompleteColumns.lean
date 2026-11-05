module
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedOldTimeEnergy
public import SHE.MixedPastSignedEndpointTrace
public import SHE.RawTraceRMS
public import SHE.MixedPastKernelSections
public import SHE.RelativeKernelTruncationZero
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option quotPrecheck false

namespace SHE.MixedPastNativeCompleteColumns
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastSignedEndpointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastSignedEndpointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastSignedEndpointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastSignedEndpointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastSignedEndpointMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastSignedEndpointMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastSignedEndpointMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total

open ActualMeanKernel NativeRandomKernel NormalizedKernelSplit NativeSignedHaarProcess SignedKernelTruncation
local notation "Endpoint"=>MixedPastKernelFields.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

local instance mixedPastNativeCompleteColumns_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance mixedPastNativeCompleteColumns_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedPastNativeCompleteColumns_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
local notation "Add"=>MixedPastNativeOldTimeEnergy.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "BaseCols"=>MixedPastNativeOldTimeEnergy.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Signed"=>MixedPastSignedEndpointFields.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Complete left-channel columns after the original old-time average. -/
def left (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(ω:Ω):NativeKernelHaarColumns.Space:=
  ∫t,Add k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))

/-- Complete right-channel columns include BOTH the common-kernel
change and the endpoint stop-weighted coefficient-difference columns. -/
def right (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(ω:Ω):NativeKernelHaarColumns.Space:=
  (∫t,BaseCols k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))+
  (∫t,Signed k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))

def commonBudget (k:ℕ)(q:ℝ≥0)(A0 ν ρ χ:ℝ)(p:ℕ)(Bcur Bword:ℝ≥0):ℝ:=
  let Cf:=NativeUniversalConstants.rowConstant (1+k)
  let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
  let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) P k Cf ρ
  let Ccur:=sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
  let Cpast:=sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) P k Bword)
  let Eq:=∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ
  let Ev:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  ((b:ℝ)-(q:ℝ))^(ρ/2)*(Ccur*Eq^(χ/2)*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
      ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) ((2-χ)/4) A0 ν+
    Cpast*sqrt Ev*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
      ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν)

def signedBudget (k:ℕ)(q:ℝ≥0)(A0 ν mass ρ lam ε tail η:ℝ)(hmass:1≤mass)
    (hρ:0<ρ)(hρhalf:ρ<1/2)(p:ℕ)(Bcur:ℝ≥0):ℝ:=
  let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
  let C:=MixedPastWordMoments.momentConstant P k k p
    ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^P.exponent)
  let E:=∫ω,inputEnergy hmass hρ.le (CU (q,ω)) (CV (q,ω)) ∂μ
  PastSignedEndpointTime.goodCoefficient P k Jt ρ η*lam^ε*((b:ℝ)-(q:ℝ))^((ρ+η)/2)*sqrt E*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
      ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (RawTraceTimeEnvelope.freshDegree ρ η) A0 ν+
  PastSignedEndpointTime.badCoefficient P k M C*lam^(-tail/2)*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
      ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν

local notation "LCols"=>left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RCols"=>right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CBudget"=>commonBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b
local notation "SBudget"=>signedBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b

theorem left_time_measurable (k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (fun z:ℝ≥0×Ω=>LCols k z.1 hmass hρ z.2):=
  MixedPastNativeOldTimeEnergy.additive_average_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k _ hmass hρ

theorem right_time_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (fun z:ℝ≥0×Ω=>RCols k z.1 hmass hρ z.2):=by
  have hb:=MixedPastNativeOldTimeEnergy.base_average_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k
    (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) hmass hρ
  have hs:=MixedPastSignedEndpointFields.average_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm hΛ k
    (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) hmass hρ
  exact hb.add hs

attribute [local irreducible] MixedPastNativeOldTimeEnergy.additive MixedPastNativeOldTimeEnergy.base
  MixedPastSignedEndpointFields.raw commonBudget signedBudget

include hIJ₀ hIJ₁ in
/-- The full actual higher-noise column field has BOTH sharp branches.
No independent kernel/current moment or random-reference hypothesis is
introduced in this original-old-time energy bound. -/
theorem energy (k:ℕ)(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hrootStop:∀x i,(Z.observations x i).stop=(b:ℝ))(hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (hspanF:(b:ℝ)-(v:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(b:ℝ)-(v:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (q:ℝ≥0)(hvq:v<q)(hqb:q<b)(hqH:q≤H)(hq1:(q:ℝ)≤1)(hwidth1:(b:ℝ)-(q:ℝ)≤1)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (mass ρ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    Integrable (fun ω=>‖LCols k q hmass hρ.le ω‖^2) μ ∧
      Integrable (fun ω=>‖RCols k q hmass hρ.le ω‖^2) μ ∧
      (∫ω,‖LCols k q hmass hρ.le ω‖^2 ∂μ)+(∫ω,‖RCols k q hmass hρ.le ω‖^2 ∂μ)≤
        4*(commonBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b k q A0 ν ρ χ p Bcur Bword)^2+
        2*(signedBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b
          k q A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2:=by
  have hc:=MixedPastNativeOldTimeEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    k hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC hHistory
    q hvq hqb hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    mass ρ hmass hρ hρhalf
  have hBDGs:StandardTerminalBDGPower ((p-1+1)*(k+2)) J Bcur:=by
    simpa only [Nat.sub_add_cancel hp] using hBDGcur
  have hs:=MixedPastSignedOldTimeEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ.le (fun x i=>by rw [hrootStop x i,hrootTarget x i]) (fun x i=>(hrootStop x i).le)
    hrootTarget (fun x=>hcenter x 0) hspan k hspanS hHistory A0 ν hA0 hν hjet
    (p-1) Bcur hBDGs q hvq.le hqb hqH hwidth1 mass ρ lam ε tail η hmass hρ hρhalf hlam htail hη hρη
  let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
  let B:=fun ω=>∫t,BaseCols k q hmass hρ.le (t,ω) ∂old
  let D:=fun ω=>∫t,Signed k q hmass hρ.le (t,ω) ∂old
  have hiB:Integrable (fun ω=>‖B ω‖^2) μ:=hc.2.2.2.1
  have hiD:Integrable (fun ω=>‖D ω‖^2) μ:=hs.2.1
  have hmR:Measurable (fun ω=>RCols k q hmass hρ.le ω):=
    (right_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hΛ.le k hmass hρ.le).comp
        ((measurable_const (a:=q)).prodMk measurable_id)
  have hpoint(ω:Ω):‖RCols k q hmass hρ.le ω‖^2≤2*‖B ω‖^2+2*‖D ω‖^2:=by
    calc
      _≤(‖B ω‖+‖D ω‖)^2:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _≤_:=by nlinarith [sq_nonneg (‖B ω‖-‖D ω‖)]
  have hboundi:Integrable (fun ω=>2*‖B ω‖^2+2*‖D ω‖^2) μ:=(hiB.const_mul 2).add (hiD.const_mul 2)
  have hiR:Integrable (fun ω=>‖RCols k q hmass hρ.le ω‖^2) μ:=hboundi.mono'
    (hmR.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ (fun ω=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)];exact hpoint ω))
  have hR:=integral_mono hiR hboundi hpoint
  rw [integral_add (hiB.const_mul 2) (hiD.const_mul 2),integral_const_mul,integral_const_mul] at hR
  have hcommon:(∫ω,‖LCols k q hmass hρ.le ω‖^2 ∂μ)+(∫ω,‖B ω‖^2 ∂μ)≤
      2*(commonBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b k q A0 ν ρ χ p Bcur Bword)^2:=by
    unfold commonBudget
    exact hc.2.2.2.2
  have hsigned:(∫ω,‖D ω‖^2 ∂μ)≤(signedBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b
      k q A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2:=by
    unfold signedBudget
    simpa only [Nat.sub_add_cancel hp] using hs.2.2
  refine ⟨hc.2.2.1,hiR,?_⟩
  have hleft:0≤∫ω,‖LCols k q hmass hρ.le ω‖^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  linarith only [hcommon,hsigned,hR,hleft]

end SHE.MixedPastNativeCompleteColumns
