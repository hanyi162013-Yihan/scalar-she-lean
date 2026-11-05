module

public import SHE.NativeUniversalConstants

public import SHE.MixedPastNativeKernelEnergy
public import SHE.MixedPastNativeKernelTrace
public import SHE.MixedPastNativeMeanFTCClip
public import SHE.NativeCurrentCoordinates
public import SHE.NativeCurrentOutputRMS
public import SHE.NativeReserveTranslatedEnvelope
public import SHE.MixedPastNativeKernelAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.NativeParentOutputEnergyAE
public import SHE.ControlledThetaNativePointFields
public import SHE.MixedPastLiteralFields
public import SHE.ControlledFamilyKernelBounds
public import SHE.NativeKernelParameterAverage
public import SHE.ControlledFamilyNativePacketFTC
public import SHE.MixedPastNativeLegIdentity
public import SHE.MixedPastNativeMeanClip
public import SHE.MixedPastNativeMeanCap
public import SHE.NativeCarrierGeometry
public import SHE.ControlledRelativeScoreForest
public import SHE.ControlledThetaNativeGradient
public import SHE.MixedPastNativeConsistentPoint
public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
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
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelCurrent
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanFTCClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanFTCClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanFTCClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanFTCClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastNativeMeanFTCClip_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeMeanFTCClip_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeMeanFTCClip_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

include hIJ₀ hIJ₁ in
/-- The current RMS consumed by the complete physical kernel trace.
Every target, old interval, unit/native clock and sample correlation is
specialized to its literal relative original-history frame. -/
theorem actual_current_fixed (k:ℕ):
    let hcur:=NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    ∀(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
      (q:ℝ≥0)(hvq:v≤q)(hqH:q≤H)(hq1:(q:ℝ)≤1)
      (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
      (t:Fin k→ℝ)(w:Fin k→HeatCircle),
      (q:ℝ)<(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)→
      (∀i,targets Zero k (QuarterSpatialEvent.anchor k t) i-(q:ℝ)≤4*Real.pi^2*hcur)→
      ∀(p:ℕ),0<p→∀(B0:ℝ≥0),StandardTerminalBDGPower (p*(k+2)) J B0→
      ∀χ:ℝ,0≤χ→χ<1→1≤(p:ℝ)*(1-χ)→
      let δ:=(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-(q:ℝ)
      let Cpacket:=MixedPastNativePacketUniform.constant P k k p*
        (1+2*(2:ℝ)^(((2*(p*(k+2)):ℕ):ℝ)*P.exponent)*
          ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M)^P.exponent))
      ∃aCur:HeatCircle→ℝ,Measurable aCur ∧ (∀x,0≤aCur x) ∧
        Integrable (fun x=>aCur x^2) haarAddCircle ∧
        (∀ᵐx:HeatCircle∂haarAddCircle,
          MemLp (fun ω=>Current k q t w p χ (ω,x)) 2 μ ∧
          ProfileL2.normTwo μ (fun ω=>Current k q t w p χ (ω,x))=aCur x) ∧
        (∫x,aCur x^2 ∂haarAddCircle)≤
          ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
            Cpacket^(1/(p:ℝ)):=by
  intro hcur Cdim
  have hh:=NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega)
  have hh1:=NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega)
  have hC:=NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega)
  have he:=NativeCurrentOutputRMS.actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ (1+k) (by omega)
  intro hΛ hlocal q hvq hqH hq1 B1 hBDG1 t w hqt hsmall p hp B0 hBDG χ hχ hχ1 horder δ Cpacket
  let a0:=QuarterSpatialEvent.anchor k t
  let target:=fun i=>targets Zero k a0 i-(v:ℝ)
  let a:=fun i=>NativeHeatSpan.unitCenter (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
  let lo:=fun j=>lower Zero k a0 j-(v:ℝ)
  let hi:=fun j=>upper Zero k a0 j-(v:ℝ)
  let ages:=fun i=>NativeHeatSpan.clock (target i-((q:ℝ)-(v:ℝ)))
  have hage(i:Fin (1+k)):0<target i-((q:ℝ)-(v:ℝ)):=by
    have ht: (q:ℝ)<targets Zero k a0 i:=hqt.trans_le ((carrier Zero k).targets_after a0 i)
    dsimp only [target]
    linarith
  have hages:∀i,0<ages i:=fun i=>NativeHeatSpan.clock_pos (hage i)
  have hagesSmall:∀i,ages i≤hcur:=by
    intro i
    dsimp only [ages,NativeHeatSpan.clock,target]
    apply (div_le_iff₀ (by positivity : 0<4*Real.pi^2)).mpr
    nlinarith [hsmall i]
  have hclock(i:Fin (1+k)):target i-((q:ℝ)-(v:ℝ))=4*Real.pi^2*ages i:=by
    dsimp only [ages,NativeHeatSpan.clock]
    field_simp
  have hδ:0<δ:=sub_pos.mpr hqt
  have hmin(i:Fin (1+k)):(q:ℝ)-(v:ℝ)+δ≤target i:=by
    have ht: (carrier Zero k).terminal a0≤targets Zero k a0 i:=(carrier Zero k).targets_after a0 i
    dsimp only [target,δ]
    linarith
  have hdisjoint(j l:Fin k)(hne:j≠l):hi j≤lo l ∨ hi l≤lo j:=
    RelativeHistoryGeometry.relative_disjoint Zero k a0 j l hne
  obtain ⟨aCur,ham,ha0,hai,hsec,hE⟩:=he P hΛ hlocal v q hvq hqH hq1 B1 hBDG1
    target a ages hages hagesSmall hclock δ hδ hmin k k lo hi hdisjoint
    (leafIndex k (fun i=>i)) p hp B0 hBDG χ hχ hχ1 horder
  refine ⟨aCur,ham,ha0,hai,?_,hE⟩
  filter_upwards [hsec] with x hx
  have heq:(fun ω=>Current k q t w p χ (ω,x))=
      fun ω=>|MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P v q target a lo hi (ω,NativeHeatSpan.unitCenter x)|^χ*
      MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (r:=k)
        P v q target target a (leafIndex k (fun i=>i)) p (ω,NativeHeatSpan.unitCenter x):=by
    funext ω
    simp only [MixedPastNativeKernelEnergy.current,abs_of_nonneg (Real.sqrt_nonneg _),
      MixedNativeDampedScoreAmplitude.amplitude]
    rfl
  rw [heq]
  exact hx

include hIJ₀ hIJ₁ in
theorem actual_current (k:ℕ):
    ∃hcur Cdim:ℝ,0<hcur ∧ hcur≤1 ∧ 0<Cdim ∧
    ∀(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
      (q:ℝ≥0)(hvq:v≤q)(hqH:q≤H)(hq1:(q:ℝ)≤1)
      (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
      (t:Fin k→ℝ)(w:Fin k→HeatCircle),
      (q:ℝ)<(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)→
      (∀i,targets Zero k (QuarterSpatialEvent.anchor k t) i-(q:ℝ)≤4*Real.pi^2*hcur)→
      ∀(p:ℕ),0<p→∀(B0:ℝ≥0),StandardTerminalBDGPower (p*(k+2)) J B0→
      ∀χ:ℝ,0≤χ→χ<1→1≤(p:ℝ)*(1-χ)→
      let δ:=(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-(q:ℝ)
      let Cpacket:=MixedPastNativePacketUniform.constant P k k p*
        (1+2*(2:ℝ)^(((2*(p*(k+2)):ℕ):ℝ)*P.exponent)*
          ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M)^P.exponent))
      ∃aCur:HeatCircle→ℝ,Measurable aCur ∧ (∀x,0≤aCur x) ∧
        Integrable (fun x=>aCur x^2) haarAddCircle ∧
        (∀ᵐx:HeatCircle∂haarAddCircle,
          MemLp (fun ω=>Current k q t w p χ (ω,x)) 2 μ ∧
          ProfileL2.normTwo μ (fun ω=>Current k q t w p χ (ω,x))=aCur x) ∧
        (∫x,aCur x^2 ∂haarAddCircle)≤
          ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
            Cpacket^(1/(p:ℝ)):=by
  exact ⟨NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant.{0} (1+k) (by omega),NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega),NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega),actual_current_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k⟩

end SHE.MixedPastNativeKernelCurrent
