module

public import SHE.NativeUniversalConstants

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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelTrace
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

/-- Original relative observations at fixed old times and sites. The
main native stop=target geometry is retained in every coordinate. -/
def frame (k:ℕ) (t:Fin k→ℝ) (w:Fin k→HeatCircle):Fin (1+k)→Observation:=
  fun i=>⟨targets Zero k (QuarterSpatialEvent.anchor k t) i-(v:ℝ),
    targets Zero k (QuarterSpatialEvent.anchor k t) i-(v:ℝ),
    OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i⟩

local notation "Frame"=>frame Λ P haP v b hvb Z htarget hstop F hF hFm

/-- The ORIGINAL absolute row-r is exactly the translated relative
frame at r-v. Its Gaussian law remains the original law-q. -/
theorem row_relative
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x y:HeatCircle)(r:ℝ):
    heatRow ((carrier Zero k).observations.observations (separated k (x,t,fun i=>w i+x))) r y=
      heatRow (NativeReserveTranslatedEnvelope.translate (Frame k t w) x) (r-(v:ℝ)) y:=by
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have ht:=FixedHistoryTimeFactors.targets_sections Zero b hT (fun _:Fin 1=>(b:ℝ)) hrootTarget
    k t x 0 (fun i=>w i+x) (fun _=>0)
  have hc:=ScalarRootRelativeGeometry.centers_relative Zero hcenter k t x w
  apply PiLp.ext
  intro i
  change (ProfileVariance.heatPhysical
    (targets Zero k (separated k (x,t,fun i=>w i+x)) i-r)
    (centers Zero k (separated k (x,t,fun i=>w i+x)) i) y).re=_
  rw [ht,hc]
  change (ProfileVariance.heatPhysical (targets Zero k (QuarterSpatialEvent.anchor k t) i-r)
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i+x) y).re=
    (ProfileVariance.heatPhysical ((targets Zero k (QuarterSpatialEvent.anchor k t) i-(v:ℝ))-(r-(v:ℝ)))
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i+x) y).re
  congr 2
  ring

theorem reserve_relative
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:HeatCircle)(q:ℝ):
    NativeFirstScoreReserve.covariance P
      (fun i=>targets Zero k (separated k (x,t,fun i=>w i+x)) i-(v:ℝ))
      (fun i=>targets Zero k (separated k (x,t,fun i=>w i+x)) i-(v:ℝ))
      (centers Zero k (separated k (x,t,fun i=>w i+x))) (q-(v:ℝ))=
    NativeFirstScoreReserve.covariance P (fun i=>(Frame k t w i).stop) (fun i=>(Frame k t w i).target)
      (fun i=>(NativeReserveTranslatedEnvelope.translate (Frame k t w) x i).center) (q-(v:ℝ)):=by
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  rw [FixedHistoryTimeFactors.targets_sections Zero b hT (fun _:Fin 1=>(b:ℝ)) hrootTarget k t x 0 _ (fun _=>0),
    ScalarRootRelativeGeometry.centers_relative Zero hcenter]
  rfl

/-- A genuine JOINT physical input/output range and all-parent score
bound for the exact original law-q/row-r comparison. Every old site is
translated simultaneously; no adaptive fixed-frame AE substitution occurs. -/
theorem row_event_fixed (k:ℕ):
    let Hf:=NativeUniversalConstants.rowHorizon (1+k)
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    ∀(hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
        (hcenter:∀x i,(Z.observations x i).center=x)
        (q r:ℝ)(hq:(v:ℝ)≤q)(hqr:q≤r)(t:Fin k→ℝ)(w:Fin k→HeatCircle),
      ∀hrt:r<(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t),
      (∀i,targets Zero k (QuarterSpatialEvent.anchor k t) i-r≤Hf)→
      ∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      let h:=separated k (yx.2,t,fun i=>w i+yx.2)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let R:=NativeFirstScoreReserve.covariance P target target (centers Zero k h) (q-(v:ℝ))
      let E:=heatRow ((carrier Zero k).observations.observations h) r yx.1
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range ∧
      Real.sqrt (scoreVariance R E)≤
        Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-r)))*
          NativeHeatSpan.sqrtKernelConstant*∑i,
          ((Frame k t w i).target-(r-(v:ℝ)))^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*((Frame k t w i).target-(r-(v:ℝ))))
            (by
              change 0<8*((targets Zero k (QuarterSpatialEvent.anchor k t) i-(v:ℝ))-(r-(v:ℝ)))
              have hAfter:(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)≤
                  targets Zero k (QuarterSpatialEvent.anchor k t) i:=
                (carrier Zero k).targets_after (QuarterSpatialEvent.anchor k t) i
              linarith [hrt,hAfter])
            yx.1 (yx.2+(Frame k t w i).center)‖:=by
  intro Hf Cf
  have hHf:=NativeUniversalConstants.rowHorizon_pos (1+k)
  have hCf:=NativeUniversalConstants.rowConstant_pos (1+k)
  have henv:=(NativeUniversalConstants.row_spec (1+k)).2.2
  intro hrootTarget hcenter q r hq hqr t w hrt hsmall
  let a:=QuarterSpatialEvent.anchor k t
  let Q:=Frame k t w
  have hstopFrame(i:Fin (1+k)):(carrier Zero k).terminal a-(v:ℝ)≤(Q i).stop:=
    sub_le_sub_right ((carrier Zero k).targets_after a i) _
  have hage(i:Fin (1+k)):(Q i).target-(r-(v:ℝ))≤Hf:=by
    change (targets Zero k a i-(v:ℝ))-(r-(v:ℝ))≤Hf
    convert! hsmall i using 1 <;> ring
  have hagesFrame:∀i,(Q i).stop≤(Q i).target:=by
    intro i
    change (targets Zero k a i-(v:ℝ))≤(targets Zero k a i-(v:ℝ))
    exact le_rfl
  have hh:=henv P Q hagesFrame (sub_nonneg.mpr hq)
    (sub_le_sub_right hqr (v:ℝ)) (sub_lt_sub_right hrt (v:ℝ)) hstopFrame hage
  filter_upwards [hh] with yx hyx
  intro h target R E
  have hRow:=row_relative Λ P haP v b hvb Z htarget hstop F hF hFm hrootTarget hcenter k t w yx.2 yx.1 r
  have hReserve:=reserve_relative Λ P haP v b hvb Z htarget hstop F hF hFm hrootTarget hcenter k t w yx.2 q
  dsimp only [R,E,target,h]
  rw [hReserve,hRow]
  refine ⟨hyx.1,hyx.2.trans_eq ?_⟩
  have hgap:((carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-(v:ℝ))-(r-(v:ℝ))=
      (carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-r:=by ring
  simp only [hgap]
  congr 2
  funext i
  dsimp only [Q]
  rw [NativeHeatSpan.kernel_symm,add_comm (Frame k t w i).center yx.2]

theorem row_event (k:ℕ):
    ∃Hf Cf:ℝ,0<Hf ∧ 0<Cf ∧
      ∀(hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
        (hcenter:∀x i,(Z.observations x i).center=x)
        (q r:ℝ)(hq:(v:ℝ)≤q)(hqr:q≤r)(t:Fin k→ℝ)(w:Fin k→HeatCircle),
      ∀hrt:r<(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t),
      (∀i,targets Zero k (QuarterSpatialEvent.anchor k t) i-r≤Hf)→
      ∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      let h:=separated k (yx.2,t,fun i=>w i+yx.2)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let R:=NativeFirstScoreReserve.covariance P target target (centers Zero k h) (q-(v:ℝ))
      let E:=heatRow ((carrier Zero k).observations.observations h) r yx.1
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range ∧
      Real.sqrt (scoreVariance R E)≤
        Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-r)))*
          NativeHeatSpan.sqrtKernelConstant*∑i,
          ((Frame k t w i).target-(r-(v:ℝ)))^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*((Frame k t w i).target-(r-(v:ℝ))))
            (by
              change 0<8*((targets Zero k (QuarterSpatialEvent.anchor k t) i-(v:ℝ))-(r-(v:ℝ)))
              have hAfter:(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)≤
                  targets Zero k (QuarterSpatialEvent.anchor k t) i:=
                (carrier Zero k).targets_after (QuarterSpatialEvent.anchor k t) i
              linarith [hrt,hAfter])
            yx.1 (yx.2+(Frame k t w i).center)‖:=by
  exact ⟨NativeUniversalConstants.rowHorizon (1+k),NativeUniversalConstants.rowConstant (1+k),NativeUniversalConstants.rowHorizon_pos (1+k),NativeUniversalConstants.rowConstant_pos (1+k),row_event_fixed Λ P haP v b hvb Z htarget hstop F hF hFm k⟩

end SHE.MixedPastNativeKernelTrace
