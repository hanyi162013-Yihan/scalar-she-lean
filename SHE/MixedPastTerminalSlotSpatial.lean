module

public import SHE.MixedPastTerminalSlotHistory
public import SHE.ControlledTerminalPairedSections
public import SHE.HistoryRelativeEvenMoment
public import SHE.MixedPastTerminalRootHistory
public import SHE.MixedPastTerminalRoughHistory
public import SHE.PairedTerminalConstants
public import SHE.MixedPastTerminalPairedActive
public import SHE.MixedPastTerminalRootEnvelope
public import SHE.HistoryNewestMoment
public import SHE.ControlledTerminalPairedAmplitude
public import SHE.ControlledRelativeScoreForest
public import SHE.TerminalConditionalGeometry
public import SHE.ParentMeanDensity
public import SHE.MixedPastTerminalPairedIdentity
public import SHE.MixedPastTerminalPairedFields
public import SHE.ControlledTerminalPairedRelative
public import SHE.TerminalSuccessorGeometry
public import SHE.MixedPastTerminalState
public import SHE.MixedPastTerminalFirstState
public import SHE.JointHistoryFields
public import SHE.WeightedRowTimeShift
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalSlotSpatial
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S


open MixedPastTerminalPairedFields


local notation "G" => MixedPastTerminalPairedActive.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Raw" => MixedPastTerminalPairedFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp" => ControlledTerminalPairedAmplitude.amplitude P haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Sc" => ControlledTerminalPairedAmplitude.scale P haP Λ v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests Classical

def anchor (k:ℕ) (t:Fin k→ℝ):History HeatCircle k:=separated k ((0:HeatCircle),t,fun _=>0)

def timeAmplitude (k:ℕ) (t:Fin k→ℝ) (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):ℝ:=
  timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k (anchor k t)*
    |Sc k (anchor k t) choices χ A0 ν i|

def envelope (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ) (t:Fin k→ℝ) (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1))
    (w:Fin k→HeatCircle):ℝ:=
  if hp:StrictHistory Zero k (anchor k t) then
    timeAmplitude Λ P haP v b hvb Z htarget hstop F hF hFm k t choices χ A0 ν i*
    parentDensity 2 (by norm_num) k (targets Zero k (anchor k t))
      (carrier_orderedTimes Zero hages k _ hp) (values (fun _:Fin 1=>(0:HeatCircle)) k w)
  else 0

include hIJ₀ hIJ₁ in
/-- Genuine sample/output even moments of every literal paired slot
at fixed relative old sites. The actual stochastic past, covariance,
current states and all rough factors may remain fully correlated. -/
theorem all_slots_spatial_ae
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H) (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (choices:List (Fin (k+1)×Fin (k+2))) (hnd:(choices.map Prod.fst).Nodup)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hjet:∀x j,j≤(GaussianAssignmentBlocks.block choices 0).length+1→∀z,
      ‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (B0:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0):
    ∀ᵐ t:Fin (k+1)→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      ∀hp:StrictHistory Zero (k+1) (anchor (k+1) t),∀i:Fin (k+2),
      ∀ᵐ w:Fin (k+1)→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      let GG:=fun y:Ω×HeatCircle=>G (k+1) choices ν χ i
        (separated (k+1) (y.2,t,fun j=>w j+y.2)) y.1
      Integrable (fun y=>|GG y|^(2*order)) (μ.prod haarAddCircle) ∧
      (∫y,|GG y|^(2*order) ∂μ.prod haarAddCircle)≤
        PairedTerminalConstants.constant P κ M B0 choices χ order i*
        ((timeAmplitude Λ P haP v b hvb Z htarget hstop F hF hFm (k+1) t choices χ A0 ν i)*
          parentDensity 2 (by norm_num) (k+1) (targets Zero (k+1) (anchor (k+1) t))
            (carrier_orderedTimes Zero hages (k+1) _ hp) (values (fun _:Fin 1=>(0:HeatCircle)) (k+1) w))^(2*order):=by
  have hm:=MixedPastTerminalSlotHistory.all_slots_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootstop
    (fun x i=>(hrootage x i).le) hspan hbH haarAddCircle k hsmall choices hnd
    hA0 hν hχ hχβ hjet order horder B0 hBDG
  have hs(i:Fin (k+2)):=HistoryProductMeasure.relative_even_moment
    (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) μ (k+1)
    (fun z=>G (k+1) choices ν χ i z.1 z.2)
    (MixedPastTerminalPairedActive.point_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm (k+1) choices ν χ i)
    (fun h=>Amp (k+1) h choices χ A0 ν i)
    (PairedTerminalConstants.constant P κ M B0 choices χ order i) order
    (hm.mono (fun h hh=>hh i))
    (fun t=>StrictHistory Zero (k+1) (anchor (k+1) t))
    (fun t w=>envelope Λ P haP v b hvb Z htarget hstop F hF hFm hages (k+1) t choices χ A0 ν i w)
    (by
      intro t hp w x
      unfold envelope
      rw [dif_pos hp]
      exact ControlledTerminalPairedSections.amplitude_relative
        P haP Λ v b hvb Z htarget hstop F hF hFm hages hrootage hcenter
        (k+1) t hp x w choices χ A0 ν i)
  filter_upwards [ae_all_iff.mpr hs] with t ht
  intro hp i
  simpa only [envelope,dif_pos hp] using ht i hp

end SHE.MixedPastTerminalSlotSpatial
