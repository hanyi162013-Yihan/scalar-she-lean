module

public import SHE.MixedPastTerminalRoughSpatialEnergy
public import SHE.MixedPastTerminalRootSpatialEnergy
public import SHE.MixedHilbertInputMoments
public import SHE.MixedPastTerminalSlotSpatial
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

namespace SHE.MixedPastTerminalPairedSpatial
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
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
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
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S


open MixedPastTerminalPairedFields


local notation "G" => MixedPastTerminalPairedActive.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Raw" => MixedPastTerminalPairedFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp" => ControlledTerminalPairedAmplitude.amplitude P haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Sc" => ControlledTerminalPairedAmplitude.scale P haP Λ v b hvb Z htarget hstop F hF hFm


open HistoryProductMeasure OrderedHeatForests Classical ProfileL2 ProfileStability
local notation "Src"=>MixedPastTerminalSources.source 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "TimeAmp"=>MixedPastTerminalSlotSpatial.timeAmplitude Λ P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Actual all-order rough paired source energy on original old-time
sections. Every conditional/native Gaussian applicability premise and
all current/past energy finiteness are discharged from the SAME actual
mixed solution and the accepted original Ito moment package. -/
theorem rough_energy_ae
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H)
    (hsmallP:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (choices:List (Fin (k+1)×Fin (k+2))) (hnd:(choices.map Prod.fst).Nodup)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤(GaussianAssignmentBlocks.block choices 0).length+1→∀z,
      ‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1):
    ∀ᵐ t:Fin (k+1)→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
    ∀hp:StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t),∀j:Fin (k+1),
    let Q:=(carrier Zero (k+1)).terminal (MixedPastTerminalSlotSpatial.anchor (k+1) t)
    let E0:=∫ω,‖S.second Q.toNNReal ω-S.first Q.toNNReal ω‖^2 ∂μ
    let E1:=(2*P.holder)^2*(∫ω,‖Dir ω‖^2 ∂μ)^P.exponent
    let C:=PairedTerminalConstants.constant P κ M B0 choices χ order j.succ
    let V:=fun z:(Ω×HeatCircle)×(Fin (k+1)→HeatCircle)=>
      Src (k+1) choices ν χ j.succ (separated (k+1) (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1*
        G (k+1) choices ν χ j.succ (separated (k+1) (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1
    Integrable V ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin (k+1)=>haarAddCircle))) ∧
      Integrable (fun y=>|∫w,V (y,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)|^2) (μ.prod haarAddCircle) ∧
      (∫y,|∫w,V (y,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
        2*C^(1/(order:ℝ))*(max 1 (P.holder^(χ/P.exponent))^2*E0^χ+E1^(χ/P.exponent))*
          (TimeAmp (k+1) t choices χ A0 ν j.succ*(Fintype.card (Choices 1 (k+1)):ℝ))^2:=by
  have hm:=MixedPastTerminalSlotSpatial.all_slots_spatial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootstop hrootage hcenter
    hspan hbH k hsmall choices hnd hA0 hν hχ hχβ.le hjet order horder B0 hBDG
  have hdv:=MixedHeatedDifferenceMoments.current_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v (hvb.trans hbH)
    ((show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvb.trans hbH).trans hH) 1 (by decide) B1 hBDG1
  have hdp:Integrable (fun ω=>‖Dir ω‖^2) μ:=by
    simpa only [MixedPastJointData.pastD,embed_norm] using hdv.1
  filter_upwards [hm] with t ht
  intro hp j
  let h:=MixedPastTerminalSlotSpatial.anchor (k+1) t
  let Q:=(carrier Zero (k+1)).terminal h
  have hnode:(carrier Zero k).nodeTime h=h.2.1:=ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
  have hpos:(v:ℝ)<Q:=by
    change (v:ℝ)<(carrier Zero k).nodeTime h
    rw [hnode]
    exact hp.2.1
  have hqb:Q≤(b:ℝ):=terminal_le_initial Zero (k+1) h
  have hqH:Q.toNNReal≤H:=Real.toNNReal_le_iff_le_coe.mpr
    (hqb.trans (by exact_mod_cast hbH))
  have hdi:=MixedHeatedDifferenceMoments.current_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ Q.toNNReal hqH
    ((show (Q.toNNReal:ℝ)≤(H:ℝ) from by exact_mod_cast hqH).trans hH) 1 (by decide) B1 hBDG1
  have hage:targets Zero (k+1) h (leafIndex (k+1) (fun i:Fin (1+(k+1))=>i) j)-(v:ℝ)∈Ioc 0 P.horizon:=by
    have he:targets Zero (k+1) h (leafIndex (k+1) (fun i:Fin (1+(k+1))=>i) j)=lower Zero (k+1) h j:=by
      unfold targets
      rw [leaf_observation]
    rw [he]
    exact ⟨sub_pos.mpr (hpos.trans_le (terminal_le_lower Zero (k+1) h j)),
      (sub_le_sub_right ((lower_lt_upper Zero (k+1) h hp j).le.trans (upper_le_initial Zero (k+1) h j)) _).trans hspan⟩
  convert! MixedPastTerminalRoughSpatialEnergy.section_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hΛ hages hrootage hcenter hsmallP (k+1) t hp choices hν hχ hχβ j order horder ho0 ho1
    (PairedTerminalConstants.constant P κ M B0 choices χ order j.succ)
    (PairedTerminalConstants.constant_nonneg P hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) B0 choices χ order j.succ)
    (ht hp j.succ) hdi.1 hdp hage using 1

end SHE.MixedPastTerminalPairedSpatial
