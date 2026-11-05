module

public import SHE.MixedPastTerminalRootSpatialActual
public import SHE.MixedPastTerminalPairedSpatial
public import SHE.MixedPastTerminalPairedWord
public import SHE.AssignmentGapPartition
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

namespace SHE.MixedPastTerminalPairedPackets
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


open GaussianAssignmentBlocks

def field (k:ℕ) (choices:List (Fin k×Fin (k+1))) (ν χ:ℝ) (i:Fin (k+1))
    (t:Fin k→ℝ) (z:(Ω×HeatCircle)×(Fin k→HeatCircle)):ℝ:=
  Src k choices ν χ i (separated k (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1*
    G k choices ν χ i (separated k (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1

theorem field_joint_measurable (k:ℕ) (choices:List (Fin k×Fin (k+1))) (ν χ:ℝ) (i:Fin (k+1)):
    Measurable (fun z:(Fin k→ℝ)×((Ω×HeatCircle)×(Fin k→HeatCircle))=>
      field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        k choices ν χ i z.1 z.2):=by
  have hh:Measurable (fun z:(Fin k→ℝ)×((Ω×HeatCircle)×(Fin k→HeatCircle))=>
      separated k (z.2.1.2,z.1,fun l=>z.2.2 l+z.2.1.2)):=
    (separated_measurable k).comp (measurable_snd.fst.snd.prodMk
      (measurable_fst.prodMk (Measurable.of_eval (fun l=>
        ((measurable_pi_apply l).comp measurable_snd.snd).add measurable_snd.fst.snd))))
  convert! (MixedPastTerminalSourceFields.source_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k choices ν χ i).mul (MixedPastTerminalPairedActive.point_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k choices ν χ i) |>.comp (hh.prodMk measurable_snd.fst.fst) using 1

def budget (k:ℕ) (t:Fin k→ℝ) (choices:List (Fin k×Fin (k+1)))
    (χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0) (i:Fin (k+1)):ℝ:=
  let Q:=(carrier Zero k).terminal (MixedPastTerminalSlotSpatial.anchor k t)
  let E0:=∫ω,‖S.second Q.toNNReal ω-S.first Q.toNNReal ω‖^2 ∂μ
  let E1:=(2*P.holder)^2*(∫ω,‖Dir ω‖^2 ∂μ)^P.exponent
  Fin.cases
    (2*(PairedTerminalConstants.constant P κ M B0 choices χ order 0)^(1/(order:ℝ))*
      ((ν^χ)^2*E0^χ)*(TimeAmp k t choices χ A0 ν 0*(Fintype.card (Choices 1 k):ℝ))^2)
    (fun j=>2*(PairedTerminalConstants.constant P κ M B0 choices χ order j.succ)^(1/(order:ℝ))*
      (max 1 (P.holder^(χ/P.exponent))^2*E0^χ+E1^(χ/P.exponent))*
        (TimeAmp k t choices χ A0 ν j.succ*(Fintype.card (Choices 1 k):ℝ))^2) i

include hIJ₀ hIJ₁ in
/-- ALL original finite assignments and ALL root/rough sources have
genuine joint-L1/spatial-L2 packets on one original-time event. The
current and past differences are the actual correlated native inputs. -/
theorem all_packets_ae
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H)
    (hsmallP:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1):
    let cs:=assignments (m:=k+2) (List.finRange (k+1))
    ∀ᵐ t:Fin (k+1)→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
    ∀hp:StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t),
      ∀c:Fin cs.length,∀i:Fin (k+2),
    let V:=field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      (k+1) (cs.get c) ν χ i t
    Integrable V ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin (k+1)=>haarAddCircle))) ∧
      Integrable (fun y=>|∫w,V (y,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)|^2) (μ.prod haarAddCircle) ∧
      (∫y,|∫w,V (y,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
        budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          (k+1) t (cs.get c) χ A0 ν order B0 i:=by
  intro cs
  have hnd(c:Fin cs.length):((cs.get c).map Prod.fst).Nodup:=
    AssignmentGapPartition.coordinates_nodup _ (List.get_mem cs c)
  have hjetc(c:Fin cs.length):∀x j,j≤(block (cs.get c) 0).length+1→∀z,
      ‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j:=by
    have hlen:(block (cs.get c) 0).length≤k+1:=by
      rw [←AssignmentGapPartition.block_length _ (List.get_mem cs c) 0]
      exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin (k+1))
    intro x j hj z
    exact hjet x j (hj.trans (by omega)) z
  have hr(c:Fin cs.length):=MixedPastTerminalRootSpatialActual.root_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hages hrootstop hrootage hcenter hspan hbH k hsmall (cs.get c) (hnd c)
    hA0 hν hχ hχβ.le (lt_of_lt_of_le hχβ P.exponent_le_one) (hjetc c) order horder ho0 B0 B1 hBDG hBDG1
  have hh(c:Fin cs.length):=MixedPastTerminalPairedSpatial.rough_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hages hrootstop hrootage hcenter hspan hbH hsmallP k hsmall (cs.get c) (hnd c)
    hA0 hν hχ.le hχβ (hjetc c) order horder ho0 ho1 B0 B1 hBDG hBDG1
  filter_upwards [ae_all_iff.mpr hr,ae_all_iff.mpr hh] with t htr hth
  intro hp c i
  refine Fin.cases ?_ (fun j=>?_) i
  · convert! htr c hp using 1
  · convert! hth c hp j using 1

end SHE.MixedPastTerminalPairedPackets
