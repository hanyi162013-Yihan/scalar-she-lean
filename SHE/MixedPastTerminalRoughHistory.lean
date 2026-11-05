module

public import SHE.MixedPastTerminalPairedActive
public import SHE.MixedPastTerminalRoughEnvelope
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

namespace SHE.MixedPastTerminalRoughHistory
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
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
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

include hIJ₀ hIJ₁ in
/-- Literal actual random-past ROUGH-paired terminal slots have their
sharp original-history even moments. Geometry, all-data Gaussian ranges,
conditional native offsets, old forest and newest-coordinate Fubini are
ALL discharged, before a current source is paired by Holder. -/
theorem actual_even_moment_ae
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (choices:List (Fin (k+1)×Fin (k+2))) (hnd:(choices.map Prod.fst).Nodup)
    (j0:Fin (k+1))
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hjet:∀x j,j≤(GaussianAssignmentBlocks.block choices 0).length+1→∀z,
      ‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (B0:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ (k+1),
      Integrable (fun ω=>|G (k+1) choices ν χ j0.succ h ω|^(2*order)) μ ∧
      (∫ω,|G (k+1) choices ν χ j0.succ h ω|^(2*order) ∂μ)≤
      PairedRoughWordMoments.constant P choices j0 χ order
        (2*((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (order*((k+1)+2)) B0 κ M)^P.exponent)*
        (Amp (k+1) h choices χ A0 ν j0.succ)^(2*order):=by
  let CC:=PairedRoughWordMoments.constant P choices j0 χ order
    (2*((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (order*((k+1)+2)) B0 κ M)^P.exponent)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hMC:0≤NativeHybridMoments.momentConstant (order*((k+1)+2)) B0 κ M:=by
    unfold NativeHybridMoments.momentConstant
    exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
  have hCC:0≤CC:=by
    unfold CC
    exact PairedRoughWordMoments.constant_nonneg P choices j0 χ order
      (mul_nonneg (by positivity) (Real.rpow_nonneg hMC _))
  apply HistoryNewestMoment.ae_succ_even _ ρ k μ
    (fun z=>G (k+1) choices ν χ j0.succ z.1 z.2)
    (MixedPastTerminalPairedActive.point_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      (k+1) choices ν χ j0.succ)
    (fun h=>CC*(Amp (k+1) h choices χ A0 ν j0.succ)^(2*order))
    (((ControlledTerminalPairedAmplitude.amplitude_measurable
      P haP Λ v b hvb Z htarget hstop F hF hFm (k+1) choices χ A0 ν j0.succ).pow_const _).const_mul CC)
    (fun h=>mul_nonneg hCC (Even.pow_nonneg (even_two_mul order) _)) order
  have hrel:=Measure.ae_ae_of_ae_prod (MixedPastTerminalPairedIdentity.point_relative_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootstop ρ k)
  have hfr:=Measure.ae_ae_of_ae_prod (ControlledRelativeScoreForest.all_inputs_ae
    P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ (k+1))
  filter_upwards [hrel,hfr] with old holdrel holdfr
  have hrelt:=Measure.ae_ae_of_ae_prod holdrel
  have hfrt:=Measure.ae_ae_of_ae_prod holdfr
  filter_upwards [hrelt,hfrt] with t htrel htfr
  let h:History X (k+1):=(old,(t,0))
  let sectionHistory:=TerminalSuccessorGeometry.atSpace h
  change ∀ᵐ x:HeatCircle ∂haarAddCircle,
    Integrable (fun ω=>|G (k+1) choices ν χ j0.succ (sectionHistory x) ω|^(2*order)) μ ∧
    (∫ω,|G (k+1) choices ν χ j0.succ (sectionHistory x) ω|^(2*order) ∂μ)≤
      CC*(Amp (k+1) (sectionHistory x) choices χ A0 ν j0.succ)^(2*order)
  by_cases hp:StrictHistory Zero (k+1) h
  · have hpx(x:HeatCircle):StrictHistory Zero (k+1) (sectionHistory x):=hp
    have hnode:(carrier Zero k).nodeTime h=h.2.1:=ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
    have hpos:(v:ℝ)<(carrier Zero k).nodeTime h:=by rw [hnode];exact hp.2.1
    let q:ℝ≥0:=Real.toNNReal ((carrier Zero k).nodeTime h)
    have heq:(q:ℝ)=(carrier Zero k).nodeTime h:=Real.coe_toNNReal _ (v.2.trans hpos.le)
    have hvq:v<q:=by exact_mod_cast hpos.trans_eq heq.symm
    have hqt:(q:ℝ)<(carrier Zero k).terminal h.1:=by rw [heq,hnode];exact hp.2.2
    have hqH:q≤H:=by
      have hqb:(q:ℝ)≤(b:ℝ):=hqt.le.trans (terminal_le_initial Zero k h.1)
      exact_mod_cast hqb.trans (by exact_mod_cast hbH)
    have hspanq:(q:ℝ)-(v:ℝ)≤1:=by
      have hqb:(q:ℝ)≤(b:ℝ):=hqt.le.trans (terminal_le_initial Zero k h.1)
      linarith [hspan.trans P.horizon_le_one]
    have hgap(i):(q:ℝ)<((carrier Zero k).observations.observations h.1 i).target:=
      carrier_targets_after Zero h.1 hages hqt i
    have hpkt:=TerminalConditionalGeometry.packet Zero hages (b:ℝ) P.horizon (fun _=>le_rfl)
      (hspan.trans P.horizon_le_one) hspan k h hp
    rw [←heq] at hpkt
    let K:HeatCircle→ℝ:=fun x=>timeWeight Zero (fraction P*P.lower) (uniformConstant 1) (k+1) h*
      ParentMeanDensity.parentProduct Zero (k+1) (sectionHistory x)
    have hK(x):0≤K x:=mul_nonneg
      (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
        (fun j=>(uniformConstant_pos 1 j).le) (k+1) h hp)
      (ParentMeanDensity.parentProduct_nonneg Zero (k+1) (sectionHistory x))
    have hrepr:∀ᵐ x:HeatCircle ∂haarAddCircle,∀ω:Ω,
      Raw (k+1) choices ν χ j0.succ (sectionHistory x) ω=
      PairedAssignedTelescope.averageSlot P Λ (U ω) (Dir ω) 0 1 0 ((q:ℝ)-(v:ℝ))
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun i=>stops Zero k h.1 i-(v:ℝ)))
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun i=>targets Zero k h.1 i-(v:ℝ)))
        (Fin.cons x (centers Zero k h.1))
        (fun j=>lower Zero (k+1) h j-(v:ℝ)) (fun j=>upper Zero (k+1) h j-(v:ℝ))
        (directions Zero ((carrier Zero (k+1)).observations.observations (sectionHistory x)) (k+1) (sectionHistory x)) choices
        (F (rootParameter (k+1) h)) (rootSelector (k+1) (fun i=>i)) (leafIndex (k+1) (fun i=>i))
        (MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S 1 v q
          (fun i=>stops Zero k h.1 i-(v:ℝ)) (fun i=>targets Zero k h.1 i-(v:ℝ)) (centers Zero k h.1) x ω)
        (MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S 0 v q
          (fun i=>stops Zero k h.1 i-(v:ℝ)) (fun i=>targets Zero k h.1 i-(v:ℝ)) (centers Zero k h.1) x ω) ν χ j0.succ:=by
      filter_upwards [htrel] with x hx
      intro ω
      have hh:=hx q heq hgap choices ν χ j0.succ ω
      have hl:lower Zero (k+1) (old,(t,x))=lower Zero (k+1) h:=rfl
      have hu:upper Zero (k+1) (old,(t,x))=upper Zero (k+1) h:=rfl
      rw [hl,hu] at hh
      exact hh
    have hframe:∀ᵐ x:HeatCircle ∂haarAddCircle,∀ω:Ω,
      let A:=OldIntervalCovariance.familyCovariance
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun i=>stops Zero k h.1 i-(v:ℝ)))
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun i=>targets Zero k h.1 i-(v:ℝ)))
        (Fin.cons x (centers Zero k h.1)) (referenceProfile P Λ (U ω) (Dir ω))
        (fun j=>lower Zero (k+1) h j-(v:ℝ)) (fun j=>upper Zero (k+1) h j-(v:ℝ))
      let D:=directions Zero ((carrier Zero (k+1)).observations.observations (sectionHistory x)) (k+1) (sectionHistory x)
      (∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range) ∧
      |∏j,MeasurableGaussianScores.scoreVariance (A j) (D j)|≤K x:=by
      filter_upwards [htfr] with x hx
      intro ω
      have htx:(q:ℝ)≤(carrier Zero (k+1)).terminal (sectionHistory x):=heq.le
      have hh:=hx (q:ℝ) (by exact_mod_cast hvq.le) htx (U ω,Dir ω)
      have hsx:=RelativeHistoryGeometry.smallHistory_of_span Zero (b:ℝ) (fun _=>le_rfl) hrootage
        (uniformHorizon 1) (k+1) hsmall (sectionHistory x)
      have hb:=(hh.2 (hpx x) hsx).2
      have harr:=TerminalSuccessorGeometry.relative_arrays_atSpace Zero (v:ℝ) k h x
      rw [←heq] at harr
      dsimp only [TerminalSuccessorGeometry.atSpace,h] at harr
      dsimp only at hh hb
      have hl:lower Zero (k+1) (old,(t,x))=lower Zero (k+1) h:=rfl
      have hu:upper Zero (k+1) (old,(t,x))=upper Zero (k+1) h:=rfl
      rw [harr.1,harr.2.1,harr.2.2,hl,hu] at hh hb
      refine ⟨hh.1,?_⟩
      have hmass:=ParentMeanDensity.parentProduct_eq_parentDensity Zero hages (k+1) (sectionHistory x) (hpx x)
      change _≤timeWeight Zero (fraction P*P.lower) (uniformConstant 1) (k+1) h*_
      rw [hmass]
      exact hb
    have hout:=MixedPastTerminalRoughEnvelope.conditional_rough
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z htarget hstop F hF hFm k h q hlocal hΛ hvq hqH hspanq hpkt
      choices hnd j0 hA0 hν hχ hχβ (hjet _) order horder B0 hBDG K hK hframe hrepr
    filter_upwards [hout] with x hx
    have hh:=hx univ MeasurableSet.univ
    simp only [Measure.restrict_univ,probReal_univ,mul_one] at hh
    have htar:(fun i=>targets Zero (k+1) h i-(v:ℝ))=
        Fin.cons ((q:ℝ)-(v:ℝ)) (fun i=>targets Zero k h.1 i-(v:ℝ)):=by
      rw [TerminalSuccessorGeometry.targets_succ,←heq]
      funext i
      exact Fin.cases rfl (fun _=>rfl) i
    have hsc:Sc (k+1) h choices χ A0 ν j0.succ=
        PairedTerminalTimeFields.factor P (fun j=>lower Zero (k+1) h j-(v:ℝ))
          (fun j=>upper Zero (k+1) h j-(v:ℝ))
          (fun j:Fin (k+1)=>(Fin.cons ((q:ℝ)-(v:ℝ))
            (fun i:Fin (1+k)=>targets Zero k h.1 i-(v:ℝ)) : Fin (1+(k+1))→ℝ)
            (leafIndex (n:=1) (k+1) (fun i:Fin (1+(k+1))=>i) j)) choices χ A0 ν j0.succ:=by
      unfold ControlledTerminalPairedAmplitude.scale
      congr 1
      funext j
      exact congrFun htar (leafIndex (n:=1) (k+1) (fun i:Fin (1+(k+1))=>i) j)
    rw [←hsc] at hh
    have hamp:Amp (k+1) (sectionHistory x) choices χ A0 ν j0.succ=K x*|Sc (k+1) h choices χ A0 ν j0.succ|:=by
      unfold ControlledTerminalPairedAmplitude.amplitude
      rw [ControlledTerminalPairedAmplitude.scale_atSpace]
      rfl
    rw [←hamp] at hh
    simpa only [MixedPastTerminalPairedActive.point,if_pos (hpx x)] using hh
  · apply ae_of_all
    intro x
    have hn:¬StrictHistory Zero (k+1) (sectionHistory x):=hp
    simp only [MixedPastTerminalPairedActive.point,if_neg hn,abs_zero,
      zero_pow (by omega : 2*order≠0),integrable_zero,integral_zero,true_and]
    exact ⟨MeasureTheory.integrable_zero Ω ℝ μ,mul_nonneg hCC (Even.pow_nonneg (even_two_mul order) _)⟩

end SHE.MixedPastTerminalRoughHistory
