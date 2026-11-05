module

public import SHE.ControlledTerminalPairedTime
public import SHE.PairedSourceBudget
public import SHE.MeanCurrentFields
public import SHE.MixedPastTerminalPairedPackets
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

namespace SHE.MixedPastTerminalTimeFields
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
local notation "Budget"=>MixedPastTerminalPairedPackets.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def currentEnergy (k:ℕ) (t:Fin k→ℝ):ℝ:=
  let Q:=(carrier Zero k).terminal (MixedPastTerminalSlotSpatial.anchor k t)
  ∫ω,‖S.second Q.toNNReal ω-S.first Q.toNNReal ω‖^2 ∂μ

theorem currentEnergy_measurable (k:ℕ):
    Measurable (currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k):=by
  have ha:Measurable (MixedPastTerminalSlotSpatial.anchor (k:=k)):=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  exact (ActualInterpolatedMeanFields.current_energy_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S).comp
    (measurable_real_toNNReal.comp ((carrier Zero k).terminal_measurable.comp ha))

theorem currentEnergy_nonneg (k:ℕ) (t:Fin k→ℝ):
    0≤currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k t:=
  integral_nonneg (fun _=>sq_nonneg _)

include hIJ₀ hIJ₁ in
/-- Only integrability uses this actual uniform cap; quantitative source
estimates continue to retain the TRUE currentEnergy at its own time. -/
theorem currentEnergy_cap (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hbH:b≤H)
    (B1:ℝ≥0) (hBDG1:StandardTerminalBDGPower 1 J B1) (k:ℕ) (t:Fin k→ℝ):
    currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k t≤
      MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M:=by
  let Q:=(carrier Zero k).terminal (MixedPastTerminalSlotSpatial.anchor k t)
  have hqH:Q.toNNReal≤H:=Real.toNNReal_le_iff_le_coe.mpr
    ((terminal_le_initial Zero k _).trans (by exact_mod_cast hbH))
  have hh:=MixedHeatedDifferenceMoments.current_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ Q.toNNReal hqH
    ((show (Q.toNNReal:ℝ)≤(H:ℝ) from by exact_mod_cast hqH).trans hH) 1 (by decide) B1 hBDG1
  simpa only [currentEnergy,Q,Nat.cast_one,div_one,Real.rpow_one] using hh.2

/-- A common finite coefficient separates the TRUE current and past
energies from every literal slot budget, without altering its time gain. -/
theorem budget_bound (k:ℕ) (t:Fin k→ℝ) (cs:List (Fin k×Fin (k+1)))
    (χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0) (i:Fin (k+1)):
    Budget k t cs χ A0 ν order B0 i≤
      (2*(PairedTerminalConstants.constant P κ M B0 cs χ order i)^(1/(order:ℝ))*
        PairedSourceBudget.coefficient P.holder P.exponent χ (Fin.cases ν (fun _=>0) i)*(Fintype.card (Choices 1 k):ℝ)^2)*
      (TimeAmp k t cs χ A0 ν i)^2*
      ((currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k t)^χ+
        (∫ω,‖Dir ω‖^2 ∂μ)^χ):=by
  have hE:0≤currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k t:=
    currentEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k t
  have hP:0≤∫ω,‖Dir ω‖^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  have hCp(l:Fin (k+1)):0≤2*(PairedTerminalConstants.constant P κ M B0 cs χ order l)^(1/(order:ℝ)):=
    mul_nonneg (by norm_num) (rpow_nonneg (PairedTerminalConstants.constant_nonneg
      P hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) B0 cs χ order l) _)
  refine Fin.cases ?_ (fun j=>?_) i
  · have hh:=PairedSourceBudget.root_bound (β:=P.exponent) (χ:=χ) (ν:=ν)
      (C:=2*(PairedTerminalConstants.constant P κ M B0 cs χ order 0)^(1/(order:ℝ)))
      (A:=TimeAmp k t cs χ A0 ν 0*(Fintype.card (Choices 1 k):ℝ))
      P.holder_nonneg (hCp 0) hE hP
    convert! hh using 1 <;> simp only [Fin.cases_zero,Fin.cases_succ] <;> first |rfl|ring
  · have hh:=PairedSourceBudget.rough_bound (β:=P.exponent) (χ:=χ) (ν:=0)
      (C:=2*(PairedTerminalConstants.constant P κ M B0 cs χ order j.succ)^(1/(order:ℝ)))
      (A:=TimeAmp k t cs χ A0 ν j.succ*(Fintype.card (Choices 1 k):ℝ))
      P.holder_nonneg P.exponent_pos (hCp j.succ) hE hP
    convert! hh using 1 <;> simp only [Fin.cases_zero,Fin.cases_succ] <;> first |rfl|ring

end SHE.MixedPastTerminalTimeFields
