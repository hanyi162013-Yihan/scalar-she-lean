module

public import SHE.MixedPastTerminalTimeFields
public import SHE.PairedRMSWeights
public import SHE.MixedPastTerminalPairedAverage
public import SHE.ControlledTerminalPairedTime
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

namespace SHE.MixedPastTerminalRMS
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
local notation "Ai"=>ControlledTerminalPairedTime.amplitude P haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Budget"=>MixedPastTerminalPairedPackets.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "En"=>MixedPastTerminalTimeFields.currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def amplitude (k:ℕ) (t:Fin k→ℝ) (ν χ A0:ℝ) (order:ℕ) (B0:ℝ≥0):ℝ:=
  let cs:=assignments (m:=k+1) (List.finRange k)
  (1/2:ℝ)^k*sqrt ((cs.length*(k+1):ℕ):ℝ)*
    ∑i:Fin cs.length×Fin (k+1),
      sqrt (PairedRMSWeights.coefficient P κ M B0 (cs.get i.1) χ ν order i.2)*
        Ai k t (cs.get i.1) χ A0 ν i.2

theorem single_nonneg (k:ℕ) (t:Fin k→ℝ) (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    0≤Ai k t cs χ A0 ν i:=by
  unfold ControlledTerminalPairedTime.amplitude
  split_ifs with hp
  · exact mul_nonneg (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k _ hp) (abs_nonneg _)
  · exact le_rfl

theorem amplitude_nonneg (k:ℕ) (t:Fin k→ℝ) (ν χ A0:ℝ) (order:ℕ) (B0:ℝ≥0):
    0≤amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t ν χ A0 order B0:=by
  unfold amplitude
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sqrt_nonneg _) (single_nonneg Λ P haP v b hvb Z htarget hstop F hF hFm k t _ χ A0 ν i.2)

theorem amplitude_measurable (k:ℕ) (ν χ A0:ℝ) (order:ℕ) (B0:ℝ≥0):
    Measurable (fun t=>amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t ν χ A0 order B0):=by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (ControlledTerminalPairedTime.amplitude_measurable
    P haP Λ v b hvb Z htarget hstop F hF hFm k _ χ A0 ν i.2)

theorem amplitude_integrable (hvb':v<b) (k:ℕ) {A0 ν χ:ℝ}
    (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ<P.exponent) (order:ℕ) (B0:ℝ≥0):
    Integrable (fun t=>amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
      (k+1) t ν χ A0 order B0) (Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))):=by
  unfold amplitude
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  have hc:=List.get_mem (assignments (m:=k+2) (List.finRange (k+1))) i.1
  refine Fin.cases ?_ (fun j=>?_) i.2
  · exact (ControlledTerminalPairedTime.root_integral P haP Λ v b hvb Z htarget hstop F hF hFm hvb' k _ hc hA0 hν).1
  · exact (ControlledTerminalPairedTime.rough_integral P haP Λ v b hvb Z htarget hstop F hF hFm hvb' k _ hc j hχ hχβ hA0 hν).1

/-- The whole finite assignment budget fits ONE genuine RMS time
amplitude. Every old min-gap/root-clip/full-age factor remains in its
original summand and current/past energy is kept separate from it. -/
theorem budget_sum_bound (k:ℕ) (t:Fin k→ℝ)
    (hp:StrictHistory Zero k (MixedPastTerminalSlotSpatial.anchor k t))
    (ν χ A0:ℝ) (order:ℕ) (B0:ℝ≥0):
    let cs:=assignments (m:=k+1) (List.finRange k)
    ((1/2:ℝ)^k)^2*((cs.length*(k+1):ℕ):ℝ)*
      (∑c:Fin cs.length,∑i:Fin (k+1),Budget k t (cs.get c) χ A0 ν order B0 i)≤
      (amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
        k t ν χ A0 order B0)^2*(En k t^χ+(∫ω,‖Dir ω‖^2 ∂μ)^χ):=by
  intro cs
  let I:=Fin cs.length×Fin (k+1)
  let coeff:=fun i:I=>PairedRMSWeights.coefficient P κ M B0 (cs.get i.1) χ ν order i.2
  let bb:=fun i:I=>sqrt (coeff i)*Ai k t (cs.get i.1) χ A0 ν i.2
  let E:=En k t^χ+(∫ω,‖Dir ω‖^2 ∂μ)^χ
  have hE:0≤E:=add_nonneg (rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _)
    (rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _)
  have hc(i:I):0≤coeff i:=PairedRMSWeights.coefficient_nonneg P hκ.le
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) B0 _ χ ν order i.2
  have hbb(i:I):0≤bb i:=mul_nonneg (sqrt_nonneg _)
    (single_nonneg Λ P haP v b hvb Z htarget hstop F hF hFm k t _ χ A0 ν i.2)
  have hb(i:I):Budget k t (cs.get i.1) χ A0 ν order B0 i.2≤bb i^2*E:=by
    have hh:=MixedPastTerminalTimeFields.budget_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k t (cs.get i.1) χ A0 ν order B0 i.2
    have hai:Ai k t (cs.get i.1) χ A0 ν i.2=TimeAmp k t (cs.get i.1) χ A0 ν i.2:=by
      rw [ControlledTerminalPairedTime.amplitude,if_pos hp]
    change _≤coeff i*(TimeAmp k t (cs.get i.1) χ A0 ν i.2)^2*E at hh
    rw [←hai] at hh
    simpa only [bb,mul_pow,Real.sq_sqrt (hc i)] using hh
  have hs:∑i:I,Budget k t (cs.get i.1) χ A0 ν order B0 i.2≤(∑i:I,bb i)^2*E:=by
    calc
      _≤∑i:I,bb i^2*E:=Finset.sum_le_sum (fun i _=>hb i)
      _=(∑i:I,bb i^2)*E:=by rw [Finset.sum_mul]
      _≤_:=mul_le_mul_of_nonneg_right (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _=>hbb i)) hE
  have hz:=mul_le_mul_of_nonneg_left hs
    (show 0≤((1/2:ℝ)^k)^2*((cs.length*(k+1):ℕ):ℝ) by positivity)
  have hsum:(∑c:Fin cs.length,∑i:Fin (k+1),Budget k t (cs.get c) χ A0 ν order B0 i)=
      ∑i:I,Budget k t (cs.get i.1) χ A0 ν order B0 i.2:=
    (Fintype.sum_prod_type (fun i:I=>Budget k t (cs.get i.1) χ A0 ν order B0 i.2)).symm
  rw [hsum]
  apply hz.trans_eq
  simp only [amplitude,bb,coeff,E,cs,mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg ((assignments (m:=k+1) (List.finRange k)).length*(k+1)))]
  ring

end SHE.MixedPastTerminalRMS
