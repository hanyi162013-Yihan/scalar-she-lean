module

public import SHE.InitialPhysicalEnvelope
public import SHE.InitialRMSGapEnvelope
public import SHE.ControlledTerminalRMSMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.InitialActualRMSEnvelope
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  ControlledFamilyProfileForest SmoothCylinders UniformSmooth CoveredControlledLaw CoveredHistoryGeometry
  PhysicalParentGeometry HistoryProductMeasure GaussianAssignmentBlocks Real Classical
open scoped NNReal BigOperators
local instance initialActualRMSEnvelope_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance initialActualRMSEnvelope_circleSigma:MeasurableSpace CircleL2:=borel _
local instance initialActualRMSEnvelope_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (T:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(T:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(T:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "L"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 T bot_le Z htarget hstop F hF hFm (0,(0,0))
local notation "Ai"=>ControlledTerminalPairedTime.amplitude P haP Λ 0 T bot_le Z htarget hstop F hF hFm
variable (κ M:ℝ)
local notation "RMS"=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=T) (hvb:=bot_le)
  (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)

/-- The actual RMS time amplitude for EVERY initial output T≤h is
bounded by ONE integrable positive original-gap kernel at scale h. -/
theorem amplitude_bound {h χ A0 ν:ℝ} (hh:0<h) (hTh:(T:ℝ)≤h)
    (hχ:0≤χ) (hχβ:χ<P.exponent) (hA0:0≤A0) (hν:0≤ν)
    (k:ℕ) (t:Fin (k+1)→ℝ) (order:ℕ) (B0:ℝ≥0):
    RMS (k+1) t ν χ A0 order B0≤
      InitialRMSGapEnvelope.kernel P κ M (ControlledOldIntervals.fraction P*P.lower)
        (uniformConstant 1) (k+1) h χ A0 ν order B0 (OrderedGapCoordinates.gaps (T:ℝ) (k+1) t):=by
  let p:=MixedPastTerminalSlotSpatial.anchor (k+1) t
  have hn:=InitialRMSGapEnvelope.kernel_nonneg (κ:=κ) (M:=M) (χ:=χ) P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) (k+1) hh.le hA0 hν order B0
    (OrderedGapCoordinates.gaps (T:ℝ) (k+1) t)
  by_cases hp:StrictHistory L (k+1) p
  · have hac:StrictHistory L (k+1) p ∧ (0:ℝ)<(carrier L (k+1)).terminal p:=
      (ControlledTerminalPairedTime.strict_active P haP Λ 0 T bot_le Z htarget hstop F hF hFm k t).mpr hp
    have ho:= (PhysicalOrderedGaps.strict_active_iff_ordered L T (fun _=>rfl) 0 le_rfl (k+1) t
      (0:HeatCircle) (fun _=>0)).mp hac
    have hg:=PhysicalOrderedGaps.old_gaps_eq L T (fun _=>rfl) (k+1) t (0:HeatCircle) (fun _=>0) hp
    change (fun j=>upper L (k+1) p j-lower L (k+1) p j)=_ at hg
    have hdp:= (OrderedGapCoordinates.ordered_iff 0 T (k+1) t).mp ho
    have hd:GapSimplexFaces.simplex h (fun j=>upper L (k+1) p j-lower L (k+1) p j):=by
      rw [hg]
      exact ⟨hdp.1,by dsimp [GapSimplexReflection.slack];linarith [hdp.2]⟩
    have hin:initialTerminal L (k+1) p≤h:=by
      change (T:ℝ)≤h
      exact hTh
    have hb(cs:List (Fin (k+1)×Fin (k+2)))
        (hc:cs∈assignments (m:=k+2) (List.finRange (k+1))) (i:Fin (k+2)):
        Ai (k+1) t cs χ A0 ν i≤InitialAssignmentEnvelope.kernel P (ControlledOldIntervals.fraction P*P.lower)
          (uniformConstant 1) cs h χ A0 ν i (OrderedGapCoordinates.gaps (T:ℝ) (k+1) t):=by
      rw [ControlledTerminalPairedTime.amplitude,if_pos hp]
      have he:=InitialPhysicalEnvelope.time_factor_bound L P
        (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
        (fun j=>(uniformConstant_pos 1 j).le) (k+1) p hp rfl hac.2 hh hχ hχβ hA0 hν hin cs hc hd i
      rw [hg] at he
      convert! he using 1
    unfold MixedPastTerminalRMS.amplitude InitialRMSGapEnvelope.kernel
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hb _ (List.get_mem _ i.1) i.2) (sqrt_nonneg _)
  · have hz:RMS (k+1) t ν χ A0 order B0=0:=by
      change ¬StrictHistory L (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t) at hp
      unfold MixedPastTerminalRMS.amplitude
      simp only [ControlledTerminalPairedTime.amplitude,if_neg hp,mul_zero,Finset.sum_const_zero]
    rw [hz]
    exact hn

end SHE.InitialActualRMSEnvelope
