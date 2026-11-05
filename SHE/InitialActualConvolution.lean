module

public import SHE.InitialActualRMSEnvelope
public import SHE.InitialGapCurrent
public import SHE.ControlledScalarReference

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.InitialActualConvolution
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalParentGeometry GaussianAssignmentBlocks Real Classical
open scoped NNReal ENNReal BigOperators
local instance initialActualConvolution_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance initialActualConvolution_circleSigma:MeasurableSpace CircleL2:=borel _
local instance initialActualConvolution_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ κ M:ℝ) (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformSmooth.UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "ZZ" T:max=>ControlledScalarReference.observations T
local notation "RMS" T:max=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=T)
  (hvb:=bot_le) (Z:=ZZ T) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl) (F:=F) (hF:=hF) (hFm:=hFm)
local notation "K" k:max h:max χ:max A0:max ν:max order:max B0:max=>InitialRMSGapEnvelope.kernel P κ M
  (ControlledOldIntervals.fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1) k h χ A0 ν order B0

/-- The literal actual initial-triangle RMS/current integral has the
SAME finite high-order budget and counts true current energy exactly
once. No initial coarse strip or independent current bound is used. -/
theorem energy_bound (E:ℝ→ℝ≥0∞) (hE:Measurable E) {h H χ A0 ν:ℝ}
    (hh:0<h) (hhH:h≤H) (hχ:0≤χ) (hχβ:χ<P.exponent) (hA0:0≤A0) (hν:0≤ν)
    (k:ℕ) (order:ℕ) (B0:ℝ≥0):
    (∫⁻T in Ioc (0:ℝ) h,∫⁻t:Fin (k+1)→ℝ,
      ENNReal.ofReal ((RMS T.toNNReal) (k+1) t ν χ A0 order B0)*
        MovingPastFractional.powerWindow H χ E (OrderedGapCoordinates.boundary T (k+1) t)
        ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) T)))≤
      ENNReal.ofReal (PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
        (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0)*
        ((∫⁻r in Ioc (0:ℝ) H,E r)^χ*(ENNReal.ofReal H)^(1-χ)):=by
  let KK:= (K (k+1) h χ A0 ν order B0)
  have hKm:Measurable KK:=InitialRMSGapEnvelope.kernel_measurable P κ M _ _ (k+1) h χ A0 ν order B0
  have hK0(d):0≤KK d:=InitialRMSGapEnvelope.kernel_nonneg (κ:=κ) (M:=M) (χ:=χ) P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
    (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) hh.le hA0 hν order B0 d
  have hKi:=InitialRMSGapEnvelope.kernel_integral (κ:=κ) (M:=M) P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
    (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) hh hχ hχβ hA0 hν order B0
  have hdom:(∫⁻T in Ioc (0:ℝ) h,∫⁻t:Fin (k+1)→ℝ,
      ENNReal.ofReal ((RMS T.toNNReal) (k+1) t ν χ A0 order B0)*
        MovingPastFractional.powerWindow H χ E (OrderedGapCoordinates.boundary T (k+1) t)
        ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) T)))≤
      ∫⁻T in Ioc (0:ℝ) h,∫⁻t:Fin (k+1)→ℝ,if OrderedGapCoordinates.ordered 0 T (k+1) t then
        ENNReal.ofReal (KK (OrderedGapCoordinates.gaps T (k+1) t))*
          MovingPastFractional.powerWindow H χ E (OrderedGapCoordinates.boundary T (k+1) t) else 0:=by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with T hT
    have hcoe:(T.toNNReal:ℝ)=T:=Real.coe_toNNReal _ hT.1.le
    have hm:Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) T))≤(volume:Measure (Fin (k+1)→ℝ)):=by
      rw [←Measure.restrict_pi_pi (μ:=fun _:Fin (k+1)=>(volume:Measure ℝ)) (fun _=>Ioc (0:ℝ) T)]
      exact Measure.restrict_le_self
    apply (lintegral_mono' hm le_rfl).trans
    apply lintegral_mono
    intro t
    dsimp only
    by_cases ho:OrderedGapCoordinates.ordered 0 T (k+1) t
    · rw [if_pos ho]
      have he:=InitialActualRMSEnvelope.amplitude_bound P haP Λ T.toNNReal (ZZ T.toNNReal)
        (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm κ M hh (by simpa only [hcoe] using hT.2)
        hχ hχβ hA0 hν k t order B0
      have he':(RMS T.toNNReal) (k+1) t ν χ A0 order B0≤KK (OrderedGapCoordinates.gaps T (k+1) t):=
        he.trans_eq (congrArg (fun r:ℝ=>KK (OrderedGapCoordinates.gaps r (k+1) t)) hcoe)
      simpa only [mul_comm] using mul_le_mul_right (ENNReal.ofReal_le_ofReal he') (MovingPastFractional.powerWindow H χ E (OrderedGapCoordinates.boundary T (k+1) t))
    · rw [if_neg ho]
      let L:=ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 T.toNNReal bot_le
        (ZZ T.toNNReal) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,(0,0))
      have hn:¬PhysicalParentGeometry.StrictHistory L (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t):=by
        intro hp
        have ha:=(ControlledTerminalPairedTime.strict_active P haP Λ 0 T.toNNReal bot_le
          (ZZ T.toNNReal) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k t).mpr hp
        have hor:=(PhysicalOrderedGaps.strict_active_iff_ordered L T (fun _=>hcoe) 0 le_rfl (k+1) t
          (0:HeatCircle) (fun _=>0)).mp ha
        exact ho hor
      dsimp only [L] at hn
      simp only [MixedPastTerminalRMS.amplitude,ControlledTerminalPairedTime.amplitude,if_neg hn,
        mul_zero,Finset.sum_const_zero,ENNReal.ofReal_zero,zero_mul]
      exact le_rfl
  have hc:=InitialGapCurrent.energy_bound (k+1) (fun d=>ENNReal.ofReal (KK d)) E
    (ENNReal.measurable_ofReal.comp hKm) hE hχ (hχβ.le.trans P.exponent_le_one) hhH
  refine hdom.trans (hc.trans ?_)
  have hm:(∫⁻d:Fin (k+1)→ℝ,ENNReal.ofReal (KK d))≤ENNReal.ofReal
      (PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
        (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0):=by
    rw [←ofReal_integral_eq_lintegral_ofReal hKi.1 (ae_of_all _ hK0)]
    exact ENNReal.ofReal_le_ofReal hKi.2
  simpa only [mul_comm] using mul_le_mul_right hm ((∫⁻r in Ioc (0:ℝ) H,E r)^χ*(ENNReal.ofReal H)^(1-χ))

end SHE.InitialActualConvolution
