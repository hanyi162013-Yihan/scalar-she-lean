module

public import SHE.PairedTimeTranslation
public import SHE.ControlledWordTimeShift
public import SHE.MixedPastTerminalRMS

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.ControlledPairedTimeTranslation
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays CoveredControlledLaw
  ShiftedWordGeometry ShiftedScoreArrays ShiftedPhysicalArrays ControlledProfile
  SmoothCylinders UniformSmooth
open scoped NNReal BigOperators
local instance controlledPairedTimeTranslation_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledPairedTimeTranslation_circleSigma:MeasurableSpace CircleL2:=borel _
local instance controlledPairedTimeTranslation_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient) (Λ:ℝ)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient hA Λ h Z htarget hstop F hF hFm (0,(0,0))
local notation "Abs" v=>ControlledWordTimeShift.absoluteLevel P P.coefficient hA Λ h Z htarget hstop F hF hFm v (0,(0,0))
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "BS" v=>ControlledWordTimeShift.base_shift P P.coefficient hA Λ h v (0,(0,0))
local notation "TS" v=>ControlledWordTimeShift.terminal_shift P P.coefficient hA Λ h Z htarget hstop F hF hFm v (0,(0,0))
local notation "ZS" v=>ControlledWordTimeShift.observations_shift P P.coefficient hA Λ h Z htarget hstop F hF hFm v (0,(0,0))

/-- The genuine minimum-gap/root-clip factor is invariant under a
physical clock translation, including all inactive configurations. -/
theorem scale_translation (v:ℝ≥0) (k:ℕ) (p:History HeatCircle k)
    (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    ControlledTerminalPairedAmplitude.scale P hA Λ v (v+h) (le_self_add)
      (ZT v) (HT v) (HS v) F hF hFm k (shift (v:ℝ) k p) cs χ A0 ν i=
    ControlledTerminalPairedAmplitude.scale P hA Λ 0 h bot_le Z htarget hstop F hF hFm k p cs χ A0 ν i:=by
  change PairedTerminalTimeFields.factor P
    (fun j=>lower (Abs v) k (shift (v:ℝ) k p) j-(v:ℝ))
    (fun j=>upper (Abs v) k (shift (v:ℝ) k p) j-(v:ℝ))
    (fun j=>targets (Abs v) k (shift (v:ℝ) k p) (leafIndex k (fun i=>i) j)-(v:ℝ)) cs χ A0 ν i=_
  rw [lower_shift Rel (Abs v) (v:ℝ) (BS v) (TS v) k p,
    upper_shift Rel (Abs v) (v:ℝ) (BS v) (TS v) k p,
    targets_shift Rel (Abs v) (v:ℝ) (BS v) (TS v) (ZS v) k p]
  simp only [add_sub_cancel_right,ControlledTerminalPairedAmplitude.scale,NNReal.coe_zero,sub_zero]

theorem timeAmplitude_translation (v:ℝ≥0) (k:ℕ) (t:Fin k→ℝ)
    (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    MixedPastTerminalSlotSpatial.timeAmplitude Λ P hA v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k (fun j=>t j+(v:ℝ)) cs χ A0 ν i=
    MixedPastTerminalSlotSpatial.timeAmplitude Λ P hA 0 h bot_le
      Z htarget hstop F hF hFm k t cs χ A0 ν i:=by
  have he:=PairedTimeTranslation.separated_shift (v:=(v:ℝ)) k (0:HeatCircle) t (fun _=>0)
  unfold MixedPastTerminalSlotSpatial.timeAmplitude MixedPastTerminalSlotSpatial.anchor
  rw [←he,PairedTimeTranslation.timeWeight_shift Rel (Abs v) (v:ℝ) (BS v) (TS v),
    scale_translation P hA Λ h Z htarget hstop F hF hFm v k]

/-- The strict-supported ORIGINAL old-time amplitude is exactly the
relative one; neither ordering domains nor root clips are enlarged. -/
theorem amplitude_translation (v:ℝ≥0) (k:ℕ) (t:Fin k→ℝ)
    (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    ControlledTerminalPairedTime.amplitude P hA Λ v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k (fun j=>t j+(v:ℝ)) cs χ A0 ν i=
    ControlledTerminalPairedTime.amplitude P hA Λ 0 h bot_le
      Z htarget hstop F hF hFm k t cs χ A0 ν i:=by
  have he:=PairedTimeTranslation.separated_shift (v:=(v:ℝ)) k (0:HeatCircle) t (fun _=>0)
  have hs:=PairedTimeTranslation.strict_shift Rel (Abs v) (v:ℝ) (BS v) (TS v) k
    (MixedPastTerminalSlotSpatial.anchor k t)
  unfold ControlledTerminalPairedTime.amplitude
  rw [show MixedPastTerminalSlotSpatial.anchor k (fun j=>t j+(v:ℝ))=
      shift (v:ℝ) k (MixedPastTerminalSlotSpatial.anchor k t) from he.symm,hs]
  rw [timeAmplitude_translation P hA Λ h Z htarget hstop F hF hFm v k t cs χ A0 ν i]

theorem rms_translation (κ M:ℝ) (v:ℝ≥0) (k:ℕ) (t:Fin k→ℝ)
    (χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0):
    MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) Λ P hA v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k (fun j=>t j+(v:ℝ)) ν χ A0 order B0=
    MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) Λ P hA 0 h bot_le
      Z htarget hstop F hF hFm k t ν χ A0 order B0:=by
  unfold MixedPastTerminalRMS.amplitude
  dsimp only
  simp_rw [amplitude_translation P hA Λ h Z htarget hstop F hF hFm v k t]

end SHE.ControlledPairedTimeTranslation
