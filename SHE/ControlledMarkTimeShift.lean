module

public import SHE.ControlledMeanTimeShift
public import SHE.ShiftedPhysicalMarks
public import SHE.ControlledFamilyLegFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledMarkTimeShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledMarkTimeShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledMarkTimeShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledMarkTimeShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A) (Λ : ℝ)
variable (h : ℝ≥0) {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P A hA Λ h Z htarget hstop F hF hFm


open PhysicalChainArrays PhysicalScoreChain ControlledFamilyProfileForest ControlledReferenceLevel
local notation "MA"=>ControlledMeanTimeShift.absoluteMean P A hA Λ h Z htarget hstop F hF hFm
local notation "MR"=>ControlledMeanTimeShift.relativeMean P A hA Λ h Z htarget hstop F hF hFm
local notation "LPRel"=>ControlledFamilyThreeLeg.leafPoint P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
  Z htarget hstop F hF hFm
local notation "LPAbs" v=>ControlledFamilyThreeLeg.leafPoint P A hA Λ v (v+h) (show v≤v+h from le_self_add)
  (ObservationFamilyTimeShift.family (v:ℝ) Z) (ControlledWordTimeShift.translatedTargets h Z htarget v)
  (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm

theorem oldProfile_translation (v : ℝ≥0) (p : Inputs) :
    oldProfile P Λ v p=ObservationTimeShift.profile (v:ℝ) (oldProfile P Λ 0 p) := by
  funext z
  simp only [oldProfile,ControlledReferenceWindows.coefficient,ObservationTimeShift.profile,NNReal.coe_zero,sub_zero]

/-- Every erased leaf keeps the same true relative profile age under
translation of the whole physical window. -/
theorem leafPoint_translation (v : ℝ≥0) (p : Inputs) (k : ℕ) (hist : History X k) :
    (LPAbs v) p k (shift (v:ℝ) k hist)=LPRel p k hist := by
  unfold ControlledFamilyThreeLeg.leafPoint ControlledFamilyThreeLeg.lo
  have hl:=ShiftedScoreArrays.lower_shift (Rel (0,p)) (Abs v (0,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (0,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p)) k hist
  rw [hl,ShiftedScoreArrays.space_shift (v:ℝ) k hist]
  funext j
  simp only [add_sub_cancel_right,NNReal.coe_zero,sub_zero]

/-- The literal canonical covariance leg itself has exact moving-past
translation, before all original histories and theta are integrated. -/
theorem covariance_translation (v : ℝ≥0) (p : Inputs) (k : ℕ) (hist : History X k)
    (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledFamilyLegFubini.covariance P A hA Λ v (v+h) (show v≤v+h from le_self_add)
      (ObservationFamilyTimeShift.family (v:ℝ) Z) (ControlledWordTimeShift.translatedTargets h Z htarget v)
      (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm
      p k (shift (v:ℝ) k hist) (q+(v:ℝ)) U D θ=
    ControlledFamilyLegFubini.covariance P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
      Z htarget hstop F hF hFm p k hist q U D θ := by
  classical
  have ht:=ShiftedWordGeometry.terminal_shift (Rel (0,p)) (Abs v (0,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (0,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p)) k hist
  have hq : ((v:ℝ)≤q+(v:ℝ))↔0≤q:=by constructor <;> intro hq <;> linarith
  unfold ControlledFamilyLegFubini.covariance
  rw [ht]
  simp only [hq,add_lt_add_iff_right,NNReal.coe_zero]
  split_ifs
  · rw [oldProfile_translation P Λ v p]
    have hm:=ControlledMeanTimeShift.mean_translation P A hA Λ h Z htarget hstop F hF hFm v p k hist q U D θ
    dsimp only [ControlledMeanTimeShift.absoluteMean,ControlledMeanTimeShift.relativeMean] at hm
    rw [hm]
    have he : ObservationTimeShift.profile (0:ℝ) (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ))=
        (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ)) := by
      funext z
      simp only [ObservationTimeShift.profile,sub_zero]
    rw [he]
    exact ShiftedPhysicalMarks.covariance_point_shift (Rel (θ,p)) (Abs v (θ,p)) (v:ℝ)
      (ControlledWordTimeShift.base_shift P A hA Λ h v (θ,p))
      (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
      (ControlledWordTimeShift.observations_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
      (ControlledWordTimeShift.reference_shift P A hA Λ h v (θ,p)) rfl (fun _=>rfl)
      (by change (0:ℝ)≤0;exact le_rfl) v.2 (oldProfile P Λ 0 p) _ k hist q _
  · rfl

theorem baseline_translation (v : ℝ≥0) (p : Inputs) (k : ℕ) (hist : History X k)
    (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledFamilyLegFubini.baseline P A hA Λ v (v+h) (show v≤v+h from le_self_add)
      (ObservationFamilyTimeShift.family (v:ℝ) Z) (ControlledWordTimeShift.translatedTargets h Z htarget v)
      (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm
      p k (shift (v:ℝ) k hist) (q+(v:ℝ)) U D θ=
    ControlledFamilyLegFubini.baseline P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
      Z htarget hstop F hF hFm p k hist q U D θ := by
  classical
  have ht:=ShiftedWordGeometry.terminal_shift (Rel (0,p)) (Abs v (0,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (0,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p)) k hist
  have hq : ((v:ℝ)≤q+(v:ℝ))↔0≤q:=by constructor <;> intro hq <;> linarith
  unfold ControlledFamilyLegFubini.baseline
  rw [ht]
  simp only [hq,add_lt_add_iff_right,NNReal.coe_zero]
  split_ifs
  · rw [oldProfile_translation P Λ v p,leafPoint_translation P A hA Λ h Z htarget hstop F hF hFm v p k hist]
    have hm:=ControlledMeanTimeShift.mean_translation P A hA Λ h Z htarget hstop F hF hFm v p k hist q U D θ
    dsimp only [ControlledMeanTimeShift.absoluteMean,ControlledMeanTimeShift.relativeMean] at hm
    rw [hm]
    exact ShiftedPhysicalMarks.baseline_point_shift (Rel (θ,p)) (Abs v (θ,p)) (v:ℝ)
      (ControlledWordTimeShift.base_shift P A hA Λ h v (θ,p))
      (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
      (ControlledWordTimeShift.observations_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
      (ControlledWordTimeShift.reference_shift P A hA Λ h v (θ,p)) rfl (fun _=>rfl)
      (by change (0:ℝ)≤0;exact le_rfl) v.2 (oldProfile P Λ 0 p) k hist q _ _
  · rfl

end SHE.ControlledMarkTimeShift

