module

public import SHE.ControlledWordTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledMeanTimeShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledMeanTimeShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledMeanTimeShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledMeanTimeShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A) (Λ : ℝ)
variable (h : ℝ≥0) {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P A hA Λ h Z htarget hstop F hF hFm

abbrev absoluteMean (v : ℝ≥0) (p : Inputs) (k : ℕ) (hist : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) :=
  ControlledFamilyActualTransfer.mean P A hA Λ v (v+h) (show v≤v+h from le_self_add)
    (ObservationFamilyTimeShift.family (v:ℝ) Z) (ControlledWordTimeShift.translatedTargets h Z htarget v)
    (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm p k hist (q+(v:ℝ)) U D θ

abbrev relativeMean (p : Inputs) (k : ℕ) (hist : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) :=
  ControlledFamilyActualTransfer.mean P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
    Z htarget hstop F hF hFm p k hist q U D θ

local notation "MA"=>absoluteMean P A hA Λ h Z htarget hstop F hF hFm
local notation "MR"=>relativeMean P A hA Λ h Z htarget hstop F hF hFm

/-- The entire literal joint mean, including every stop damper, is
unchanged by translating the physical past and every original target. -/
theorem mean_translation (v : ℝ≥0) (p : Inputs) (k : ℕ) (hist : History X k)
    (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    MA v p k (shift (v:ℝ) k hist) q U D θ=MR p k hist q U D θ := by
  have ho:=ShiftedWordGeometry.observations_shift (Rel (0,p)) (Abs v (0,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (0,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p))
    (ControlledWordTimeShift.observations_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p)) k hist
  unfold absoluteMean relativeMean ControlledFamilyActualTransfer.mean ControlledFamilyThreeLeg.center
  rw [ho]
  apply PiLp.ext
  intro i
  simp only [ControlledJointWeightedWord.jointMeanVector_apply,
    ObservationTimeShift.observations_stop,ObservationTimeShift.observations_target,
    ObservationTimeShift.observations_center,add_sub_add_right_eq_sub]

/-- The actual terminal mean kernel itself is preserved, with its
q-law and original stop-dependent joint current, rather than merely an
auxiliary kernel with a supplied unrelated Gaussian mean. -/
theorem weighted_actual_mean_translation (v : ℝ≥0) (p : Inputs) (k : ℕ)
    (hist : History X k) (q r : ℝ) (U D : CircleL2) (θ : ℝ) (y : HeatCircle) :
    ActualMeanKernel.weightedPoint (Abs v (θ,p)) k Λ (q+(v:ℝ)) (r+(v:ℝ))
      (fun hist=>MA v p k hist q U D θ) (shift (v:ℝ) k hist) y=
    ActualMeanKernel.weightedPoint (Rel (θ,p)) k Λ q r (fun hist=>MR p k hist q U D θ) hist y := by
  have hh:=ControlledWordTimeShift.weightedPoint_translation P A hA Λ h Z htarget hstop F hF hFm
    v (θ,p) k q r (fun hist=>MA v p k hist q U D θ) hist y
  simpa only [mean_translation P A hA Λ h Z htarget hstop F hF hFm] using hh

end SHE.ControlledMeanTimeShift
