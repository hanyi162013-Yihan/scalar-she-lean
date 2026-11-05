module

public import SHE.ControlledMarkTimeShift
public import SHE.ControlledMeanTimeShift
public import SHE.ShiftedPhysicalMarks
public import SHE.ControlledFamilyLegFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledMeanLegShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledMeanLegShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledMeanLegShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledMeanLegShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

/-- The entire original-stop physical mean leg is invariant under the
moving-past clock translation, before every history or theta average. -/
theorem mean_translation (v : ℝ≥0) (p : Inputs) (k : ℕ) (hist : History X k)
    (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledFamilyLegFubini.mean P A hA Λ v (v+h) (show v≤v+h from le_self_add)
      (ObservationFamilyTimeShift.family (v:ℝ) Z) (ControlledWordTimeShift.translatedTargets h Z htarget v)
      (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm
      p k (shift (v:ℝ) k hist) (q+(v:ℝ)) U D θ=
    ControlledFamilyLegFubini.mean P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
      Z htarget hstop F hF hFm p k hist q U D θ := by
  classical
  have ht:=ShiftedWordGeometry.terminal_shift (Rel (0,p)) (Abs v (0,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (0,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p)) k hist
  have ho:=ShiftedWordGeometry.observations_shift (Rel (0,p)) (Abs v (0,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (0,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p))
    (ControlledWordTimeShift.observations_shift P A hA Λ h Z htarget hstop F hF hFm v (0,p)) k hist
  have hq : ((v:ℝ)≤q+(v:ℝ))↔0≤q:=by constructor <;> intro hq <;> linarith
  unfold ControlledFamilyLegFubini.mean
  rw [ht]
  simp only [hq,add_lt_add_iff_right,NNReal.coe_zero]
  split_ifs
  · have hcov:=ShiftedWordCalculus.covariance_shift (Rel (θ,p)) (Abs v (θ,p)) (v:ℝ)
      (ControlledWordTimeShift.base_shift P A hA Λ h v (θ,p))
      (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
      (ControlledWordTimeShift.observations_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
      (ControlledWordTimeShift.reference_shift P A hA Λ h v (θ,p)) k hist q
    have hm:=ControlledMeanTimeShift.mean_translation P A hA Λ h Z htarget hstop F hF hFm v p k hist q U D θ
    dsimp only [ControlledMeanTimeShift.absoluteMean,ControlledMeanTimeShift.relativeMean] at hm
    rw [hcov,ControlledWordTimeShift.test_translation P A hA Λ h Z htarget hstop F hF hFm,hm]
    congr 1
    apply PiLp.ext
    intro i
    simp only [PhysicalMeanRange.dampedDirection,PiLp.toLp_apply,ControlledFamilyThreeLeg.sigma,
      ControlledFamilyThreeLeg.target,StoppedGaussianScore.nativeCenter,ControlledFamilyThreeLeg.center,ho,
      ObservationTimeShift.observations_stop,ObservationTimeShift.observations_target,
      ObservationTimeShift.observations_center,NNReal.coe_zero,sub_zero,add_sub_cancel_right]
  · rfl

end SHE.ControlledMeanLegShift

