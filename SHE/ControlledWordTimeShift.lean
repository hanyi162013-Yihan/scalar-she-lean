module

public import SHE.ShiftedWordCalculus
public import SHE.ObservationFamilyTimeShift
public import SHE.ControlledFamilyActualTransfer

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledWordTimeShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledWordTimeShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledWordTimeShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledWordTimeShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A) (Λ : ℝ)
variable (h : ℝ≥0) {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))

def translatedTargets (v : ℝ≥0) (x : X) (i : Fin n) :
    ((v+h:ℝ≥0):ℝ)≤((ObservationFamilyTimeShift.family (v:ℝ) Z).observations x i).target := by
  change ((v+h:ℝ≥0):ℝ)≤(Z.observations x i).target+(v:ℝ)
  rw [NNReal.coe_add]
  linarith [htarget x i]

def translatedStops (v : ℝ≥0) (x : X) (i : Fin n) :
    ((v+h:ℝ≥0):ℝ)≤((ObservationFamilyTimeShift.family (v:ℝ) Z).observations x i).stop := by
  change ((v+h:ℝ≥0):ℝ)≤(Z.observations x i).stop+(v:ℝ)
  rw [NNReal.coe_add]
  linarith [hstop x i]

abbrev relativeLevel (p : ℝ×Inputs) := ControlledReferenceThetaGeometry.level P A hA Λ 0 h
  (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm p

/-- The literal canonical controlled level on the moving physical
window [v,v+h], with every original observation translated separately. -/
abbrev absoluteLevel (v : ℝ≥0) (p : ℝ×Inputs) := ControlledReferenceThetaGeometry.level P A hA Λ v (v+h)
  (show v≤v+h from le_self_add) (ObservationFamilyTimeShift.family (v:ℝ) Z)
  (translatedTargets h Z htarget v) (translatedStops h Z hstop v) F hF hFm p
local notation "Rel"=>relativeLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>absoluteLevel P A hA Λ h Z htarget hstop F hF hFm

theorem base_shift (v : ℝ≥0) (p : ℝ×Inputs) :
    (ControlledReferenceLevel.referenceData P A hA Λ p.1 v (v+h) (show v≤v+h from le_self_add) p.2).base=
      (ControlledReferenceLevel.referenceData P A hA Λ p.1 0 h (show (0:ℝ≥0)≤h from bot_le) p.2).base+(v:ℝ) := by
  change (v:ℝ)=(0:ℝ)+(v:ℝ)
  exact (zero_add _).symm

theorem terminal_shift (v : ℝ≥0) (p : ℝ×Inputs) (x : X) : (Abs v p).terminal x=(Rel p).terminal x+(v:ℝ) := by
  change ((v+h:ℝ≥0):ℝ)=(h:ℝ)+(v:ℝ)
  rw [NNReal.coe_add,add_comm]

theorem observations_shift (v : ℝ≥0) (p : ℝ×Inputs) (x : X) :
    (Abs v p).observations.observations x=ObservationTimeShift.observations (v:ℝ) ((Rel p).observations.observations x) := rfl

theorem reference_shift (v : ℝ≥0) (p : ℝ×Inputs) :
    (ControlledReferenceLevel.referenceData P A hA Λ p.1 v (v+h) (show v≤v+h from le_self_add) p.2).reference=
      ObservationTimeShift.profile (v:ℝ)
        (ControlledReferenceLevel.referenceData P A hA Λ p.1 0 h (show (0:ℝ≥0)≤h from bot_le) p.2).reference := by
  funext z
  change ControlledProfile.profile P Λ p.2.1 p.2.2 (p.1,(z.1-(v:ℝ),z.2))=
    ControlledProfile.profile P Λ p.2.1 p.2.2 (p.1,((z.1-(v:ℝ))-0,z.2))
  rw [sub_zero]

/-- Actual finite recursive Gaussian tests obey exact moving-past
translation; this identifies the relative construction pointwise. -/
theorem test_translation (v : ℝ≥0) (p : ℝ×Inputs) (k : ℕ) (hist : History X k) :
    UncutSmoothWords.test (Abs v p) k (shift (v:ℝ) k hist)=UncutSmoothWords.test (Rel p) k hist :=
  ShiftedWordCalculus.test_shift (Rel p) (Abs v p) (v:ℝ)
    (base_shift P A hA Λ h v p) (terminal_shift P A hA Λ h Z htarget hstop F hF hFm v p)
    (observations_shift P A hA Λ h Z htarget hstop F hF hFm v p)
    (reference_shift P A hA Λ h v p) rfl (fun _=>rfl) k hist

theorem weightedPoint_translation (v : ℝ≥0) (p : ℝ×Inputs) (k : ℕ) (q r : ℝ)
    (m : History X k→WordRecursion.State (n+k)) (hist : History X k) (y : HeatCircle) :
    ActualMeanKernel.weightedPoint (Abs v p) k Λ (q+(v:ℝ)) (r+(v:ℝ)) m (shift (v:ℝ) k hist) y=
      ActualMeanKernel.weightedPoint (Rel p) k Λ q r (fun hist=>m (shift (v:ℝ) k hist)) hist y :=
  ShiftedWordCalculus.weightedPoint_shift (Rel p) (Abs v p) (v:ℝ)
    (base_shift P A hA Λ h v p) (terminal_shift P A hA Λ h Z htarget hstop F hF hFm v p)
    (observations_shift P A hA Λ h Z htarget hstop F hF hFm v p)
    (reference_shift P A hA Λ h v p) rfl (fun _=>rfl) k Λ q r m hist y

end SHE.ControlledWordTimeShift
