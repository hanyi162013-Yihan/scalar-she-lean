module

public import SHE.ControlledMeanSpatialShift
public import SHE.ShiftedOldTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledMeanInputShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth HistoryProductMeasure NativeRandomKernel
open scoped NNReal
local instance controlledMeanInputShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledMeanInputShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledMeanInputShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A) (Λ : ℝ)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "MA"=>ControlledMeanTimeShift.absoluteMean P A hA Λ h Z htarget hstop F hF hFm
local notation "MR"=>ControlledMeanTimeShift.relativeMean P A hA Λ h Z htarget hstop F hF hFm

abbrev relativeReference (p : ℝ×Inputs) :=
  ControlledReferenceLevel.referenceData P A hA Λ p.1 0 h (show (0:ℝ≥0)≤h from bot_le) p.2
abbrev absoluteReference (a : ℝ≥0×(ℝ×Inputs)) :=
  ControlledReferenceLevel.referenceData P A hA Λ a.2.1 a.1 (a.1+h) (show a.1≤a.1+h from le_self_add) a.2.2
local notation "RR"=>relativeReference P A hA Λ h
local notation "RA"=>absoluteReference P A hA Λ h

variable {W : Type} [MeasurableSpace W]

/-- Exact operator-kernel equality on a moving physical window. The
whole variable family is compared, so no representative or parameterwise
almost-everywhere substitution is used. -/
theorem familyWeightedField_translation (k : ℕ) (v : W→ℝ≥0) (p : W→Inputs)
    (q r : W→ℝ) (U D : W→CircleL2) (θ : W→ℝ) (t : W→Fin k→ℝ) :
    ActualMeanKernel.familyWeightedField RA (fun a=>Abs a.1 a.2)
      (fun w=>(v w,(θ w,p w))) k (fun _=>Λ) (fun w=>q w+(v w:ℝ)) (fun w=>r w+(v w:ℝ))
      (fun w hist=>MA (v w) (p w) k hist (q w) (U w) (D w) (θ w))
      (fun w i=>t w i+(v w:ℝ))=
    ActualMeanKernel.familyWeightedField RR Rel (fun w=>(θ w,p w)) k (fun _=>Λ) q r
      (fun w hist=>MR (p w) k hist (q w) (U w) (D w) (θ w)) t := by
  funext z
  exact ControlledMeanSpatialShift.weightedSpatial_translation P A hA Λ h Z htarget hstop F hF hFm
    (v z.1) (p z.1) k (q z.1) (r z.1) (U z.1) (D z.1) (θ z.1) (t z.1) z.2.1 z.2.2

def absoluteInput (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v : W→ℝ≥0) (p : W→Inputs) (q : W→ℝ) (U D : W→CircleL2) (θ : W→ℝ)
    (t : W→Fin k→ℝ) (V : W→DyadicApproximation.RealL2) : W→CircleL2 :=
  ActualMeanKernel.familyMeanInput RA (fun a=>Abs a.1 a.2) (fun w=>(v w,(θ w,p w))) k mass ρ hmass hρ
    (fun _=>Λ) (fun w=>q w+(v w:ℝ))
    (fun w hist=>MA (v w) (p w) k hist (q w) (U w) (D w) (θ w))
    (fun w i=>t w i+(v w:ℝ)) V

def relativeInput (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (p : W→Inputs) (q : W→ℝ) (U D : W→CircleL2) (θ : W→ℝ)
    (t : W→Fin k→ℝ) (V : W→DyadicApproximation.RealL2) : W→CircleL2 :=
  ActualMeanKernel.familyMeanInput RR Rel (fun w=>(θ w,p w)) k mass ρ hmass hρ (fun _=>Λ) q
    (fun w hist=>MR (p w) k hist (q w) (U w) (D w) (θ w)) t V

/-- Literal negative-output Hilbert mean fields agree before any
old-time, theta, sample, or current-time integration. -/
theorem input_translation (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v : W→ℝ≥0) (p : W→Inputs) (q : W→ℝ) (U D : W→CircleL2) (θ : W→ℝ)
    (t : W→Fin k→ℝ) (V : W→DyadicApproximation.RealL2) :
    absoluteInput P A hA Λ h Z htarget hstop F hF hFm k mass ρ hmass hρ v p q U D θ t V=
      relativeInput P A hA Λ h Z htarget hstop F hF hFm k mass ρ hmass hρ p q U D θ t V := by
  unfold absoluteInput relativeInput ActualMeanKernel.familyMeanInput
  rw [familyWeightedField_translation P A hA Λ h Z htarget hstop F hF hFm]

end SHE.ControlledMeanInputShift
