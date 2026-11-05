module

public import SHE.ControlledMeanInputShift
public import SHE.NativeKernelCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledMeanOldAverageShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth HistoryProductMeasure NativeRandomKernel
open scoped NNReal
local instance controlledMeanOldAverageShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledMeanOldAverageShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledMeanOldAverageShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A) (Λ : ℝ)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "IR"=>ControlledMeanInputShift.relativeInput P A hA Λ h Z htarget hstop F hF hFm
local notation "IA"=>ControlledMeanInputShift.absoluteInput P A hA Λ h Z htarget hstop F hF hFm

def relativeAt (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (p : Inputs) (q : ℝ) (U D : CircleL2) (θ : ℝ) (t : Fin k→ℝ) (V : DyadicApproximation.RealL2) : CircleL2 :=
  IR k mass ρ hmass hρ (fun _ : Unit=>p) (fun _=>q) (fun _=>U) (fun _=>D) (fun _=>θ) (fun _=>t) (fun _=>V) ()

def absoluteAt (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v : ℝ≥0) (p : Inputs) (q : ℝ) (U D : CircleL2) (θ : ℝ) (t : Fin k→ℝ) (V : DyadicApproximation.RealL2) : CircleL2 :=
  IA k mass ρ hmass hρ (fun _ : Unit=>v) (fun _=>p) (fun _=>q) (fun _=>U) (fun _=>D) (fun _=>θ)
    (fun _ i=>t i-(v:ℝ)) (fun _=>V) ()
local notation "AR"=>relativeAt P A hA Λ h Z htarget hstop F hF hFm
local notation "AA"=>absoluteAt P A hA Λ h Z htarget hstop F hF hFm

theorem relative_section {W : Type} [MeasurableSpace W] (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (p : W→Inputs) (q : W→ℝ) (U D : W→CircleL2) (θ : W→ℝ) (t : W→Fin k→ℝ)
    (V : W→DyadicApproximation.RealL2) (w : W) :
    IR k mass ρ hmass hρ p q U D θ t V w=AR k mass ρ hmass hρ (p w) (q w) (U w) (D w) (θ w) (t w) (V w) := by
  unfold relativeAt ControlledMeanInputShift.relativeInput ActualMeanKernel.familyMeanInput
  congr 1

theorem absoluteAt_translation (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v : ℝ≥0) (p : Inputs) (q : ℝ) (U D : CircleL2) (θ : ℝ) (t : Fin k→ℝ) (V : DyadicApproximation.RealL2) :
    AA k mass ρ hmass hρ v p q U D θ (fun i=>t i+(v:ℝ)) V=
      AR k mass ρ hmass hρ p q U D θ t V := by
  unfold absoluteAt
  rw [ControlledMeanInputShift.input_translation]
  simp only [add_sub_cancel_right]
  rfl

/-- Exact original old-time average equals a fixed relative-cube
Bochner average, before its norm is squared. -/
theorem old_average_translation (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v : ℝ≥0) (p : Inputs) (q : ℝ) (U D : CircleL2) (θ : ℝ) (V : DyadicApproximation.RealL2) :
    (∫ t,AA k mass ρ hmass hρ v p q U D θ t V
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) ((v:ℝ)+(h:ℝ)))))=
    ∫ t,AR k mass ρ hmass hρ p q U D θ t V
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc 0 (h:ℝ))) := by
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  apply integral_congr_ae
  filter_upwards [] with t
  exact absoluteAt_translation P A hA Λ h Z htarget hstop F hF hFm k mass ρ hmass hρ v p q U D θ t V

end SHE.ControlledMeanOldAverageShift
