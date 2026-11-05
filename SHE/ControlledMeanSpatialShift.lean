module

public import SHE.ControlledMeanTimeShift
public import SHE.FamilyMeanInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
noncomputable section
namespace SHE.ControlledMeanSpatialShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth HistoryProductMeasure
open scoped NNReal
local instance controlledMeanSpatialShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledMeanSpatialShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledMeanSpatialShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

theorem shift_assemble {X : Type} [MeasurableSpace X] (v : ℝ) (k : ℕ)
    (x : X) (nodes : Fin k→ℝ×HeatCircle) :
    shift v k (assemble k (x,nodes))=assemble k (x,fun i=>((nodes i).1+v,(nodes i).2)) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    change (shift v k (assemble k (x,fun i=>nodes i.succ)),(nodes 0).1+v,(nodes 0).2)=_
    rw [ih]
    rfl

/-- Translating all old times leaves the genuine old spatial product
coordinates, their order, and their Haar measure unchanged. -/
theorem shift_separated {X : Type} [MeasurableSpace X] (v : ℝ) (k : ℕ)
    (x : X) (t : Fin k→ℝ) (z : Fin k→HeatCircle) :
    shift v k (separated k (x,t,z))=separated k (x,(fun i=>t i+v),z) :=
  shift_assemble v k x (fun i=>(t i,z i))

variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A) (Λ : ℝ)
variable (h : ℝ≥0) {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "MA"=>ControlledMeanTimeShift.absoluteMean P A hA Λ h Z htarget hstop F hF hFm
local notation "MR"=>ControlledMeanTimeShift.relativeMean P A hA Λ h Z htarget hstop F hF hFm

/-- Exact translation of the actual old-space averaged weighted mean
kernel; no Gaussian mean or covariance is replaced in this equality. -/
theorem weightedSpatial_translation (v : ℝ≥0) (p : Inputs) (k : ℕ)
    (q r : ℝ) (U D : CircleL2) (θ : ℝ) (t : Fin k→ℝ) (y : HeatCircle) (x : X) :
    ActualMeanKernel.weightedSpatial (Abs v (θ,p)) k Λ (q+(v:ℝ)) (r+(v:ℝ))
      (fun _ : Unit=>fun hist=>MA v p k hist q U D θ) (fun i=>t i+(v:ℝ)) () y x=
    ActualMeanKernel.weightedSpatial (Rel (θ,p)) k Λ q r
      (fun _ : Unit=>fun hist=>MR p k hist q U D θ) t () y x := by
  unfold ActualMeanKernel.weightedSpatial
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←shift_separated]
  exact ControlledMeanTimeShift.weighted_actual_mean_translation P A hA Λ h Z htarget hstop F hF hFm
    v p k (separated k (x,t,z)) q r U D θ y

end SHE.ControlledMeanSpatialShift
