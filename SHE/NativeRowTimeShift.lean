module

public import SHE.ControlledMeanSpatialShift
public import SHE.SeparatedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.ShiftedWordCalculus
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry GaussianConvolution
variable {X:Type}[MeasurableSpace X]{R Q:ReferenceData}{n:ℕ}
variable (L:Level R X n)(K:Level Q X n)(v:ℝ)
variable (hb:Q.base=R.base+v)(hT:∀x,K.terminal x=L.terminal x+v)
variable (hZ:∀x,K.observations.observations x=ObservationTimeShift.observations v (L.observations.observations x))
variable (hc:Q.reference=ObservationTimeShift.profile v R.reference)
variable (hV:Q.totalVariance=R.totalVariance)(hF:∀x,K.test x=L.test x)

include hb hT hZ hc hV hF in
/-- The unweighted native row translates independently of the damping
in the controlled reference profile, with the original law retained. -/
theorem rowPoint_shift (k:ℕ)(q r:ℝ)(m:History X k→WordRecursion.State (n+k))
    (p:History X k)(y:HeatCircle):
    ActualMeanKernel.rowPoint K k (q+v) (r+v) m (shift v k p) y=
      ActualMeanKernel.rowPoint L k q r (fun p=>m (shift v k p)) p y:=by
  classical
  unfold ActualMeanKernel.rowPoint
  rw [terminal_shift L K v hb hT k p]
  simp only [add_lt_add_iff_right]
  split_ifs with ha
  · have hcov:=covariance_shift L K v hb hT hZ hc k p q
    rw [terminal_shift L K v hb hT k p] at hcov
    rw [hcov,test_shift L K v hb hT hZ hc hV hF k p,
      observations_shift L K v hb hT hZ k p,ObservationTimeShift.heatRow_translation]
  · rfl

end SHE.ShiftedWordCalculus

namespace SHE.ControlledMeanTimeShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ControlledProfile SmoothCylinders UniformSmooth HistoryProductMeasure
open scoped NNReal
local instance nativeRowTimeShift_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeRowTimeShift_circleSigma:MeasurableSpace CircleL2:=borel _
local instance nativeRowTimeShift_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)(Λ:ℝ)
variable (h:ℝ≥0){X:Type}[MeasurableSpace X]{n:ℕ}(Z:VariableObservations.Family X n)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State n=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P A hA Λ h Z htarget hstop F hF hFm
local notation "MA"=>absoluteMean P A hA Λ h Z htarget hstop F hF hFm
local notation "MR"=>relativeMean P A hA Λ h Z htarget hstop F hF hFm

theorem row_actual_mean_translation (v:ℝ≥0)(p:Inputs)(k:ℕ)(hist:History X k)
    (q r:ℝ)(U D:CircleL2)(θ:ℝ)(y:HeatCircle):
    ActualMeanKernel.rowPoint (Abs v (θ,p)) k (q+(v:ℝ)) (r+(v:ℝ))
      (fun hist=>MA v p k hist q U D θ) (shift (v:ℝ) k hist) y=
      ActualMeanKernel.rowPoint (Rel (θ,p)) k q r (fun hist=>MR p k hist q U D θ) hist y:=by
  have hh:=ShiftedWordCalculus.rowPoint_shift (Rel (θ,p)) (Abs v (θ,p)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P A hA Λ h v (θ,p))
    (ControlledWordTimeShift.terminal_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
    (ControlledWordTimeShift.observations_shift P A hA Λ h Z htarget hstop F hF hFm v (θ,p))
    (ControlledWordTimeShift.reference_shift P A hA Λ h v (θ,p)) rfl (fun _=>rfl)
    k q r (fun hist=>MA v p k hist q U D θ) hist y
  simpa only [mean_translation P A hA Λ h Z htarget hstop F hF hFm] using hh

theorem rowSpatial_translation (v:ℝ≥0)(p:Inputs)(k:ℕ)(q r:ℝ)(U D:CircleL2)
    (θ:ℝ)(t:Fin k→ℝ)(y:HeatCircle)(x:X):
    ActualMeanKernel.rowSpatial (Abs v (θ,p)) k (q+(v:ℝ)) (r+(v:ℝ))
      (fun _:Unit=>fun hist=>MA v p k hist q U D θ) (fun i=>t i+(v:ℝ)) () y x=
      ActualMeanKernel.rowSpatial (Rel (θ,p)) k q r
        (fun _:Unit=>fun hist=>MR p k hist q U D θ) t () y x:=by
  unfold ActualMeanKernel.rowSpatial
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←ControlledMeanSpatialShift.shift_separated]
  exact row_actual_mean_translation P A hA Λ h Z htarget hstop F hF hFm
    v p k (separated k (x,t,z)) q r U D θ y

end SHE.ControlledMeanTimeShift
