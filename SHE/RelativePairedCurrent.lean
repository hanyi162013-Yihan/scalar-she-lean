module

public import SHE.ControlledPairedClockShift
public import SHE.JointObservationClockShift
public import SHE.JointWordAnalytic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.RelativePairedCurrent
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ControlledProfile SmoothCylinders UniformSmooth ShiftedWordGeometry
open scoped NNReal
local instance relativePairedCurrent_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance relativePairedCurrent_circleSigma:MeasurableSpace CircleL2:=borel _
local instance relativePairedCurrent_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type} [MeasurableSpace Ω]
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient) (Λ:ℝ)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient hA Λ h Z htarget hstop F hF hFm (0,(0,0))
local notation "Abs"=>fun v=>ControlledWordTimeShift.absoluteLevel P P.coefficient hA Λ h Z htarget hstop F hF hFm v (0,(0,0))
variable (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)

/-- The physical terminal current, written on a FIXED relative
history space. The sample and the moving past remain dependent. -/
def current (k:ℕ) (v:ℝ) (hist:History HeatCircle k) (ω:Ω):WordRecursion.State (1+k):=
  JointWordAnalytic.state (carrier Rel k) Λ
    (fun z:(ℝ×Ω)×ℝ=>U (z.1.2,z.2+z.1.1))
    (fun z:(ℝ×Ω)×ℝ=>V (z.1.2,z.2+z.1.1))
    (fun z:(ℝ×Ω)×(ℝ×HeatCircle)=>XU (z.1.2,(z.2.1+z.1.1,z.2.2)))
    (fun z:(ℝ×Ω)×(ℝ×HeatCircle)=>XV (z.1.2,(z.2.1+z.1.1,z.2.2)))
    hist (v,ω) ((carrier Rel k).terminal hist)

theorem current_measurable (hU:Measurable U) (hV:Measurable V)
    (hXU:Measurable XU) (hXV:Measurable XV) (k:ℕ):
    Measurable (fun z:ℝ×(History HeatCircle k×Ω)=>current P hA Λ h Z htarget hstop F hF hFm
      U V XU XV k z.1 z.2.1 z.2.2):=by
  have hu:Measurable (fun z:(ℝ×Ω)×ℝ=>U (z.1.2,z.2+z.1.1)):=
    hU.comp (measurable_fst.snd.prodMk (measurable_snd.add measurable_fst.fst))
  have hv:Measurable (fun z:(ℝ×Ω)×ℝ=>V (z.1.2,z.2+z.1.1)):=
    hV.comp (measurable_fst.snd.prodMk (measurable_snd.add measurable_fst.fst))
  have hxu:Measurable (fun z:(ℝ×Ω)×(ℝ×HeatCircle)=>XU (z.1.2,(z.2.1+z.1.1,z.2.2))):=
    hXU.comp (measurable_fst.snd.prodMk ((measurable_snd.fst.add measurable_fst.fst).prodMk measurable_snd.snd))
  have hxv:Measurable (fun z:(ℝ×Ω)×(ℝ×HeatCircle)=>XV (z.1.2,(z.2.1+z.1.1,z.2.2))):=
    hXV.comp (measurable_fst.snd.prodMk ((measurable_snd.fst.add measurable_fst.fst).prodMk measurable_snd.snd))
  have hm:Measurable (fun z:ℝ×(History HeatCircle k×Ω)=>
      ((z.2.1,(z.1,z.2.2)),(carrier Rel k).terminal z.2.1)):=
    (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)).prodMk
      ((carrier Rel k).terminal_measurable.comp measurable_snd.fst)
  convert! (JointWordAnalytic.state_measurable (carrier Rel k) Λ hu hv hxu hxv).comp hm using 1

/-- Exact actual-current clock identity, including the newest
physical zero-age coordinate. -/
theorem current_translation (v:ℝ≥0) (k:ℕ) (hist:History HeatCircle k) (ω:Ω):
    JointWordAnalytic.state (carrier (Abs v) k) Λ U V XU XV (shift (v:ℝ) k hist) ω
      ((carrier (Abs v) k).terminal (shift (v:ℝ) k hist))=
      current P hA Λ h Z htarget hstop F hF hFm U V XU XV k v hist ω:=by
  let K:=Abs v
  have hb:=ControlledWordTimeShift.base_shift P P.coefficient hA Λ h v (0,(0,0))
  have ht:=ControlledWordTimeShift.terminal_shift P P.coefficient hA Λ h Z htarget hstop F hF hFm v (0,(0,0))
  have hz:=ControlledWordTimeShift.observations_shift P P.coefficient hA Λ h Z htarget hstop F hF hFm v (0,(0,0))
  unfold JointWordAnalytic.state current
  rw [terminal_shift Rel K (v:ℝ) hb ht k hist,observations_shift Rel K (v:ℝ) hb ht hz k hist]
  exact JointObservationClockShift.evaluate_translation Λ (v:ℝ) ((carrier Rel k).terminal hist)
    (fun t=>U (ω,t)) (fun t=>V (ω,t)) (fun p=>XU (ω,p)) (fun p=>XV (ω,p)) _

end SHE.RelativePairedCurrent
