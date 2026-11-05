module
public import SHE.ControlledScalarCovarianceTailEnergy
public import SHE.VariableObservations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.InitialScalarCovarianceTail
open Set MeasureTheory ControlledProfile StoppedFourier WordRecursion
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
abbrev Parameter:=((Inputs×ℝ)×ℝ)×HeatCircle

def field(P:CanonicalCovariance.ProfileParameters)(Λ θ:ℝ)(p:Parameter):ℝ:=
  ControlledScalarCovarianceTail.tail P Λ 0 (min p.1.1.2 p.1.2) p.1.2 θ p.1.1.1.1 p.1.1.1.2 p.2

attribute [local irreducible] ControlledProfile.profile

/-- Genuine own-profile covariance with variable terminal/current clocks
and original initial data. The profile itself is not changed with the terminal. -/
theorem field_measurable(P:CanonicalCovariance.ProfileParameters)(Λ θ:ℝ):Measurable (field P Λ θ):=by
  let Z:VariableObservations.Family Parameter 1:={
    observations:=fun p=>ScalarCovarianceTailScale.observation p.1.2 p.2
    stop_measurable:=fun _=>show Measurable (fun p:Parameter=>p.1.2) from measurable_fst.snd
    target_measurable:=fun _=>show Measurable (fun p:Parameter=>p.1.2) from measurable_fst.snd
    center_measurable:=fun _=>show Measurable (fun p:Parameter=>p.2) from measurable_snd}
  have hmap:Measurable (fun p:Parameter×Domain=>(p.1.1.1.1,p.2)):=
    measurable_fst.fst.fst.fst.prodMk measurable_snd
  have hc:Measurable (fun p:Parameter×Domain=>
      ControlledReferenceWindows.coefficient P Λ θ 0 p.1.1.1.1 p.2):=
    (ControlledReferenceWindows.coefficient_measurable P Λ θ 0).comp hmap
  have hm:=Z.covariance_measurable hc (measurable_fst.fst.snd.min measurable_fst.snd)
    measurable_fst.snd (fun p=>min_le_right p.1.1.2 p.1.2)
  have he:(field P Λ θ)=(fun p:Parameter=>WordRecursion.covariance
      (fun r=>ControlledReferenceWindows.coefficient P Λ θ 0 p.1.1.1 r)
      (Z.observations p) (min p.1.1.2 p.1.2) p.1.2 0 0):=by
    funext p
    unfold field ControlledScalarCovarianceTail.tail ControlledReferenceWindows.coefficient
    rfl
  rw [he]
  exact hm.eval_matrix (i:=0) (j:=0)

 theorem field_eq(P:CanonicalCovariance.ProfileParameters)(Λ θ:ℝ)(u d:CircleL2)(q b:ℝ)(hqb:q≤b)(x:HeatCircle):
    field P Λ θ ((((u,d),q),b),x)=ControlledScalarCovarianceTail.tail P Λ 0 q b θ u d x:=by
  simp only [field,min_eq_left hqb]
end SHE.InitialScalarCovarianceTail
