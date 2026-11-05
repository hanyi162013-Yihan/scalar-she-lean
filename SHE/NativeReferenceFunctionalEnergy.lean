module

public import SHE.NativeHeatFunctionalEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NativeReferenceFunctionalEnergy
open Set MeasureTheory AddCircle Real StoppedFourier NativeHeatObservation DyadicApproximation
open scoped ENNReal
local instance referenceFunctional_period : Fact (0<2*π):=⟨by positivity⟩
local instance referenceFunctional_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- A positive-age scalar observation has exactly the spatial energy
of the true native heat state, including honest scalar integrability. -/
theorem functional_energy {τ:ℝ} (hτ:0<τ) (X:RealL2):
    Integrable (fun x:HeatCircle=>(functional τ x X)^2) haarAddCircle ∧
      (∫x:HeatCircle,(functional τ x X)^2 ∂haarAddCircle)=‖heat τ X‖^2:=by
  let W:=heat τ X
  have hf:=NativeHeatFunctionalEnergy.functional_ae hτ X
  have hz:=PredictableScalarField.nativeField_ae_state (fun _:Unit=>(0:RealL2)) ()
  have hzero:∀ᵐx:HeatCircle ∂haarAddCircle,
      PredictableScalarField.nativeField (fun _:Unit=>(0:RealL2)) ((),x)=0:=by
    filter_upwards [hz,Lp.coeFn_zero ℂ 2 (haarAddCircle (T:=2*π))] with x hx h0
    simpa only [map_zero,h0,Pi.zero_apply,Complex.zero_re] using hx
  have hi:=NativeRepresentativeEnergy.section_integrable (fun _:Unit=>(0:RealL2)) (fun _:Unit=>W) ()
  have he:=NativeRepresentativeEnergy.section_energy (fun _:Unit=>(0:RealL2)) (fun _:Unit=>W) ()
  have heq:(fun x:HeatCircle=>(PredictableScalarField.nativeField (fun _:Unit=>W) ((),x)-
      PredictableScalarField.nativeField (fun _:Unit=>(0:RealL2)) ((),x))^2)=ᵐ[haarAddCircle]
      (fun x:HeatCircle=>(functional τ x X)^2):=by
    filter_upwards [hf,hzero] with x hx h0
    rw [h0,sub_zero,←hx]
  refine ⟨hi.congr heq,?_⟩
  rw [←integral_congr_ae heq]
  simpa only [sub_zero] using he

/-- The actual compatible-reference root combines the old damped heat
part with its SAME-driver partial frozen integral BEFORE squaring. Its
scalar spatial energy is the genuine Hilbert heat energy. -/
theorem reference_energy {s τ:ℝ} (hs:0≤s) (hτ:0<τ) (a:ℝ) (d N:RealL2):
    let f:=fun x:HeatCircle=>a*functional (s+τ) x d+functional τ x N
    Integrable (fun x=>f x^2) haarAddCircle ∧
      (∫x,f x^2 ∂haarAddCircle)=‖heat τ (a•heat s d+N)‖^2:=by
  intro f
  have he:f=fun x:HeatCircle=>functional τ x (a•heat s d+N):=by
    funext x
    rw [map_add,map_smul,functional_heat hτ hs,add_comm τ s]
    rfl
  rw [he]
  exact functional_energy hτ _

end SHE.NativeReferenceFunctionalEnergy
