module

public import SHE.NativeCurrentDifference
public import SHE.NativeRepresentativeEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeHeatFunctionalEnergy
open Set MeasureTheory AddCircle Real StoppedFourier NativeHeatObservation DyadicApproximation
open scoped ENNReal
local instance nativeHeatFunctionalEnergy_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeHeatFunctionalEnergy_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- The physical observation functional is an actual spatial
representative of the native heat-semigroup state. -/
theorem functional_ae {τ : ℝ} (hτ : 0<τ) (u : RealL2) :
    (fun x : HeatCircle=>functional τ x u)=ᵐ[haarAddCircle]
      (fun x=>PredictableScalarField.nativeField (fun _ : Unit=>heat τ u) ((),x)) := by
  filter_upwards [heat_kernel_inner_ae hτ (embed u),
    PredictableScalarField.nativeField_ae_state (fun _ : Unit=>heat τ u) ()] with x hx hr
  rw [hr,embed_heat hτ.le,←hx]
  rfl

/-- The actual corrected-current root direction has the TRUE spatial
L2 energy of its native Hilbert state. The old deterministic correction
is retained, including the original physical damping clock. -/
theorem current_energy {Λ s τ : ℝ} (hΛ : 0≤Λ) (hs : 0≤s) (hτ : 0<τ)
    (dCurrent dOld : RealL2) :
    let f:=fun x : HeatCircle=>functional τ x dCurrent-
      (exp (-Λ*s)*(1-exp (-Λ*τ)))*functional (s+τ) x dOld
    Integrable (fun x=>f x^2) haarAddCircle ∧
      (∫ x,f x^2 ∂haarAddCircle)=‖NativeCurrentDifference.currentDifference Λ s τ dCurrent dOld‖^2 ∧
      (∫ x,f x^2 ∂haarAddCircle)≤2*‖dCurrent‖^2+2*‖dOld‖^2 := by
  intro f
  let W:=NativeCurrentDifference.currentDifference Λ s τ dCurrent dOld
  have he : f=ᵐ[haarAddCircle] (fun x=>PredictableScalarField.nativeField (fun _ : Unit=>W) ((),x)) := by
    filter_upwards [functional_ae hτ dCurrent,functional_ae (by linarith : 0<s+τ) dOld,
      PredictableScalarField.nativeField_ae_state (fun _ : Unit=>heat τ dCurrent) (),
      PredictableScalarField.nativeField_ae_state (fun _ : Unit=>heat (s+τ) dOld) (),
      PredictableScalarField.nativeField_ae_state (fun _ : Unit=>W) (),
      Lp.coeFn_sub (embed (heat τ dCurrent))
        ((exp (-Λ*s)*(1-exp (-Λ*τ))) • embed (heat (s+τ) dOld)),
      Lp.coeFn_smul (exp (-Λ*s)*(1-exp (-Λ*τ))) (embed (heat (s+τ) dOld))] with x h0 h1 h0r h1r hWr hsub hsmul
    rw [hWr]
    change f x=(embed (heat τ dCurrent-(exp (-Λ*s)*(1-exp (-Λ*τ))) • heat (s+τ) dOld) x).re
    rw [map_sub,map_smul,hsub,Pi.sub_apply,hsmul,Pi.smul_apply,Complex.sub_re,Complex.smul_re]
    dsimp only [f]
    rw [h0,h1,h0r,h1r]
    rfl
  have hz:=PredictableScalarField.nativeField_ae_state (fun _ : Unit=>(0:RealL2)) ()
  have hzero : ∀ᵐ x∂haarAddCircle,PredictableScalarField.nativeField (fun _ : Unit=>(0:RealL2)) ((),x)=0 := by
    filter_upwards [hz,Lp.coeFn_zero ℂ 2 (haarAddCircle (T:=2*π))] with x hx hzero
    simpa only [map_zero,hzero,Pi.zero_apply,Complex.zero_re] using hx
  have hi:=NativeRepresentativeEnergy.section_integrable (fun _ : Unit=>(0:RealL2)) (fun _ : Unit=>W) ()
  have hv:=NativeRepresentativeEnergy.section_energy (fun _ : Unit=>(0:RealL2)) (fun _ : Unit=>W) ()
  have heq : (fun x=>(PredictableScalarField.nativeField (fun _ : Unit=>W) ((),x)-
      PredictableScalarField.nativeField (fun _ : Unit=>(0:RealL2)) ((),x))^2)=ᵐ[haarAddCircle] (fun x=>f x^2) := by
    filter_upwards [he,hzero] with x hx hz
    rw [hx,hz,sub_zero]
  have hE : (∫ x,f x^2 ∂haarAddCircle)=‖W‖^2 := by
    rw [←integral_congr_ae heq]
    simpa only [sub_zero] using hv
  refine ⟨hi.congr heq,hE,?_⟩
  rw [hE]
  have hn:=pow_le_pow_left₀ (norm_nonneg _) (NativeCurrentDifference.currentDifference_norm hΛ hs hτ.le dCurrent dOld) 2
  change ‖W‖^2≤_ at hn
  nlinarith [sq_nonneg (‖dCurrent‖-‖dOld‖)]

end SHE.NativeHeatFunctionalEnergy
