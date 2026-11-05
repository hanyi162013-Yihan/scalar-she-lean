module
public import SHE.RootSectionAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.RootSectionAverage
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance rootSectionParameterSwap_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω Θ:Type*}[MeasurableSpace Ω][MeasurableSpace Θ]

/-- Genuine parameter/history Fubini with the original untranslated
old locations and root retained. Absolute joint integrability is required
before any signed averaging. -/
theorem parameter_integral_ae (R:ReferenceData)(k:ℕ)
    (τ:Measure Θ)[SFinite τ](μ:Measure Ω)[SFinite μ]
    (F:Θ×(Ω×History HeatCircle k)→ℝ)(hF:Measurable F)
    (hi:Integrable F (τ.prod (μ.prod (historyMeasure R haarAddCircle k)))):
    ∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,
      Integrable (fun θ=>average R k (fun a=>F (θ,a)) z) τ ∧
      (∫θ,average R k (fun a=>F (θ,a)) z∂τ)=average R k (fun a=>∫θ,F (θ,a)∂τ) z:=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  let Y:=μ.prod (haarAddCircle:Measure HeatCircle)
  let B:=T.prod W
  have hroot:MeasurePreserving
      (fun z:(Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))=>
        (z.1.1,separated k (z.1.2,z.2.1,z.2.2)))
      (Y.prod B) (μ.prod (historyMeasure R haarAddCircle k)):=by
    exact ((MeasurePreserving.id μ).prod (separated_measurePreserving R haarAddCircle k)).comp
      (measurePreserving_prodAssoc μ haarAddCircle B)
  have hp:MeasurePreserving
      (fun z:(Ω×HeatCircle)×(Θ×((Fin k→ℝ)×(Fin k→HeatCircle)))=>
        (z.2.1,(z.1.1,separated k (z.1.2,z.2.2.1,z.2.2.2))))
      (Y.prod (τ.prod B)) (τ.prod (μ.prod (historyMeasure R haarAddCircle k))):=by
    exact ((MeasurePreserving.id τ).prod hroot).comp
      ((measurePreserving_prodAssoc τ Y B).comp
        (((Measure.measurePreserving_swap (μ:=Y) (ν:=τ)).prod (MeasurePreserving.id B)).comp
          (measurePreserving_prodAssoc Y τ B).symm))
  let G:(Ω×HeatCircle)×(Θ×((Fin k→ℝ)×(Fin k→HeatCircle)))→ℝ:=fun z=>
    F (z.2.1,(z.1.1,separated k (z.1.2,z.2.2.1,z.2.2.2)))
  have hG:Integrable G (Y.prod (τ.prod B)):=(hp.integrable_comp hF.aestronglyMeasurable).mpr hi
  filter_upwards [hG.prod_right_ae] with z hz
  have hleft:(fun θ=>average R k (fun a=>F (θ,a)) z)=ᵐ[τ]
      fun θ=>∫a,G (z,(θ,a))∂B:=by
    filter_upwards [hz.prod_right_ae] with θ hθ
    exact (integral_prod _ hθ).symm
  refine ⟨hz.integral_prod_left.congr (hleft.mono (fun _ h=>h.symm)),?_⟩
  rw [integral_congr_ae hleft]
  calc
    _=∫a,∫θ,G (z,(θ,a))∂τ∂B:=integral_integral_swap hz
    _=average R k (fun a=>∫θ,F (θ,a)∂τ) z:=integral_prod _ hz.swap.integral_prod_left

end SHE.RootSectionAverage
