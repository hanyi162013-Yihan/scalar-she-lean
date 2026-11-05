module
public import SHE.RootSectionAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace SHE.RootDensityHistory
open MeasureTheory Set StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- Integrating original node variables preserves integrability of
the actual retained-root section under the same root measure. -/
theorem average_integrable (R:ReferenceData)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (k:ℕ)(F:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hi:Integrable (fun h=>F (ω,h)) (historyMeasure R ν k)):
    Integrable (fun x=>RootSectionAverage.average R k F (ω,x)) ν:=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>AddCircle.haarAddCircle (T:=2*Real.pi))
  have hp:=separated_measurePreserving R ν k
  have hh:Integrable (fun z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>F (ω,separated k z))
      (ν.prod (T.prod W)):=(hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  apply hh.integral_prod_left.congr
  filter_upwards [hh.prod_right_ae] with x hx
  exact integral_prod _ hx

variable (R:ReferenceData)(k:ℕ)(g:HeatCircle→ℝ)(hg:Measurable g)(hg0:∀x,0≤g x)
local notation "ν"=>(AddCircle.haarAddCircle:Measure HeatCircle).withDensity (fun x=>ENNReal.ofReal (g x))

include hg hg0 in
/-- The actual positive root density becomes its literal retained-root
test, with all original old-time and old-space measures unchanged. -/
theorem integral [IsFiniteMeasure ν](F:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hi:Integrable (fun h=>F (ω,h)) (historyMeasure R ν k)):
    (∫h,F (ω,h) ∂historyMeasure R ν k)=
      ∫x:HeatCircle,g x*RootSectionAverage.average R k F (ω,x) ∂AddCircle.haarAddCircle:=by
  rw [RootSectionAverage.integral_history R ν k F ω hi,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ENNReal.toReal_ofReal (hg0 x),smul_eq_mul]

include hg hg0 in
theorem integrable [IsFiniteMeasure ν](F:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hi:Integrable (fun h=>F (ω,h)) (historyMeasure R ν k)):
    Integrable (fun x:HeatCircle=>g x*RootSectionAverage.average R k F (ω,x)) AddCircle.haarAddCircle:=by
  have hh:=average_integrable R ν k F ω hi
  have hh':= (integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal
    (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))).mp hh
  simpa only [ENNReal.toReal_ofReal (hg0 _),smul_eq_mul] using hh'
end SHE.RootDensityHistory
