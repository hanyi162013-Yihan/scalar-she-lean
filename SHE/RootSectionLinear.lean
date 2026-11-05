module
public import SHE.RootDensityHistory
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.RootSectionLinear
open MeasureTheory Set StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance rootSectionLinear_period:Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- Subtraction of retained-root averages follows from genuine original-history L1. -/
theorem sub_ae (R:ReferenceData)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (k:ℕ)(F G:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hF:Integrable (fun h=>F (ω,h)) (historyMeasure R ν k))
    (hG:Integrable (fun h=>G (ω,h)) (historyMeasure R ν k)):
    ∀ᵐx∂ν,RootSectionAverage.average R k (fun z=>F z-G z) (ω,x)=
      RootSectionAverage.average R k F (ω,x)-RootSectionAverage.average R k G (ω,x):=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>AddCircle.haarAddCircle (T:=2*Real.pi))
  have hp:=separated_measurePreserving R ν k
  have hiF:Integrable (fun z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>F (ω,separated k z))
      (ν.prod (T.prod W)):=(hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hiG:Integrable (fun z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>G (ω,separated k z))
      (ν.prod (T.prod W)):=(hp.integrable_comp hG.aestronglyMeasurable).mpr hG
  filter_upwards [hiF.prod_right_ae,hiG.prod_right_ae] with x hxF hxG
  change (∫t,∫w,F (ω,separated k (x,t,w))-G (ω,separated k (x,t,w)) ∂W ∂T)=_
  calc
    _=∫z:(Fin k→ℝ)×(Fin k→HeatCircle),
        F (ω,separated k (x,z))-G (ω,separated k (x,z)) ∂T.prod W:=
      (integral_prod _ (hxF.sub hxG)).symm
    _=(∫z,F (ω,separated k (x,z)) ∂T.prod W)-
        ∫z,G (ω,separated k (x,z)) ∂T.prod W:=integral_sub hxF hxG
    _=_:=by rw [integral_prod _ hxF,integral_prod _ hxG];rfl

/-- Bounded root testing preserves L1 before subtraction of the old-time/space averages. -/
theorem weighted_sub (R:ReferenceData)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (k:ℕ)(F G:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hF:Integrable (fun h=>F (ω,h)) (historyMeasure R ν k))
    (hG:Integrable (fun h=>G (ω,h)) (historyMeasure R ν k))
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ)(hb:∀x,‖g x‖≤B):
    (∫x,g x*RootSectionAverage.average R k F (ω,x) ∂ν)-
      (∫x,g x*RootSectionAverage.average R k G (ω,x) ∂ν)=
      ∫x,g x*RootSectionAverage.average R k (fun z=>F z-G z) (ω,x) ∂ν:=by
  have hiF:Integrable (fun x=>g x*RootSectionAverage.average R k F (ω,x)) ν:=
    (RootDensityHistory.average_integrable R ν k F ω hF).bdd_mul hg.aestronglyMeasurable
      (ae_of_all _ hb)
  have hiG:Integrable (fun x=>g x*RootSectionAverage.average R k G (ω,x)) ν:=
    (RootDensityHistory.average_integrable R ν k G ω hG).bdd_mul hg.aestronglyMeasurable
      (ae_of_all _ hb)
  rw [←integral_sub hiF hiG]
  apply integral_congr_ae
  filter_upwards [sub_ae R ν k F G ω hF hG] with x hx
  rw [hx,mul_sub]
end SHE.RootSectionLinear
