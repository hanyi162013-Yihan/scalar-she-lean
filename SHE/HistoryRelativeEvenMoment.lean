module

public import SHE.HistoryRelativeOldFirst
public import SHE.SectionFirstMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.HistoryProductMeasure
open Set MeasureTheory Real AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance historyRelativeEvenMoment_period : Fact (0<2*π):=⟨by positivity⟩
variable {Ω:Type} [MeasurableSpace Ω]

/-- ORIGINAL-history moments become genuine sample/output moments at
fixed relative old sites. All coordinates are changed simultaneously
before any AE section is selected. -/
theorem relative_even_moment (R:ReferenceData) (μ:Measure Ω) [SFinite μ] (k:ℕ)
    (F:History HeatCircle k×Ω→ℝ) (hF:Measurable F)
    (B:History HeatCircle k→ℝ) (C:ℝ) (order:ℕ)
    (hMom:∀ᵐ h ∂historyMeasure R haarAddCircle k,
      Integrable (fun ω=>|F (h,ω)|^(2*order)) μ ∧
      (∫ω,|F (h,ω)|^(2*order) ∂μ)≤C*(B h)^(2*order))
    (P:(Fin k→ℝ)→Prop) (D:(Fin k→ℝ)→(Fin k→HeatCircle)→ℝ)
    (hD:∀t,P t→∀w x,B (separated k (x,t,fun i=>w i+x))=D t w):
    ∀ᵐ t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)),
      P t→∀ᵐ w ∂Measure.pi (fun _:Fin k=>haarAddCircle),
      let G:=fun y:Ω×HeatCircle=>F (separated k (y.2,t,fun i=>w i+y.2),y.1)
      Integrable (fun y=>|G y|^(2*order)) (μ.prod haarAddCircle) ∧
      (∫y,|G y|^(2*order) ∂μ.prod haarAddCircle)≤C*(D t w)^(2*order):=by
  have hs:=ae_relative_old_first R k hMom
  filter_upwards [hs] with t ht
  intro hp
  filter_upwards [ht] with w hw
  intro G
  have hhist:Measurable (fun y:Ω×HeatCircle=>separated k (y.2,t,fun i=>w i+y.2)):=
    (separated_measurable k).comp (measurable_snd.prodMk
      ((measurable_const (a:=t)).prodMk (Measurable.of_eval
        (fun i=>(measurable_const (a:=w i)).add measurable_snd))))
  have hG:Measurable G:=hF.comp (hhist.prodMk measurable_fst)
  have hsec:∀ᵐ x:HeatCircle ∂haarAddCircle,
      Integrable (fun ω=>|G (ω,x)|^(2*order)) μ ∧
      (∫ω,|(|G (ω,x)|^(2*order))| ∂μ)≤C*(D t w)^(2*order):=by
    filter_upwards [hw] with x hx
    refine ⟨hx.1,?_⟩
    simpa only [G,hD t hp w x,abs_pow,abs_abs] using hx.2
  have hh:=SectionFirstMoment.joint_integrable μ haarAddCircle
    (fun y=>|G y|^(2*order)) ((continuous_abs.measurable.comp hG).pow_const _)
    (fun _:HeatCircle=>C*(D t w)^(2*order)) (integrable_const _) hsec
  simpa only [abs_pow,abs_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

end SHE.HistoryProductMeasure
