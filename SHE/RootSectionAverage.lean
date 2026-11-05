module
public import SHE.RootHistoryFields
public import SHE.UncutHistoryMass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.RootSectionAverage
open MeasureTheory Set AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

def average (R:ReferenceData)(k:ℕ)(F:Ω×History HeatCircle k→ℝ)(z:Ω×HeatCircle):ℝ:=
  ∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,F (z.1,separated k (z.2,t,w))
    ∂Measure.pi (fun _=>haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))

theorem measurable (R:ReferenceData)(k:ℕ)(F:Ω×History HeatCircle k→ℝ)(hF:Measurable F):
    Measurable (average R k F):=by
  have hm:Measurable (fun z:((Ω×HeatCircle)×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      F (z.1.1.1,separated k (z.1.1.2,z.1.2,z.2))):=
    hF.comp (measurable_fst.fst.fst.prodMk ((separated_measurable k).comp
      (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd))))
  exact hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

/-- Retaining a root is exactly original-history integration with its
root measure a Dirac measure; every original node measure is unchanged. -/
theorem integral_dirac_history (R:ReferenceData)(k:ℕ)(x:HeatCircle)
    (F:History HeatCircle k→ℝ)(hF:Integrable F (historyMeasure R (Measure.dirac x) k)):
    (∫p,F p ∂historyMeasure R (Measure.dirac x) k)=
      ∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,F (separated k (x,t,w))
        ∂Measure.pi (fun _=>haarAddCircle)
        ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)):=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  have hp:=separated_measurePreserving R (Measure.dirac x) k
  have hi:Integrable (fun z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>F (separated k z))
      ((Measure.dirac x).prod (T.prod W)):=
    (hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hx:Integrable (fun z:(Fin k→ℝ)×(Fin k→HeatCircle)=>F (separated k (x,z))) (T.prod W):=by
    simpa only [ae_dirac_eq,Filter.eventually_pure] using hi.prod_right_ae
  calc
    _=∫z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle)),F (separated k z) ∂(Measure.dirac x).prod (T.prod W):=by
      rw [←hp.map_eq]
      exact integral_map hp.measurable.aemeasurable (by simpa only [hp.map_eq] using hF.aestronglyMeasurable)
    _=∫z:(Fin k→ℝ)×(Fin k→HeatCircle),F (separated k (x,z)) ∂T.prod W:=by
      rw [integral_prod _ hi,integral_dirac]
    _=_:=integral_prod _ hx

/-- Integrating a retained root is exactly the original history integral,
for the original node measures and any finite root measure. -/
theorem integral_history (R:ReferenceData)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (k:ℕ)(F:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hF:Integrable (fun p=>F (ω,p)) (historyMeasure R ν k)):
    (∫p,F (ω,p) ∂historyMeasure R ν k)=∫x:HeatCircle,average R k F (ω,x) ∂ν:=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  have hp:=separated_measurePreserving R ν k
  have hi:Integrable (fun z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>F (ω,separated k z))
      (ν.prod (T.prod W)):=
    (hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  calc
    _=∫z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle)),F (ω,separated k z) ∂ν.prod (T.prod W):=by
      rw [←hp.map_eq]
      exact integral_map hp.measurable.aemeasurable (by simpa only [hp.map_eq] using hF.aestronglyMeasurable)
    _=∫x:HeatCircle,∫z:(Fin k→ℝ)×(Fin k→HeatCircle),F (ω,separated k (x,z)) ∂T.prod W ∂ν:=
      integral_prod _ hi
    _=_:=by
      apply integral_congr_ae
      filter_upwards [hi.prod_right_ae] with x hx
      exact integral_prod _ hx

variable {R:ReferenceData}{n:ℕ}(L:Level R HeatCircle n)

theorem massBound_dirac (x:HeatCircle)(k:ℕ):
    UncutHistoryMass.massBound (R:=R) (n:=n) (Measure.dirac x) k=
      UncutHistoryMass.massBound (R:=R) (n:=n) (haarAddCircle:Measure HeatCircle) k:=by
  induction k with
  | zero=>simp [UncutHistoryMass.massBound,Measure.real]
  | succ k ih=>simp only [UncutHistoryMass.massBound,ih]

/-- Uniform finite-depth root-retained mass from the true integrated
newest heat row, not a pointwise inverse-gap square. -/
theorem norm_le (k:ℕ)(F:Ω×History HeatCircle k→ℝ)(hF:Measurable F)
    (C:ℝ)(hC:0≤C)(hb:∀ω p,‖F (ω,p)‖≤C*UncutSmoothWords.weight L k p)
    (ω:Ω)(x:HeatCircle):
    ‖average R k F (ω,x)‖≤C*UncutHistoryMass.massBound (R:=R) (n:=n) (haarAddCircle:Measure HeatCircle) k:=by
  have hW:=UncutHistoryMass.weight_integrable L (Measure.dirac x) k
  have hi:Integrable (fun p=>F (ω,p)) (historyMeasure R (Measure.dirac x) k):=
    (hW.const_mul C).mono' (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ (hb ω))
  rw [average,←integral_dirac_history R k x _ hi]
  have hn:=norm_integral_le_of_norm_le (hW.const_mul C) (ae_of_all _ (hb ω))
  rw [integral_const_mul] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left (UncutHistoryMass.integral_weight_le L (Measure.dirac x) k) hC).trans_eq
    (congrArg (fun a=>C*a) (massBound_dirac (n:=n) x k)))
end SHE.RootSectionAverage
