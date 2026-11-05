module

public import SHE.RootHistoryMeasure
public import SHE.SectionFirstMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type} [MeasurableSpace Ω]

/-- Absolute original-history mass from TRUE fixed-old-time spatial
L1 estimates. The output root, relative old sites and sample are moved
by exact preserving maps before any Fubini or exceptional section. -/
theorem original_absolute (R:ReferenceData) (μ:Measure Ω) [SFinite μ] (k:ℕ)
    (F:Ω×History HeatCircle k→ℝ) (hF:Measurable F)
    (B:(Fin k→ℝ)→ℝ)
    (hB:Integrable B (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))))
    (hs:∀ᵐt ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)),
      let G:=fun z:(Ω×HeatCircle)×(Fin k→HeatCircle)=>
        F (z.1.1,separated k (z.1.2,t,fun i=>z.2 i+z.1.2))
      Integrable G ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin k=>haarAddCircle))) ∧
        (∫z,|G z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin k=>haarAddCircle)))≤B t):
    Integrable F (μ.prod (historyMeasure R haarAddCircle k)) ∧
      (∫z,|F z| ∂μ.prod (historyMeasure R haarAddCircle k))≤
        ∫t,B t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)):=by
  let Y:=μ.prod (haarAddCircle:Measure HeatCircle)
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  let S:((Ω×HeatCircle)×(Fin k→HeatCircle))×(Fin k→ℝ)→ℝ:=fun z=>
    F (z.1.1.1,separated k (z.1.1.2,z.2,fun i=>z.1.2 i+z.1.1.2))
  have hhist:Measurable (fun z:((Ω×HeatCircle)×(Fin k→HeatCircle))×(Fin k→ℝ)=>
      separated k (z.1.1.2,z.2,fun i=>z.1.2 i+z.1.1.2)):=
    (separated_measurable k).comp (measurable_fst.fst.snd.prodMk (measurable_snd.prodMk
      (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_fst.snd).add measurable_fst.fst.snd))))
  have hS:Measurable S:=hF.comp (measurable_fst.fst.fst.prodMk hhist)
  have hj:=SectionFirstMoment.joint_integrable (Y.prod W) T S hS B hB hs
  have hp:MeasurePreserving
      (fun z:(Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))=>((z.1,z.2.2),z.2.1))
      (Y.prod (T.prod W)) ((Y.prod W).prod T):=by
    convert! (measurePreserving_prodAssoc Y W T).symm.comp
      ((MeasurePreserving.id Y).prod (Measure.measurePreserving_swap (μ:=T) (ν:=W))) using 1
  have hr:=rootSample_preserving R μ k
  have hRel:Integrable (fun z:(Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))=>
      F (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2))) (Y.prod (T.prod W)):=by
    convert! hp.integrable_comp_of_integrable hj.1 using 1
  have hOrig:Integrable F (μ.prod (historyMeasure R haarAddCircle k)):=
    (hr.integrable_comp hF.aestronglyMeasurable).mp hRel
  have he:(∫z,|F z| ∂μ.prod (historyMeasure R haarAddCircle k))=
      ∫z,|S z| ∂(Y.prod W).prod T:=by
    have heR:(∫z,|F (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2))|
        ∂Y.prod (T.prod W))=∫z,|F z| ∂μ.prod (historyMeasure R haarAddCircle k):=by
      rw [←hr.map_eq,integral_map hr.measurable.aemeasurable
        (by rw [hr.map_eq];exact (continuous_abs.measurable.comp hF).aestronglyMeasurable)]
    rw [←heR]
    rw [←hp.map_eq,integral_map hp.measurable.aemeasurable
      (by rw [hp.map_eq];exact (continuous_abs.measurable.comp hS).aestronglyMeasurable)]
  exact ⟨hOrig,he.trans_le hj.2⟩

end SHE.HistoryProductMeasure
