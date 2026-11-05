module

public import SHE.HistoryRelativeSections
public import SHE.SectionFirstMoment

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact original history disintegration retaining the SAME sample in
all random past and current factors, with old times outermost. -/
theorem relativeSample_preserving (R : ReferenceData) (μ : Measure Ω) [SFinite μ] (k : ℕ) :
    MeasurePreserving
      (fun z : (Fin k→ℝ)×((Ω×HeatCircle)×(Fin k→HeatCircle))=>
        (z.2.1.1,separated k (z.2.1.2,z.1,fun i=>z.2.2 i+z.2.1.2)))
      ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
        ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))))
      (μ.prod (historyMeasure R haarAddCircle k)) := by
  let τ:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let νx : Measure HeatCircle:=haarAddCircle
  let νw:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  have h₁:=(MeasurePreserving.id τ).prod (measurePreserving_prodAssoc μ νx νw)
  have h₂:=(measurePreserving_prodAssoc τ μ (νx.prod νw)).symm
  have h₃:=(Measure.measurePreserving_swap (μ:=τ) (ν:=μ)).prod (MeasurePreserving.id (νx.prod νw))
  have h₄:=measurePreserving_prodAssoc μ τ (νx.prod νw)
  have h₅:=(MeasurePreserving.id μ).prod (relativeSeparated_preserving R k)
  convert! h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))) using 1

/-- Honest absolute original-history mass follows from original
old-time sections before any spatial cancellation. -/
theorem relativeSample_integrable_bound (R : ReferenceData) (μ : Measure Ω) [SFinite μ] (k : ℕ)
    (F : Ω×History HeatCircle k→ℝ) (hF : Measurable F)
    (B : (Fin k→ℝ)→ℝ)
    (hB : Integrable B (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))))
    (hs : ∀ᵐ t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)),
      Integrable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>
        F (z.1.1,separated k (z.1.2,t,fun i=>z.2 i+z.1.2)))
        ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) ∧
      (∫ z : (Ω×HeatCircle)×(Fin k→HeatCircle),
        |F (z.1.1,separated k (z.1.2,t,fun i=>z.2 i+z.1.2))|
          ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤B t) :
    Integrable F (μ.prod (historyMeasure R haarAddCircle k)) ∧
      (∫ z,|F z| ∂μ.prod (historyMeasure R haarAddCircle k))≤
        ∫ t,B t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)) := by
  let τ:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let η : Measure ((Ω×HeatCircle)×(Fin k→HeatCircle)):=(μ.prod (haarAddCircle (T:=2*Real.pi))).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))
  let G : (Fin k→ℝ)×((Ω×HeatCircle)×(Fin k→HeatCircle))→ℝ:=fun z=>
    F (z.2.1.1,separated k (z.2.1.2,z.1,fun i=>z.2.2 i+z.2.1.2))
  have hmap:=relativeSample_preserving R μ k
  have hG : Measurable G:=hF.comp hmap.measurable
  have hh:=SectionFirstMoment.joint_integrable η τ (fun z=>G (z.2,z.1))
    (hG.comp measurable_swap) B hB hs
  have hGi : Integrable G (τ.prod η):=by
    simpa only [Function.comp_def,Prod.swap] using hh.1.swap
  refine ⟨(hmap.integrable_comp hF.aestronglyMeasurable).mp hGi,?_⟩
  have he : (∫ z,|F z| ∂μ.prod (historyMeasure R haarAddCircle k))=∫ z,|G z| ∂τ.prod η:=by
    rw [←hmap.map_eq,integral_map hmap.measurable.aemeasurable
      (by rw [hmap.map_eq];exact (continuous_abs.measurable.comp hF).aestronglyMeasurable)]
  calc
    _=∫ z,|G z| ∂τ.prod η:=he
    _=∫ z,|G (z.2,z.1)| ∂η.prod τ:=by
      simpa only [Function.comp_def,Prod.swap] using (integral_prod_swap (μ:=τ) (ν:=η) (fun z=>|G z|)).symm
    _≤_:=hh.2

end SHE.HistoryProductMeasure
