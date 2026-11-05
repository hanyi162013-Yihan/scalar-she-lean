module

public import SHE.AEContinuousSections

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SHE.AEContinuousSections
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

/-- Continuous versions and fixed-time AE identifications imply a
genuine product-AE identification. No uncountable intersection is used. -/
theorem ae_eq_version {X T E : Type*} [MeasurableSpace X]
    [TopologicalSpace T] [MetrizableSpace T] [MeasurableSpace T]
    [SecondCountableTopology T] [OpensMeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure T) (μ : Measure X) [SFinite μ] (u : T→X→E) (f : T×X→E)
    (hcont : ∀x,Continuous (fun t=>u t x)) (hf : Measurable f)
    (hsection : ∀t,u t=ᵐ[μ] fun x=>f (t,x)) :
    Function.uncurry u=ᵐ[ν.prod μ] f := by
  have hu:=aemeasurable ν μ u hcont (fun t=>
    (hf.comp measurable_prodMk_left).aemeasurable.congr (hsection t).symm)
  have hs:=Measure.ae_ae_of_ae_prod hu.ae_eq_mk
  have he : hu.mk (Function.uncurry u)=ᵐ[ν.prod μ] f:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hu.measurable_mk hf)).2
    filter_upwards [hs] with t ht
    filter_upwards [ht,hsection t] with x hx hy
    exact hx.symm.trans hy
  exact hu.ae_eq_mk.trans he

/-- The same version argument on a measurable open time window, with
continuity only in that window. This is the original product measure
restricted in time, not a separately chosen fixed-time version. -/
theorem ae_eq_version_on {X T E : Type*} [MeasurableSpace X]
    [TopologicalSpace T] [MetrizableSpace T] [MeasurableSpace T]
    [SecondCountableTopology T] [OpensMeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure T) (μ : Measure X) [SFinite μ] (s : Set T) (hs : MeasurableSet s)
    (u : T→X→E) (f : T×X→E)
    (hcont : ∀x,Continuous (fun t:s=>u t x)) (hf : Measurable f)
    (hsection : ∀t∈s,u t=ᵐ[μ] fun x=>f (t,x)) :
    Function.uncurry u=ᵐ[(ν.restrict s).prod μ] f := by
  let νs:Measure s:=ν.comap ((↑):s→T)
  have he:=ae_eq_version νs μ (fun t:s=>u t) (fun z:s×X=>f (z.1,z.2)) hcont
    (hf.comp (measurable_subtype_coe.prodMap measurable_id))
    (fun t=>hsection t t.property)
  have hm : (ν.restrict s).prod μ=
      (νs.prod μ).map (Prod.map ((↑):s→T) id):=by
    rw [←Measure.map_prod_map νs μ measurable_subtype_coe measurable_id,
      Measure.map_id,map_comap_subtype_coe hs]
  rw [hm]
  exact ((MeasurableEmbedding.subtype_coe hs).prodMap MeasurableEmbedding.id).ae_map_iff.2 he

end SHE.AEContinuousSections
