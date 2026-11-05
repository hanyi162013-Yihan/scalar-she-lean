module
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SHE.SpatialTimeAE
open MeasureTheory
variable {T Ω X E:Type*}[MeasurableSpace T][MeasurableSpace Ω][MeasurableSpace X]
variable [MetricSpace E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (ν:Measure T)(μ:Measure Ω)(ξ:Measure X)[SFinite ν][SFinite μ][SFinite ξ]

/-- Honest time/root/sample Fubini for a measurable equality event.
This converts an actual nested history event to root-indexed predictable
L²-class equality; it does not interchange uncountably many null sets. -/
theorem root_energy {f g:(T×Ω)×X→E}(hf:Measurable f)(hg:Measurable g)
    (h:∀ᵐt∂ν,∀ᵐx∂ξ,∀ᵐω∂μ,f ((t,ω),x)=g ((t,ω),x)):
    ∀ᵐx∂ξ,∀ᵐp∂ν.prod μ,f (p,x)=g (p,x):=by
  let Event:=fun z:(T×Ω)×X=>f z=g z
  have hm:MeasurableSet {z|Event z}:=measurableSet_eq_fun hf hg
  have ht:∀ᵐz∂ν.prod (μ.prod ξ),Event ((z.1,z.2.1),z.2.2):=by
    have hm3:MeasurableSet {z:T×(Ω×X)|Event ((z.1,z.2.1),z.2.2)}:=
      hm.preimage ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
    apply (Measure.ae_prod_iff_ae_ae hm3).mpr
    filter_upwards [h] with t ht
    have hmt:MeasurableSet {z:Ω×X|Event ((t,z.1),z.2)}:=
      hm.preimage ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    exact (Measure.ae_prod_iff_ae_ae hmt).mpr ((Measure.ae_ae_comm hmt).mpr ht)
  have hp:∀ᵐz∂(ν.prod μ).prod ξ,Event z:=
    (measurePreserving_prodAssoc ν μ ξ).quasiMeasurePreserving.ae ht
  exact (Measure.ae_ae_comm hm).mp (Measure.ae_ae_of_ae_prod hp)
end SHE.SpatialTimeAE
