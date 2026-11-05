module
public import Mathlib.Probability.Independence.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.FiniteCylinderIndependence
open MeasureTheory ProbabilityTheory Set
variable{Ω P κ E:Type*}[MeasurableSpace Ω][MeasurableSpace P][MeasurableSpace E]
variable(μ:Measure Ω)[IsProbabilityMeasure μ]

/-- Finite-dimensional independence determines independence of the
whole cylindrical sigma algebra, without an uncountable AE diagonal. -/
theorem full (Z:Ω→P)(V:κ→Ω→E)(hZ:Measurable Z)(hV:∀k,Measurable (V k))
    (hi:∀s:Finset κ,IndepFun Z (fun ω=>fun k:s=>V k.val ω) μ):
    IndepFun Z (fun ω=>fun k=>V k ω) μ:=by
  classical
  let m:Finset κ→MeasurableSpace Ω:=fun s=>⨆k∈s,MeasurableSpace.comap (V k) ‹MeasurableSpace E›
  have hm(s:Finset κ):m s≤‹MeasurableSpace Ω›:=
    iSup_le (fun k=>iSup_le (fun _=>(hV k).comap_le))
  have hmono:Monotone m:=by
    intro s t hst
    exact iSup_le (fun k=>iSup_le (fun hk=>le_iSup_of_le k (le_iSup_of_le (hst hk) le_rfl)))
  have hi'(s:Finset κ):Indep (m s) (MeasurableSpace.comap Z ‹MeasurableSpace P›) μ:=by
    have hs:MeasurableSpace.comap (fun ω=>fun k:s=>V k.val ω)
        (inferInstance:MeasurableSpace (s→E))=m s:=by
      rw [MeasurableSpace.pi,MeasurableSpace.comap_iSup]
      simp only [MeasurableSpace.comap_comp,Function.comp_def,m]
      exact (iSup_subtype (p:=fun k:κ=>k∈s)
        (f:=fun k:s=>MeasurableSpace.comap (V k.val) ‹MeasurableSpace E›))
    rw [←hs]
    exact (hi s).symm
  have hI:=indep_iSup_of_monotone hi' hm hZ.comap_le hmono
  have hv:@Measurable Ω (κ→E) (⨆s:Finset κ,m s) _ (fun ω=>fun k=>V k ω):=by
    letI:MeasurableSpace Ω:=⨆s:Finset κ,m s
    apply measurable_pi_iff.mpr
    intro k
    apply Measurable.of_comap_le
    exact le_iSup_of_le {k} (le_iSup_of_le k (le_iSup_of_le (by simp) le_rfl))
  exact (indep_of_indep_of_le_left hI hv.comap_le).symm
end SHE.FiniteCylinderIndependence
