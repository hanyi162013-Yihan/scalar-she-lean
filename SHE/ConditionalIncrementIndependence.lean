module
public import SHE.BrownianConditionalIncrement
public import Mathlib.Probability.Kernel.Composition.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.ConditionalIncrementIndependence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory MeasureTheory
variable{Ω P R Y D:Type*}[MeasurableSpace Ω][MeasurableSpace P]
variable[MeasurableSpace R][StandardBorelSpace R][Nonempty R]
variable[MeasurableSpace Y][StandardBorelSpace Y][Nonempty Y]
variable[MeasurableSpace D][StandardBorelSpace D][Nonempty D]

private theorem kernel_prod_const (k:Kernel P Y)[IsFiniteKernel k]
    (m:Measure D)[IsFiniteMeasure m]:
    k ⊗ₖ Kernel.const (P×Y) m=k ×ₖ Kernel.const P m:=by
  ext p:1
  apply Measure.ext_prod
  intro a b ha hb
  rw[Kernel.compProd_apply_prod ha hb,Kernel.prod_apply_prod]
  simp[mul_comm]

/-- Original independence from the full past pair survives genuine
conditional disintegration. This is conditional increment independence
from the retained future STATE and DRIVER history, not merely a
conditional future-driver marginal law. -/
theorem under_conditional (μ:Measure Ω)[IsProbabilityMeasure μ]
    (Z:Ω→P)(V:Ω→R)(y:R→Y)(d:R→D)
    (hZ:Measurable Z)(hV:Measurable V)(hy:Measurable y)(hd:Measurable d)
    (hi:IndepFun (fun ω=>(Z ω,y (V ω))) (fun ω=>d (V ω)) μ):
    ∀ᵐp∂μ.map Z,IndepFun y d (condDistrib V Z μ p):=by
  let ky:Kernel P Y:=condDistrib (y∘V) Z μ
  let md:Measure D:=μ.map (d∘V)
  have hf:μ.map (fun ω=>(Z ω,(y (V ω),d (V ω))))=
      (μ.map Z) ⊗ₘ (ky ×ₖ Kernel.const P md):=by
    have hprod:μ.map (fun ω=>((Z ω,y (V ω)),d (V ω)))=
        (μ.map (fun ω=>(Z ω,y (V ω)))).prod md:=
      hi.map_prod_eq_prod_map_map (hZ.prodMk (hy.comp hV)).aemeasurable (hd.comp hV).aemeasurable
    calc
      _=(μ.map (fun ω=>((Z ω,y (V ω)),d (V ω)))).map MeasurableEquiv.prodAssoc:=by
        rw[Measure.map_map (MeasurableEquiv.prodAssoc.measurable)
          (show Measurable (fun ω=>((Z ω,y (V ω)),d (V ω))) from
            (hZ.prodMk (hy.comp hV)).prodMk (hd.comp hV))]
        rfl
      _=((μ.map (fun ω=>(Z ω,y (V ω)))).prod md).map MeasurableEquiv.prodAssoc:=by
        rw[hprod]
      _=((μ.map Z ⊗ₘ ky).prod md).map MeasurableEquiv.prodAssoc:=by
        rw[compProd_map_condDistrib hZ.aemeasurable (hy.comp hV).aemeasurable]
        rfl
      _=(μ.map Z) ⊗ₘ (ky ×ₖ Kernel.const P md):=by
        rw[←Measure.compProd_const,Measure.compProd_assoc',kernel_prod_const]
  have hpair:=condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hZ ((hy.prodMk hd).comp hV) hf
  have hpmap:=condDistrib_comp (μ:=μ) (X:=Z) (Y:=V) hZ.aemeasurable hV.aemeasurable (hy.prodMk hd)
  have hymap:=condDistrib_comp (μ:=μ) (X:=Z) (Y:=V) hZ.aemeasurable hV.aemeasurable hy
  have hid:IndepFun Z (d∘V) μ:=by
    simpa only[Function.comp_def,id_eq] using hi.comp measurable_fst measurable_id
  have hdconst:=BrownianConditionalIncrement.kernel_of_independent μ Z (d∘V)
    hZ.aemeasurable (hd.comp hV).aemeasurable hid
  have hdmap:=condDistrib_comp (μ:=μ) (X:=Z) (Y:=V) hZ.aemeasurable hV.aemeasurable hd
  filter_upwards[hpair,hpmap,hymap,hdconst,hdmap] with p hp hpm hym hdc hdm
  apply (indepFun_iff_map_prod_eq_prod_map_map hy.aemeasurable hd.aemeasurable).mpr
  change (condDistrib V Z μ p).map (fun r=>(y r,d r))= _
  rw[←Kernel.map_apply _ (hy.prodMk hd),←hpm,hp]
  rw[Kernel.prod_apply,Kernel.const_apply]
  rw[←Kernel.map_apply _ hy,←hym,←Kernel.map_apply _ hd,←hdm,hdc,Kernel.const_apply]
end SHE.ConditionalIncrementIndependence
