module

public import SHE.InitialCompleteTimePatch

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.InitialOutputExtension
open Classical Set MeasureTheory Real
variable {Y:Type*} [MeasurableSpace Y]

def field (h:ℝ) (I:ℝ×Y→ℝ) (z:ℝ×Y):ℝ:=if 0<z.1 ∧ z.1≤h then I z else 0

theorem measurable_field (h:ℝ) (I:ℝ×Y→ℝ) (hi:Measurable I):Measurable (field h I):=
  hi.ite ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)) measurable_const

theorem energy (μ:Measure Y) [SFinite μ] {h H:ℝ} (hhH:h≤H) (I:ℝ×Y→ℝ)
    (hi:Integrable (fun z=>|I z|^2) ((volume.restrict (Ioc 0 h)).prod μ)):
    Integrable (fun z=>|field h I z|^2) ((volume.restrict (Ioc 0 H)).prod μ) ∧
      (∫z,|field h I z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ)=
        ∫z,|I z|^2 ∂(volume.restrict (Ioc 0 h)).prod μ:=by
  let S:Set (ℝ×Y):=Ioc 0 h ×ˢ univ
  have hs:MeasurableSet S:=measurableSet_Ioc.prod MeasurableSet.univ
  have he:((volume.restrict (Ioc (0:ℝ) H)).prod μ).restrict S=
      (volume.restrict (Ioc (0:ℝ) h)).prod μ:=by
    rw [show S=Ioc 0 h ×ˢ univ from rfl,←Measure.prod_restrict,Measure.restrict_univ,
      Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    ext t
    simp only [mem_inter_iff,mem_Ioc]
    constructor
    · exact fun ht=>ht.1
    · exact fun ht=>⟨ht,ht.1,ht.2.trans hhH⟩
  have hf:(fun z:ℝ×Y=>|field h I z|^2)=S.indicator (fun z=>|I z|^2):=by
    funext z
    simp only [field,indicator_apply,S,mem_prod,mem_Ioc,mem_univ,and_true]
    split_ifs <;> simp_all only [abs_zero,zero_pow (by decide:(2:ℕ)≠0)]
  rw [hf]
  refine ⟨(integrable_indicator_iff hs).mpr ?_,?_⟩
  · simpa only [IntegrableOn,he] using hi
  · rw [integral_indicator hs,he]

end SHE.InitialOutputExtension
