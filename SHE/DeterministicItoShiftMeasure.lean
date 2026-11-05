module
public import SHE.PredictableTime
public import SHE.TimeMeasureRestriction
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal

theorem real_time_translation(v h:ℝ≥0):
    (volume.restrict (Ioc (0:ℝ) (h:ℝ))).map (fun t:ℝ=>(v:ℝ)+t)=
      volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ)):=by
  have hp:(fun t:ℝ=>(v:ℝ)+t) ⁻¹' Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ)=Ioc (0:ℝ) (h:ℝ):=by
    ext t
    simp only [mem_preimage,mem_Ioc,NNReal.coe_add]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
  have hm:=(measurePreserving_add_left volume (v:ℝ)).restrict_preimage
    (s:=Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ)) measurableSet_Ioc
  simpa only [hp] using hm.map_eq

/-- Exact deterministic translation of the original finite Lebesgue
clock, retaining the physical post-v window and its endpoints. -/
theorem time_translation(H v h:ℝ≥0)(hvh:v+h≤H):
    MeasurePreserving (fun t:ℝ≥0=>v+t) (timeMeasure h)
      ((timeMeasure H).restrict (Ioc v (v+h))):=by
  refine ⟨(continuous_const.add continuous_id).measurable,?_⟩
  apply nonnegative_coe_measurableEmbedding.map_injective
  have hmAdd:Measurable (fun t:ℝ≥0=>v+t):=(continuous_const.add continuous_id).measurable
  rw [Measure.map_map measurable_coe_nnreal_real hmAdd]
  have he:(((↑):ℝ≥0→ℝ)∘(fun t:ℝ≥0=>v+t))=
      (fun t:ℝ=>(v:ℝ)+t)∘((↑):ℝ≥0→ℝ):=rfl
  have hmReal:Measurable (fun t:ℝ=>(v:ℝ)+t):=measurable_const.add measurable_id
  rw [he,←Measure.map_map hmReal measurable_coe_nnreal_real,
    timeMeasure_map,real_time_translation]
  have hp:((↑):ℝ≥0→ℝ) ⁻¹' Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ)=Ioc v (v+h):=by
    ext t
    simp only [mem_preimage,mem_Ioc,NNReal.coe_lt_coe,NNReal.coe_le_coe]
  rw [←hp,←Measure.restrict_map measurable_coe_nnreal_real measurableSet_Ioc,timeMeasure_map,
    Measure.restrict_restrict measurableSet_Ioc]
  have hs:Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ)⊆Ioc (0:ℝ) (H:ℝ):=
    Ioc_subset_Ioc v.2 (by exact_mod_cast hvh)
  rw [inter_eq_left.mpr hs]

variable{Ω:Type*}[MeasurableSpace Ω]
/-- The exact local product clock lands on the SAME original physical
window. No conditional probability or new noise realization is used. -/
theorem product_translation(μ:Measure Ω)[SFinite μ](H v h:ℝ≥0)(hvh:v+h≤H):
    MeasurePreserving (fun p:ℝ≥0×Ω=>(v+p.1,p.2)) (energyMeasure μ h)
      ((energyMeasure μ H).restrict (Ioc v (v+h)×ˢuniv)):=by
  have hm:=(time_translation H v h hvh).prod (MeasurePreserving.id μ)
  have hf:Prod.map (fun t:ℝ≥0=>v+t) (id:Ω→Ω)=(fun p:ℝ≥0×Ω=>(v+p.1,p.2)):=by
    funext p
    rfl
  rw [hf] at hm
  change MeasurePreserving (fun p:ℝ≥0×Ω=>(v+p.1,p.2)) ((timeMeasure h).prod μ)
    (((timeMeasure H).prod μ).restrict (Ioc v (v+h)×ˢuniv))
  rw [←Measure.prod_restrict]
  simpa only [Measure.restrict_univ,Prod.map,id_eq] using hm

end SHE.DeterministicItoShift
