module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.FiniteKernelMixture
open Set MeasureTheory
open scoped NNReal ENNReal
variable {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]

def measure (ν:Measure X)(η:Measure Y)(W:X→ℝ≥0∞)(K:X×Y→ℝ≥0∞):Measure (X×Y):=
  (ν.prod η).withDensity (fun p=>W p.1*K p)

/-- Full history/kernel mixture mass from the true old collision mass
and uniform new-time L1 bound. No selected partition or pointwise
stochastic energy is part of the measure. -/
theorem mass (ν:Measure X)[SFinite ν](η:Measure Y)[SFinite η]
    (W:X→ℝ≥0∞)(K:X×Y→ℝ≥0∞)(hW:Measurable W)(hK:Measurable K)
    {A B:ℝ≥0∞}(hA:(∫⁻x,W x ∂ν)≤A)(hB:∀x,(∫⁻y,K (x,y) ∂η)≤B):
    measure ν η W K univ≤A*B:=by
  rw [measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [lintegral_prod (fun p:X×Y=>W p.1*K p) (by exact ((hW.comp measurable_fst).mul hK).aemeasurable)]
  calc
    _=∫⁻x,W x*(∫⁻y,K (x,y) ∂η) ∂ν:=by
      apply lintegral_congr_ae
      filter_upwards with x
      exact lintegral_const_mul _ (hK.comp (measurable_const.prodMk measurable_id))
    _≤∫⁻x,W x*B ∂ν:=lintegral_mono (fun x=>mul_le_mul' le_rfl (hB x))
    _=(∫⁻x,W x ∂ν)*B:=lintegral_mul_const _ hW
    _≤A*B:=mul_le_mul' hA le_rfl

theorem finite (ν:Measure X)[SFinite ν](η:Measure Y)[SFinite η]
    (W:X→ℝ≥0∞)(K:X×Y→ℝ≥0∞)(hW:Measurable W)(hK:Measurable K)
    {A B:ℝ≥0∞}(hA:(∫⁻x,W x ∂ν)≤A)(hB:∀x,(∫⁻y,K (x,y) ∂η)≤B)
    (hAf:A≠∞)(hBf:B≠∞):IsFiniteMeasure (measure ν η W K):=
  ⟨(mass ν η W K hW hK hA hB).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hAf hBf))⟩

end SHE.FiniteKernelMixture
