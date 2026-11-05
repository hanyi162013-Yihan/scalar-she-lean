module
public import SHE.NativeGammaAgeMeasure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeGammaAgeBound
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω:Type*} [MeasurableSpace Ω]
theorem product_le (μ:Measure Ω) [SFinite μ] (H v b:ℝ≥0) (hbH:b≤H)
    (F:(ℝ≥0×Ω)→ℝ≥0∞):
    (∫⁻p,(NativeGammaClock.window v b).indicator F p ∂energyMeasure μ H)≤
      ∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,F (((b:ℝ)-τ).toNNReal,ω) ∂μ :=by
  have ht:Measurable (fun p:ℝ≥0×Ω=>(p.1:ℝ)):=measurable_coe_nnreal_real.comp measurable_fst
  have hw:MeasurableSet (NativeGammaClock.window (Ω:=Ω) v b):=by
    exact (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)
  calc
    _≤(∫⁻q,∫⁻ω,(NativeGammaClock.window v b).indicator F (q,ω) ∂μ ∂timeMeasure H):=
      lintegral_prod_le _
    _=(∫⁻q,(Ioo v b).indicator (fun q=>∫⁻ω,F (q,ω) ∂μ) q ∂timeMeasure H):=by
      apply lintegral_congr
      intro q
      by_cases hq:q∈Ioo v b
      · simp only [indicator_of_mem hq]
        apply lintegral_congr
        intro ω
        exact indicator_of_mem (show (q,ω)∈NativeGammaClock.window v b from hq) F
      · rw [indicator_of_notMem hq]
        have he(ω:Ω): (NativeGammaClock.window v b).indicator F (q,ω)=0:=
          indicator_of_notMem (show (q,ω)∉NativeGammaClock.window v b from hq) F
        simp only [he,lintegral_zero]
    _=_:=NativeGammaAgeMeasure.scalar H v b hbH _
/-- The full original same-J six-slot RHS transports directly to its
physical future-age integral. Tonelli's upper inequality suffices, so
no unproved parameterwise version-measurability is introduced. -/
theorem bound (μ:Measure Ω) [SFinite μ] (H v b:ℝ≥0) (hbH:b≤H)
    {E:ℝ≥0∞} {f:(ℝ≥0×Ω)→ℝ}
    (hE:E≤∫⁻p,ENNReal.ofReal ((NativeGammaClock.window v b).indicator f p) ∂energyMeasure μ H):
    E≤∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (f (((b:ℝ)-τ).toNNReal,ω)) ∂μ:=by
  apply hE.trans
  have he:(fun p=>ENNReal.ofReal ((NativeGammaClock.window v b).indicator f p))=
      (NativeGammaClock.window v b).indicator (fun p=>ENNReal.ofReal (f p)):=by
    funext p
    by_cases hp:p∈NativeGammaClock.window v b <;> simp [hp]
  rw [he]
  exact product_le μ H v b hbH _
end SHE.NativeGammaAgeBound
