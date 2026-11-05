module

public import SHE.RootHistoryFubini

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Original old-history integration retains the spatial output as a
jointly measurable field. -/
theorem rootAverage_measurable (R:ReferenceData) (k:ℕ)
    (F:Ω×History HeatCircle k→ℝ) (hF:Measurable F):
    Measurable (rootAverage R k F):=by
  have hmRaw : Measurable (fun z : ((Ω×HeatCircle)×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      F (z.1.1.1,separated k (z.1.1.2,z.1.2,fun i=>z.2 i+z.1.1.2))) := by
    have hsites : Measurable (fun z : ((Ω×HeatCircle)×(Fin k→ℝ))×(Fin k→HeatCircle)=>
        fun i=>z.2 i+z.1.1.2):=Measurable.of_eval (fun i=>
      ((measurable_pi_apply i).comp measurable_snd).add measurable_fst.fst.snd)
    exact hF.comp (measurable_fst.fst.fst.prodMk ((separated_measurable k).comp
      (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk hsites))))
  exact hmRaw.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

/-- Squaring the actual retained output before any spatial contraction. -/
theorem retained_sum_energy (μ:Measure Ω) (f c p:Ω→ℝ)
    (hf:AEStronglyMeasurable f μ) (he:f=ᵐ[μ] fun z=>c z+p z)
    (hc:Integrable (fun z=>|c z|^2) μ) (hp:Integrable (fun z=>|p z|^2) μ):
    Integrable (fun z=>|f z|^2) μ ∧
      (∫z,|f z|^2 ∂μ)≤2*((∫z,|c z|^2 ∂μ)+(∫z,|p z|^2 ∂μ)):=by
  have hd:Integrable (fun z=>2*(|c z|^2+|p z|^2)) μ:=by
    convert! (hc.add hp).const_mul 2 using 1
  have hle:∀ᵐz∂μ,|f z|^2≤2*(|c z|^2+|p z|^2):=by
    filter_upwards [he] with z hz
    rw [hz]
    simp only [sq_abs]
    nlinarith [sq_nonneg (c z-p z)]
  have hi:Integrable (fun z=>|f z|^2) μ:=hd.mono' (hf.norm.pow 2)
    (hle.mono (fun z hz=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (|f z|))]
      exact hz))
  refine ⟨hi,(integral_mono_ae hi hd hle).trans_eq ?_⟩
  rw [integral_const_mul,integral_add hc hp]

end SHE.HistoryProductMeasure
