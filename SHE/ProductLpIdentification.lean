module

public import SHE.NullCompleteFiltration
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.ProductLpIdentification
open MeasureTheory Filter
open scoped ENNReal Topology
local instance productLpIdentification_pGeOne : Fact ((1:ENNReal) ≤ 2) := ⟨by norm_num⟩

variable {T Ω E : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (ν : Measure T) (μ : Measure Ω) [SFinite ν] [IsFiniteMeasure μ]

/-- A joint L² limit agrees almost everywhere with a jointly measurable
family of fixed-time limits in probability. This bridges the complete
predictable L² construction and continuous fixed-time modifications. -/
theorem ae_eq_of_slice_limits (v : ℕ → Lp E 2 (ν.prod μ)) (V : Lp E 2 (ν.prod μ))
    (hv : Tendsto v atTop (𝓝 V)) (W : T × Ω → E) (hW : StronglyMeasurable W)
    (hs : ∀ᵐ t ∂ν, TendstoInMeasure μ (fun n ω => v n (t,ω)) atTop (fun ω => W (t,ω))) :
    V =ᵐ[ν.prod μ] W := by
  obtain ⟨ns,hns,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hEq : MeasurableSet {p : T × Ω | V p=W p} :=
    (Lp.stronglyMeasurable V).measurableSet_eq_fun hW
  apply (Measure.ae_prod_iff_ae_ae hEq).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod hAE,hs] with t ht hslice
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω => v (ns n) (t,ω)) μ :=
    ((Lp.stronglyMeasurable (v (ns n))).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae hm ht)
    (hslice.comp hns.tendsto_atTop)

end SHE.ProductLpIdentification
