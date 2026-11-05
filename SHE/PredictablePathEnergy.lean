module
public import SHE.ProcessEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.PredictablePathEnergy
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (K:ℝ≥0×Ω→E)(hp:StronglyMeasurable[𝓕.predictable] K)(C:ℝ)

include hp in
/-- A deterministic bound on each actual path's square energy gives
joint integrability under ANY probability measure on the same space.
This is the input-construction step needed after changing measure. -/
theorem integrable (hpath:∀ω,Integrable (fun t=>‖K (t,ω)‖^2) (timeMeasure H))
    (hbound:∀ω,(∫t,‖K (t,ω)‖^2 ∂timeMeasure H)≤C):
    Integrable (fun p=>‖K p‖^2) (energyMeasure μ H):=by
  have hm:StronglyMeasurable (fun p=>‖K p‖^2):=(hp.mono (predictable_le_product 𝓕)).norm.pow 2
  have houter:Integrable (fun ω=>∫t,‖K (t,ω)‖^2 ∂timeMeasure H) μ:=by
    apply Integrable.of_bound hm.integral_prod_left.aestronglyMeasurable C
    exact ae_of_all _ (fun ω=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>sq_nonneg _))]
      exact hbound ω)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ hpath
  · simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using houter

include hp in
/-- The genuine predictable L2 representative keeps the actual kernel
and its deterministic cost bound under the supplied probability law. -/
theorem exists_input (hpath:∀ω,Integrable (fun t=>‖K (t,ω)‖^2) (timeMeasure H))
    (hbound:∀ω,(∫t,‖K (t,ω)‖^2 ∂timeMeasure H)≤C):
    ∃u:Process (E:=E) 𝓕 μ H,u=ᵐ[energyMeasure μ H] K ∧ ‖u‖^2≤C:=by
  have hi:=integrable 𝓕 μ H K hp C hpath hbound
  have hmem:MemLp K 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (hp.mono (predictable_le_product 𝓕)).aestronglyMeasurable).mpr hi
  have htrim:@MemLp _ _ 𝓕.predictable _ _ K 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
    change eLpNorm K 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))<⊤
    rw [eLpNorm_trim (predictable_le_product 𝓕) hp]
    exact hmem
  let u:Process (E:=E) 𝓕 μ H:=htrim.toLp K
  have hua:u=ᵐ[energyMeasure μ H] K:=ae_eq_of_ae_eq_trim htrim.coeFn_toLp
  refine ⟨u,hua,?_⟩
  rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product 𝓕) u,
    integral_congr_ae (hua.mono (fun p hp=>by rw [hp]))]
  change (∫p,‖K p‖^2 ∂(timeMeasure H).prod μ)≤C
  rw [integral_prod_symm _ hi]
  exact (integral_mono hi.integral_prod_right (integrable_const C) hbound).trans_eq (by simp)
end SHE.PredictablePathEnergy
