module
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace SHE.CommonLawLimit
open MeasureTheory Filter
open scoped Topology ENNReal
variable {Ω Ω' E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable (μ:Measure Ω)(ν:Measure Ω')[IsProbabilityMeasure μ][IsProbabilityMeasure ν]

section Metric
variable [MetricSpace E][MeasurableSpace E][BorelSpace E]

/-- Common laws of actual approximations pass to their probability
limits, even when the original probability spaces differ. -/
theorem map_eq (f:ℕ→Ω→E)(g:ℕ→Ω'→E)(F:Ω→E)(G:Ω'→E)
    (hf:∀n,AEMeasurable (f n) μ)(hg:∀n,AEMeasurable (g n) ν)
    (hF:TendstoInMeasure μ f atTop F)(hG:TendstoInMeasure ν g atTop G)
    (hlaw:∀n,μ.map (f n)=ν.map (g n)):
    μ.map F=ν.map G:=by
  have h2:=(hG.tendstoInDistribution hg).tendsto
  have he:(fun n=>(⟨μ.map (f n),inferInstance⟩:ProbabilityMeasure E))=
      (fun n=>(⟨ν.map (g n),inferInstance⟩:ProbabilityMeasure E)):=by
    funext n
    exact Subtype.ext (hlaw n)
  rw [←he] at h2
  exact tendstoInDistribution_unique f (hF.tendstoInDistribution hf)
    {forall_aemeasurable:=hf,
     aemeasurable_limit:=(hG.tendstoInDistribution hg).aemeasurable_limit,
     tendsto:=h2}
end Metric

section Normed
variable [NormedAddCommGroup E][MeasurableSpace E][BorelSpace E]

/-- Full L2 convergence suffices for the cross-space law transfer;
it introduces no solution-law or transition-kernel input. -/
theorem map_eq_of_L2
    (f:ℕ→Ω→E)(g:ℕ→Ω'→E)(F:Ω→E)(G:Ω'→E)
    (hf:∀n,AEMeasurable (f n) μ)(hg:∀n,AEMeasurable (g n) ν)
    (hF:Tendsto (fun n=>eLpNorm (f n-F) 2 μ) atTop (𝓝 0))
    (hG:Tendsto (fun n=>eLpNorm (g n-G) 2 ν) atTop (𝓝 0))
    (hlaw:∀n,μ.map (f n)=ν.map (g n)):
    μ.map F=ν.map G:=
  map_eq μ ν f g F G hf hg
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num:(2:ENNReal)≠0) hF)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num:(2:ENNReal)≠0) hG) hlaw
end Normed
end SHE.CommonLawLimit
