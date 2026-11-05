module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.HasLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.WeakLimitProbabilityTools
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Ω X Y : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (P : ℕ → ProbabilityMeasure Ω) (Q : ProbabilityMeasure Ω)
  (hlim : Tendsto P atTop (𝓝 Q))

include hlim

/-- A continuous observation keeps a fixed law under weak convergence.
This applies to finite driver observations at different times. -/
theorem hasLaw (Xf : Ω → X) (hX : Continuous Xf) (ν : Measure X) [IsProbabilityMeasure ν]
    (hP : ∀ k, HasLaw Xf ν (P k : Measure Ω)) : HasLaw Xf ν (Q : Measure Ω) := by
  refine ⟨hX.measurable.aemeasurable, ?_⟩
  have hl := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q hlim hX
  have he (k : ℕ) : (P k).map Xf = ν.toProbabilityMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    exact (hP k).map_eq
  have hz : Tendsto (fun k ↦ (P k).map Xf) atTop (𝓝 ν.toProbabilityMeasure) := by
    simpa only [he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ν.toProbabilityMeasure) atTop (𝓝 _))
  have hh := congrArg (fun p : ProbabilityMeasure X ↦ (p : Measure X))
    (tendsto_nhds_unique hl hz)
  exact hh

/-- Independence from a continuous observation of the entire past is
closed under weak convergence of the JOINT laws. This retains the state
history when passing Brownian driver laws to a weak limit. -/
theorem indepFun (Xf : Ω → X) (Yf : Ω → Y) (hX : Continuous Xf) (hY : Continuous Yf)
    (hP : ∀ k, IndepFun Xf Yf (P k : Measure Ω)) :
    IndepFun Xf Yf (Q : Measure Ω) := by
  apply indepFun_of_bcf hX.measurable.aemeasurable hY.measurable.aemeasurable
  intro f g
  let fX := f.compContinuous ⟨Xf, hX⟩
  let gY := g.compContinuous ⟨Yf, hY⟩
  have hl := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (fX * gY)
  have hr := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim fX).mul
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gY)
  have he (k : ℕ) : (∫ sample, (fX * gY) sample ∂(P k : Measure Ω)) =
      (∫ sample, fX sample ∂(P k : Measure Ω)) * ∫ sample, gY sample ∂(P k : Measure Ω) :=
    ((hP k).comp f.continuous.measurable g.continuous.measurable).integral_fun_mul_eq_mul_integral
      (f.continuous.comp hX).aestronglyMeasurable (g.continuous.comp hY).aestronglyMeasurable
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun k ↦ (he k).symm))

end SHEStochastic.WeakLimitProbabilityTools
