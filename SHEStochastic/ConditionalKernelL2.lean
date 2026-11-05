module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalKernelL2
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E X V : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [MeasurableSpace X] [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]

/-- Conditional L2 moments with a quadratic bound can be mixed under
an L2 initial law. This is the moment step needed at continuation joins. -/
theorem memLp (ρ : Measure E) [SFinite ρ] (κ : Kernel E X) [IsSFiniteKernel κ]
    (f : E×X → V) (hf : Measurable f)
    (hρ : MemLp (id : E → E) 2 ρ)
    (hLocal : ∀ᵐ z ∂ρ,MemLp (fun x => f (z,x)) 2 (κ z))
    (A B : ℝ) (hBound : ∀ᵐ z ∂ρ,(∫ x,‖f (z,x)‖^2 ∂κ z)≤A*‖z‖^2+B)
    [IsFiniteMeasure ρ] : MemLp f 2 (ρ ⊗ₘ κ) := by
  have hm : StronglyMeasurable (fun z => ∫ x,‖f (z,x)‖^2 ∂κ z) :=
    (hf.norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right'
  have hDom : Integrable (fun z => A*‖z‖^2+B) ρ :=
    ((hρ.integrable_norm_pow (by norm_num : (2 : ℕ)≠0)).const_mul A).add (integrable_const B)
  have hMean : Integrable (fun z => ∫ x,‖f (z,x)‖^2 ∂κ z) ρ := by
    apply hDom.mono' hm.aestronglyMeasurable
    filter_upwards [hBound] with z hz
    rwa [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  apply (memLp_two_iff_integrable_sq_norm hf.stronglyMeasurable.aestronglyMeasurable).mpr
  apply (Measure.integrable_compProd_iff (hf.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable).mpr
  refine ⟨hLocal.mono (fun z hz => hz.integrable_norm_pow (by norm_num : (2 : ℕ)≠0)),?_⟩
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hMean

end SHEStochastic.ConditionalKernelL2
