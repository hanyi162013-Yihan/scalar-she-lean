module

public import SHE.GaussianKernelShiftedLeaf
public import SHE.PositiveKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.UniformFiberMoments
open MeasureTheory ProbabilityTheory Real

/-- Genuine product Fubini turns uniform nonnegative fiber moments
into a joint moment, retaining arbitrary dependence of the integrand on
the outer parameter. -/
theorem nonnegative_bound {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν]
    (f : Ω×Y→ℝ) (hf : Measurable f) (hn : ∀ z,0≤f z) (C : ℝ)
    (hi : ∀ ω,Integrable (fun y => f (ω,y)) ν) (hb : ∀ ω,(∫ y,f (ω,y) ∂ν)≤C) :
    Integrable f (μ.prod ν) ∧ (∫ z,f z ∂μ.prod ν)≤C := by
  have hh := GaussianKernelShiftedLeaf.nonnegative_kernel_bound μ (Kernel.const Ω ν) f hf hn
    (fun _ => C) (integrable_const C) hi hb
  simpa only [Measure.compProd_const,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem even_moment {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν]
    (f : Ω×Y→ℝ) (hf : Measurable f) (b : ℕ) (C : ℝ)
    (hi : ∀ ω,Integrable (fun y => |f (ω,y)|^(2*b)) ν)
    (hb : ∀ ω,(∫ y,|f (ω,y)|^(2*b) ∂ν)≤C) :
    Integrable (fun z => |f z|^(2*b)) (μ.prod ν) ∧
      (∫ z,|f z|^(2*b) ∂μ.prod ν)≤C :=
  nonnegative_bound μ ν _ ((continuous_abs.measurable.comp hf).pow_const _)
    (fun z => pow_nonneg (abs_nonneg (f z)) _) C hi hb

/-- Every fixed even moment of a genuinely dependent Gaussian average
is bounded by its full joint moment. Joint integrability of the average
is concluded, not assumed as a normalized-kernel hypothesis. -/
theorem average_even_moment {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : Ω×Y→ℝ) (hf : Integrable f (μ.prod ν)) (b : ℕ)
    (hb : Integrable (fun z => |f z|^(2*b)) (μ.prod ν)) :
    Integrable (fun ω => |∫ y,f (ω,y) ∂ν|^(2*b)) μ ∧
      (∫ ω,|∫ y,f (ω,y) ∂ν|^(2*b) ∂μ)≤∫ z,|f z|^(2*b) ∂μ.prod ν := by
  have hp : Integrable (fun z => f z^(2*b)) (μ.prod ν) := by simpa only [pow_abs_two_mul] using hb
  have havg : Integrable (fun ω => (∫ y,f (ω,y) ∂ν)^(2*b)) μ := by
    apply hp.integral_prod_left.mono' (hf.integral_prod_left.aestronglyMeasurable.pow (2*b))
    filter_upwards [hf.prod_right_ae,hp.prod_right_ae] with ω hω hωb
    rw [Real.norm_eq_abs,abs_of_nonneg ((even_two_mul b).pow_nonneg _)]
    exact even_moment_average_le ν b hω hωb
  refine ⟨by simpa only [pow_abs_two_mul] using havg,?_⟩
  have he := integral_prod _ hp
  have hh : (∫ ω,(∫ y,f (ω,y) ∂ν)^(2*b) ∂μ)≤∫ z,f z^(2*b) ∂μ.prod ν := by
    rw [he]
    apply integral_mono_ae havg hp.integral_prod_left
    filter_upwards [hf.prod_right_ae,hp.prod_right_ae] with ω hω hωb
    exact even_moment_average_le ν b hω hωb
  simpa only [pow_abs_two_mul] using hh

end SHE.UniformFiberMoments
