module

public import SHE.NativeHeatConvolution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.RealCausalHeatKernel
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeHeatSpan AddCircle

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The physical heat kernel as a real continuous spatial function,
extended by zero at nonpositive ages for causal stochastic inputs. -/
def value (a : HeatCircle) (r : ℝ) : C(HeatCircle, ℝ) :=
  if hr : 0 < r then ⟨fun x ↦ (kernel r hr a x).re,
    Complex.continuous_re.comp (kernel r hr a).continuous⟩ else 0

theorem complex_eq {r : ℝ} (hr : 0 < r) (a x : HeatCircle) :
    kernel r hr a x = (value a r x : ℂ) := by
  apply Complex.ext
  · simp only [value, dif_pos hr, ContinuousMap.coe_mk, Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using (kernel_real_nonneg hr a x).1

theorem square {r : ℝ} (hr : 0 < r) (a x : HeatCircle) :
    (value a r x) ^ 2 = ‖kernel r hr a x‖ ^ 2 := by
  rw [complex_eq hr a x, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem eq_norm {r : ℝ} (hr : 0 < r) (a x : HeatCircle) :
    value a r x = ‖kernel r hr a x‖ := by
  rw [kernel_norm_eq_re]
  simp only [value, dif_pos hr, ContinuousMap.coe_mk]

theorem symm {r : ℝ} (hr : 0 < r) (a x : HeatCircle) : value a r x = value x r a := by
  rw [eq_norm hr, eq_norm hr, kernel_symm hr]

theorem integral_one {r : ℝ} (hr : 0 < r) (a : HeatCircle) :
    (∫ x : HeatCircle, value a r x ∂haarAddCircle) = 1 := by
  simpa only [eq_norm hr] using kernel_norm_mass hr a

theorem continuous_center {r : ℝ} (hr : 0 < r) : Continuous (fun a : HeatCircle ↦ value a r) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc := Complex.continuous_re.comp (continuous_heatPhysical_space hr)
  convert hc using 1
  funext p
  simp only [value, dif_pos hr, ContinuousMap.coe_mk, kernel_eq_physical]
  rfl

theorem convolution {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x y : HeatCircle) :
    (∫ a : HeatCircle, value x r a * value a s y ∂haarAddCircle) = value x (r + s) y := by
  simpa only [eq_norm hr, eq_norm hs, eq_norm (add_pos hr hs)] using kernel_norm_convolution hr hs x y

/-- Exact convolution in the continuous spatial function space, so
bounded linear maps of the kernel commute with this average directly. -/
theorem integral_kernel {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x : HeatCircle) :
    (∫ a : HeatCircle, value x r a • value a s ∂haarAddCircle) = value x (r + s) := by
  have hc : Continuous (fun a : HeatCircle ↦ value x r a • value a s) :=
    (value x r).continuous.smul (continuous_center hs)
  have hi : Integrable (fun a : HeatCircle ↦ value x r a • value a s) haarAddCircle :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext y
  rw [ContinuousMap.integral_apply hi]
  exact convolution hr hs x y

theorem difference_square {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (a b x : HeatCircle) :
    (value a r x - value b s x) ^ 2 = ‖kernel r hr a x - kernel s hs b x‖ ^ 2 := by
  rw [complex_eq hr a x, complex_eq hs b x, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem nonpos {r : ℝ} (hr : r ≤ 0) (a : HeatCircle) : value a r = 0 := by
  simp only [value, dif_neg (not_lt_of_ge hr)]

/-- Measurability in age and space reuses the existing Fourier-kernel
theorem and the checked pointwise identification with the positive kernel. -/
theorem joint_measurable (a : HeatCircle) :
    Measurable (fun p : ℝ × HeatCircle ↦ value a p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × HeatCircle ↦
      if 0 < p.1 then (ProfileVariance.heatPhysical p.1 a p.2).re else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (Complex.measurable_re.comp (ProfileVariance.heatPhysical_measurable a)) measurable_const
  convert hm using 1
  funext p
  by_cases hr : 0 < p.1
  · simp only [value, dif_pos hr, ContinuousMap.coe_mk, if_pos hr, kernel_eq_physical]
  · simp only [value, dif_neg hr, ContinuousMap.zero_apply, if_neg hr]

theorem measurable_family {P : Type*} [MeasurableSpace P] (a : HeatCircle)
    (r : P → ℝ) (hr : Measurable r) : Measurable (fun p : P × HeatCircle ↦ value a (r p.1) p.2) :=
  (joint_measurable a).comp ((hr.comp measurable_fst).prodMk measurable_snd)

theorem joint_center_measurable :
    Measurable (fun z : (ℝ × HeatCircle) × HeatCircle ↦ value z.1.2 z.1.1 z.2) := by
  have hm : Measurable (fun z : (ℝ × HeatCircle) × HeatCircle ↦
      if 0 < z.1.1 then (ProfileVariance.heatPhysical z.1.1 z.1.2 z.2).re else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst.fst)
      (Complex.measurable_re.comp ProfileVariance.heatPhysical_joint_measurable) measurable_const
  convert hm using 1
  funext z
  by_cases hr : 0 < z.1.1
  · simp only [value, dif_pos hr, ContinuousMap.coe_mk, if_pos hr, kernel_eq_physical]
  · simp only [value, dif_neg hr, ContinuousMap.zero_apply, if_neg hr]

end SHEStochastic.RealCausalHeatKernel
