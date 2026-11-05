module

public import SHE.NativeHeatKernel
public import SHE.WordRecursion
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeHeatSpan
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance
open scoped BigOperators InnerProductSpace
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem continuous_heatPhysical_space {t : ℝ} (ht : 0 < t) :
    Continuous (fun p : HeatCircle × HeatCircle => heatPhysical t p.1 p.2) := by
  have hs : Summable (fun n : ℤ => Real.exp (-t*(n : ℝ)^2)) := by
    simpa only [HeatTrace.multiplier,neg_zero,Real.rpow_zero,one_mul] using
      HeatTrace.multiplier_int_summable (Λ := 1) (ρ := 0) (by norm_num) (by norm_num) ht
  unfold heatPhysical heatCrossKernel
  apply continuous_tsum (fun n => by fun_prop) hs
  intro n p
  simp only [norm_mul,show ‖fourier n p.2‖ = 1 from Circle.norm_coe _,
    show ‖fourier (-n) p.1‖ = 1 from Circle.norm_coe _,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact le_rfl

/-- The positive continuous native kernel equals the physical Fourier
kernel at every point, not just after choosing separate AE versions. -/
theorem kernel_eq_physical {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    kernel t ht a x = heatPhysical t a x := by
  have hc : Continuous (heatPhysical t a) :=
    (continuous_heatPhysical_space ht).comp (continuous_const.prodMk continuous_id)
  exact congrFun (Measure.eq_of_ae_eq (kernel_physical_ae ht a) (kernel t ht a).continuous hc) x

theorem kernel_symm {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    kernel t ht a x = kernel t ht x a := by
  rw [kernel_eq_physical,kernel_eq_physical]
  exact WordRecursion.heatCrossKernel_symm t x a

theorem kernel_real_nonneg {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    (kernel t ht a x).im = 0 ∧ 0 ≤ (kernel t ht a x).re :=
  HeatMarkov.kernel_real_nonneg (clock_pos ht) (unitCenter x-unitCenter a)

theorem kernel_norm_eq_re {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    ‖kernel t ht a x‖ = (kernel t ht a x).re :=
  HeatMarkov.kernel_norm_eq_re (clock_pos ht) (unitCenter x-unitCenter a)

/-- Exact native-circle convolution along two consecutive positive heat
edges. The age is the sum of the true physical ages. -/
theorem kernel_convolution {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a x : HeatCircle) :
    (∫ y : HeatCircle,kernel s hs a y*kernel t ht y x ∂haarAddCircle) =
      kernel (s+t) (add_pos hs ht) a x := by
  have hpair : (∫ y : HeatCircle,heatPhysical s a y*heatPhysical t x y ∂haarAddCircle) =
      inner ℂ (circleHeat s a) (circleHeat t x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heatPhysical_ae hs a,heatPhysical_ae ht x] with y hy hz
    rw [← hy,← hz,RCLike.inner_apply]
    have hreal := WordRecursion.heatPhysical_real hs a y
    have hconj : (starRingEnd ℂ) (heatPhysical s a y) = heatPhysical s a y := by
      rw [← hreal]
      exact Complex.conj_ofReal _
    rw [hconj]
    ring
  calc
    _ = ∫ y : HeatCircle,heatPhysical s a y*heatPhysical t x y ∂haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        dsimp only
        rw [kernel_symm ht y x,kernel_eq_physical,kernel_eq_physical])
    _ = inner ℂ (circleHeat s a) (circleHeat t x) := hpair
    _ = kernel (s+t) (add_pos hs ht) a x := by
      rw [circleHeat_cross_gram hs ht,kernel_eq_physical]
      exact WordRecursion.heatCrossKernel_symm (s+t) a x

theorem kernel_norm_convolution {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a x : HeatCircle) :
    (∫ y : HeatCircle,‖kernel s hs a y‖*‖kernel t ht y x‖ ∂haarAddCircle) =
      ‖kernel (s+t) (add_pos hs ht) a x‖ := by
  have hi : Integrable (fun y : HeatCircle => kernel s hs a y*kernel t ht y x) haarAddCircle := by
    have hc : Continuous (fun y : HeatCircle => kernel s hs a y*kernel t ht y x) := by
      simp_rw [kernel_symm ht]
      exact (kernel s hs a).continuous.mul (kernel t ht x).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := congrArg Complex.re (kernel_convolution hs ht a x)
  change RCLike.re (∫ y : HeatCircle,kernel s hs a y*kernel t ht y x ∂haarAddCircle) = _ at he
  rw [← integral_re hi] at he
  change (∫ y : HeatCircle,(kernel s hs a y*kernel t ht y x).re ∂haarAddCircle) = _ at he
  simpa only [Complex.mul_re,(kernel_real_nonneg hs a _).1,(kernel_real_nonneg ht _ x).1,
    zero_mul,sub_zero,kernel_norm_eq_re] using he

end SHE.NativeHeatSpan
