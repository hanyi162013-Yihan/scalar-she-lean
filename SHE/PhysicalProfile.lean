module

public import SHE.ProfileStability

@[expose] public section
set_option autoImplicit false

/-! Scalar profiles driven by genuine physical heat means of L² data. -/
noncomputable section
namespace SHE.PhysicalProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile ProfileL2 ProfileStability

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def heatMeanSeries (d : CircleL2) (p : ℝ × HeatCircle) : ℂ :=
  ∑' n : ℤ, (Real.exp (-p.1 * (n : ℝ) ^ 2) : ℂ) * fourierCoeff d n * fourier n p.2

def physicalHeatMean (d : CircleL2) (p : ℝ × HeatCircle) : ℝ := (heatMeanSeries d p).re

theorem heatMeanSeries_measurable (d : CircleL2) : Measurable (heatMeanSeries d) := by
  apply Measurable.tsum
  intro n
  have he : Measurable (fun p : ℝ × HeatCircle =>
      (Real.exp (-p.1 * (n : ℝ) ^ 2) : ℂ)) := by fun_prop
  exact (he.mul measurable_const).mul ((fourier n).continuous.measurable.comp measurable_snd)

theorem physicalHeatMean_measurable (d : CircleL2) : Measurable (physicalHeatMean d) :=
  Complex.continuous_re.measurable.comp (heatMeanSeries_measurable d)

theorem fourierCoeff_continuous (n : ℤ) : Continuous (fun d : CircleL2 => fourierCoeff d n) := by
  have hc := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp
    (fourierBasis (T := 2 * Real.pi)).repr.continuous
  change Continuous (fun d : CircleL2 => (fourierBasis (T := 2 * Real.pi)).repr d n) at hc
  simpa only [fourierBasis_repr] using hc

/-- The physical heat mean is jointly Borel in the actual L² input, age,
and spatial center. -/
theorem physicalHeatMean_joint_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2] :
    Measurable (fun p : CircleL2 × (ℝ × HeatCircle) => physicalHeatMean p.1 p.2) := by
  have hm : Measurable (fun p : CircleL2 × (ℝ × HeatCircle) => heatMeanSeries p.1 p.2) := by
    apply Measurable.tsum
    intro n
    have he : Measurable (fun p : CircleL2 × (ℝ × HeatCircle) =>
        (Real.exp (-p.2.1 * (n : ℝ) ^ 2) : ℂ)) := by fun_prop
    exact (he.mul ((fourierCoeff_continuous n).measurable.comp measurable_fst)).mul
      ((fourier n).continuous.measurable.comp measurable_snd.snd)
  exact Complex.continuous_re.measurable.comp hm

theorem physicalHeatMean_eq {r : ℝ} (hr : 0 < r) (d : CircleL2) (x : HeatCircle) :
    physicalHeatMean d (r, x) = (inner ℂ (circleHeat r x) d).re := by
  exact congrArg Complex.re (heat_kernel_inner_hasSum hr x d).tsum_eq

theorem physicalHeatMean_memLp {r : ℝ} (hr : 0 < r) (d : CircleL2) :
    MemLp (fun x => physicalHeatMean d (r, x)) 2 haarAddCircle := by
  have hm := (physicalHeatMean_measurable d).comp
    (measurable_const.prodMk measurable_id : Measurable (fun x : HeatCircle => (r, x)))
  apply bounded_memLp (C := ‖circleHeat r (0 : HeatCircle)‖ * ‖d‖) hm
  intro x
  change |physicalHeatMean d (r, x)| ≤ ‖circleHeat r (0 : HeatCircle)‖ * ‖d‖
  rw [physicalHeatMean_eq hr]
  have hc : ‖circleHeat r x‖ = ‖circleHeat r (0 : HeatCircle)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (circleHeat_norm_sq_center r x 0)
  exact (Complex.abs_re_le_norm _).trans (by simpa only [hc] using
    (norm_inner_le_norm (𝕜 := ℂ) (circleHeat r x) d))

/-- The actual spatial heat mean contracts the original L² input. -/
theorem physicalHeatMean_contraction {r : ℝ} (hr : 0 < r) (d : CircleL2) :
    normTwo haarAddCircle (fun x => physicalHeatMean d (r, x)) ≤ ‖d‖ := by
  let S : CircleL2 := circleHeatOperator r hr.le d
  have hm := normTwo_mono (physicalHeatMean_memLp hr d) (Lp.memLp S).norm
    (by
      filter_upwards [heat_kernel_inner_ae hr d] with x hx
      change |physicalHeatMean d (r, x)| ≤ |‖S x‖|
      rw [physicalHeatMean_eq hr, abs_of_nonneg (norm_nonneg _)]
      simpa only [hx] using Complex.abs_re_le_norm (inner ℂ (circleHeat r x) d))
  have hn : normTwo haarAddCircle (fun x => ‖S x‖) = ‖S‖ := by
    unfold normTwo
    rw [← L2_norm_sq_eq_integral S, Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hm
  exact hm.trans (circleHeatOperator_norm_le r hr.le d)

theorem physicalHeatMean_difference {r : ℝ} (hr : 0 < r) (d e : CircleL2) (x : HeatCircle) :
    physicalHeatMean d (r, x) - physicalHeatMean e (r, x) = physicalHeatMean (d - e) (r, x) := by
  simp only [physicalHeatMean_eq hr, inner_sub_right, Complex.sub_re]

theorem physicalHeatMean_l2_difference {r : ℝ} (hr : 0 < r) (d e : CircleL2) :
    MemLp (fun x => physicalHeatMean d (r, x) - physicalHeatMean e (r, x)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => physicalHeatMean d (r, x) - physicalHeatMean e (r, x)) ≤ ‖d - e‖ := by
  have he : (fun x => physicalHeatMean d (r, x) - physicalHeatMean e (r, x)) =
      fun x => physicalHeatMean (d - e) (r, x) := funext (physicalHeatMean_difference hr d e)
  rw [he]
  exact ⟨physicalHeatMean_memLp hr _, physicalHeatMean_contraction hr _⟩

/-- One-input stability driven by actual physical heat means of arbitrary
L² inputs. There is no supplied Gaussian Lipschitz estimate, covariance
transfer bound, weighted supremum, or mean contraction hypothesis. -/
theorem physical_profile_l2_stability {a : ℝ → ℝ} {c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β h : ℝ} (u v : CircleL2)
    (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hsmall : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
      h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (physicalHeatMean u) c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a (physicalHeatMean v) d r x) :
    ∀ r ∈ Ioc 0 h,
      normTwo haarAddCircle (fun x => c (r, x) - d (r, x)) ≤
        2 * (meanConstant ell H β * ‖u - v‖) * r ^ ((β - 1) / 4) := by
  have he := scalar_profile_l2_stability ha hc hd hell hM hH hβ hβ1 hh hh1 (norm_nonneg _)
    haB hholder hcb hdb (fun r hr => physicalHeatMean_l2_difference hr.1 u v) hsmall hcf hdf
  exact fun r hr => (he r hr).1

end SHE.PhysicalProfile
