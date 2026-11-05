module

public import SHE.GaussianProfile
public import SHE.GaussianProfileMean
public import SHE.LowBands
public import SHE.StateBands

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.StateSmoothing
open MeasureTheory ProbabilityTheory GaussianAudit
open scoped NNReal ENNReal Topology

/-- An actual state-scale Gaussian smoothing, with variance `ν⁻²`. -/
def variance (ν : ℝ) : ℝ≥0 := ((ν⁻¹)^2).toNNReal

def mollify (ν : ℝ) (a : ℝ → ℝ) : ℝ → ℝ := gaussianConvolution (variance ν) a

theorem variance_coe (ν : ℝ) : (variance ν : ℝ) = (ν⁻¹)^2 :=
  Real.coe_toNNReal _ (sq_nonneg _)

theorem variance_ne_zero {ν : ℝ} (hν : 0 < ν) : variance ν ≠ 0 := by
  have hp : 0 < (variance ν : ℝ) := by rw [variance_coe]; positivity
  exact_mod_cast hp.ne'

theorem variance_rpow {ν : ℝ} (hν : 0 < ν) (q : ℝ) :
    (variance ν : ℝ) ^ q = ν ^ (-2*q) := by
  rw [variance_coe,← Real.rpow_natCast_mul (inv_nonneg.mpr hν.le),Real.inv_rpow hν.le,
    ← Real.rpow_neg hν.le]
  congr 1
  ring

/-- Uniform approximation of the original Hölder coefficient by the
literal Gaussian smoother, with the true state-frequency exponent. -/
theorem mollify_error {ν β H M : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x : ℝ) :
    |mollify ν a x-a x| ≤ H*gaussianAbsMoment β*ν^(-β) := by
  have hh := GaussianProfile.gaussianAverage_holder_displacement ha hM hH hβ
    (sq_nonneg ν⁻¹) hholder x
  have he : ((ν⁻¹)^2)^(β/2) = ν^(-β) := by
    rw [← variance_coe ν,variance_rpow hν]
    congr 1
    ring
  rw [he] at hh
  exact hh

theorem mollify_mean_lipschitz {ν β H M : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x y : ℝ) :
    |mollify ν a x-mollify ν a y| ≤
      (H*gaussianAbsMoment (β+1)*ν^(1-β))*|x-y| := by
  have hh := GaussianProfileMean.gaussian_mean_lipschitz_holder_bound (variance ν)
    (variance_ne_zero hν) a ha M hM hβ hH hholder y x
  have he : (variance ν:ℝ)^((β-1)/2) = ν^(1-β) := by
    rw [variance_rpow hν]
    congr 1
    ring
  rw [he] at hh
  exact hh

theorem mollify_lipschitzWith {ν β H M : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) :
    LipschitzWith (H*gaussianAbsMoment (β+1)*ν^(1-β)).toNNReal
      (fun x => (mollify ν a x:ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    Real.coe_toNNReal _ (mul_nonneg (mul_nonneg hH (gaussianAbsMoment_nonneg _))
      (Real.rpow_nonneg hν.le _))]
  exact mollify_mean_lipschitz hν hβ hH a ha hM hholder x y

theorem measurable_mollify {ν M : ℝ} (hν : 0 < ν)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M) :
    Measurable (mollify ν a) := by
  have hc : Continuous (mollify ν a) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_gaussianConvolution (variance ν) (variance_ne_zero hν) a ha M hM x).continuousAt)
  exact hc.measurable

theorem mollify_bounded (ν : ℝ) (a : ℝ → ℝ) {M : ℝ} (hM : ∀ x, |a x| ≤ M) (x : ℝ) :
    |mollify ν a x| ≤ M := by
  have hh := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 (variance ν))
    (f := fun z => a (x+z)) (C := M) (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hM (x+z)))
  simpa [mollify,gaussianConvolution] using hh

def band (ν : ℝ) (a : ℝ → ℝ) : ℝ → ℝ := fun x => mollify (2*ν) a x-mollify ν a x

def bandSize (β H : ℝ) : ℝ := H*gaussianAbsMoment β*(1+(2:ℝ)^(-β))

def bandLip (β H : ℝ) : ℝ := H*gaussianAbsMoment (β+1)*(1+(2:ℝ)^(1-β))

theorem bandSize_nonneg {H : ℝ} (hH : 0 ≤ H) (β : ℝ) : 0 ≤ bandSize β H := by
  unfold bandSize
  exact mul_nonneg (mul_nonneg hH (gaussianAbsMoment_nonneg _)) (by positivity)

theorem bandLip_nonneg {H : ℝ} (hH : 0 ≤ H) (β : ℝ) : 0 ≤ bandLip β H := by
  unfold bandLip
  exact mul_nonneg (mul_nonneg hH (gaussianAbsMoment_nonneg _)) (by positivity)

/-- The actual smooth state band has the expected Hölder amplitude cap. -/
theorem band_bounded {ν β H M : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x : ℝ) :
    |band ν a x| ≤ bandSize β H*ν^(-β) := by
  have h2ν : 0 < 2*ν := by positivity
  have hb1 := mollify_error h2ν hβ hH a ha hM hholder x
  have hb2 := mollify_error hν hβ hH a ha hM hholder x
  calc
    _ ≤ |mollify (2*ν) a x-a x| + |a x-mollify ν a x| :=
      abs_sub_le _ _ _
    _ ≤ H*gaussianAbsMoment β*(2*ν)^(-β) + H*gaussianAbsMoment β*ν^(-β) := by
      exact add_le_add hb1 (by simpa only [abs_sub_comm] using hb2)
    _ = _ := by rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2) hν.le]; unfold bandSize; ring

/-- The derivative-scale Lipschitz bound is proved for the actual band
using centered Gaussian scores, rather than assumed as a band axiom. -/
theorem band_lipschitz_bound {ν β H M : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x y : ℝ) :
    |band ν a x-band ν a y| ≤ (bandLip β H*ν^(1-β))*|x-y| := by
  calc
    _ = |(mollify (2*ν) a x-mollify (2*ν) a y) - (mollify ν a x-mollify ν a y)| := by
      congr 1
      unfold band
      ring
    _ ≤ |mollify (2*ν) a x-mollify (2*ν) a y| + |mollify ν a x-mollify ν a y| := abs_sub _ _
    _ ≤ (H*gaussianAbsMoment (β+1)*(2*ν)^(1-β))*|x-y| +
        (H*gaussianAbsMoment (β+1)*ν^(1-β))*|x-y| :=
      add_le_add (mollify_mean_lipschitz (by positivity) hβ hH a ha hM hholder x y)
        (mollify_mean_lipschitz hν hβ hH a ha hM hholder x y)
    _ = _ := by rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2) hν.le]; unfold bandLip; ring

theorem band_lipschitzWith {ν β H M : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) :
    LipschitzWith (bandLip β H*ν^(1-β)).toNNReal (fun x => (band ν a x:ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    Real.coe_toNNReal _ (mul_nonneg (bandLip_nonneg hH β) (Real.rpow_nonneg hν.le _))]
  exact band_lipschitz_bound hν hβ hH a ha hM hholder x y

theorem band_telescope (a : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range N, band ((2:ℝ)^j) a x) = mollify ((2:ℝ)^N) a x-mollify 1 a x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold band
    rw [pow_succ,show 2*(2:ℝ)^N = (2:ℝ)^N*2 by ring]
    ring

/-- The concrete Gaussian state bands are absolutely summable for every
positive Hölder exponent. -/
theorem bands_summable {β H M : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x : ℝ) :
    Summable (fun j : ℕ => band ((2:ℝ)^j) a x) := by
  have hg := (StateBands.geometric_bands hβ (by norm_num : (0:ℝ) < 1)).1
  simp only [one_mul] at hg
  apply Summable.of_norm_bounded (hg.mul_left (bandSize β H))
  intro j
  simpa only [Real.norm_eq_abs] using band_bounded (by positivity) hβ.le hH a ha hM hholder x

theorem dyadic_mollify_tendsto {β H M : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => mollify ((2:ℝ)^N) a x) Filter.atTop (𝓝 (a x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : Filter.Tendsto (fun N : ℕ => H*gaussianAbsMoment β*((2:ℝ)^N)^(-β))
      Filter.atTop (𝓝 (0:ℝ)) := by
    have hr := StateBands.geometric_ratio hβ
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le hr.2
    have hm := hh.const_mul (H*gaussianAbsMoment β)
    simpa only [mul_zero,Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] using hm
  apply squeeze_zero (fun _ => norm_nonneg _) _ he
  intro N
  simpa only [Real.norm_eq_abs] using mollify_error (by positivity) hβ.le hH a ha hM hholder x

/-- The original Hölder coefficient is exactly recovered by the
inhomogeneous smoother plus its actual infinite smooth-band series. -/
theorem bands_reconstruct {β H M : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (x : ℝ) :
    mollify 1 a x+(∑' j : ℕ,band ((2:ℝ)^j) a x) = a x := by
  have hs := bands_summable hβ hH a ha hM hholder x
  have hl := (dyadic_mollify_tendsto hβ hH a ha hM hholder x).sub_const (mollify 1 a x)
  have ht := hs.hasSum.tendsto_sum_nat
  simp only [band_telescope] at ht
  have he := tendsto_nhds_unique ht hl
  linarith

end SHE.StateSmoothing
