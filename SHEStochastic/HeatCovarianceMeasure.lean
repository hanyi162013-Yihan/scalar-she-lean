module

public import SHE.ProfileVariance
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.HeatCovarianceMeasure
open MeasureTheory Set SHE SHE.StoppedFourier SHE.ProfileVariance
open scoped ENNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev Circle := HeatCircle
abbrev Window := {r : ℝ // r ∈ Ioc 0 1}

def weight (r : ℝ) (x : Circle) (p : ℝ × Circle) : ℝ := ‖heatPhysical (r-p.1) x p.2‖ ^ 2
def base (r : ℝ) : Measure (ℝ × Circle) := (volume.restrict (Ioo 0 r)).prod AddCircle.haarAddCircle

theorem weight_measurable (r : ℝ) (x : Circle) : Measurable (weight r x) :=
  ((heatPhysical_measurable x).comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)).norm.pow_const 2

theorem weight_integrable (r : Window) (x : Circle) : Integrable (weight r.val x) (base r.val) := by
  have hm := weight_measurable r.val x
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact heatPhysical_square_integrable (sub_pos.mpr hs.2) x
  · have hi := (varianceMap_bound (c := fun _ => 1) measurable_const r.property.1 r.property.2
      (by norm_num : (0 : ℝ) ≤ 1) (by intro s hs y; norm_num) x).1.1
    apply (hi.mono_set Ioo_subset_Ioc_self).congr
    filter_upwards with s
    simp only [varianceDensity, weight, mul_one, Real.norm_of_nonneg (sq_nonneg _)]

/-- Positive time-space heat-square averaging on the same analytic circle
used by the existing scalar profile estimates. -/
def measure (r : Window) (x : Circle) : Measure (ℝ × Circle) :=
  (base r.val).withDensity (fun p => ENNReal.ofReal (weight r.val x p))

instance finite (r : Window) (x : Circle) : IsFiniteMeasure (measure r x) :=
  isFiniteMeasure_withDensity_ofReal (weight_integrable r x).hasFiniteIntegral

theorem ae_time (r : Window) (x : Circle) : ∀ᵐ p ∂measure r x, p.1 ∈ Ioo 0 r.val := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  change ∀ᵐ p ∂(volume.restrict (Ioo 0 r.val)).prod AddCircle.haarAddCircle, p.1 ∈ Ioo 0 r.val
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)]
  exact (ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
    Filter.Eventually.of_forall fun _ => hs

theorem integral_congr_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Window) (x : Circle) (f g : ℝ × Circle → E)
    (hfg : ∀ s ∈ Ioo 0 r.val, ∀ y, f (s,y) = g (s,y)) :
    (∫ p, f p ∂measure r x) = ∫ p, g p ∂measure r x := by
  apply integral_congr_ae
  filter_upwards [ae_time r x] with p hp
  exact hfg p.1 hp p.2

theorem integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Window) (x : Circle) (f : ℝ × Circle → E) :
    (∫ p, f p ∂measure r x) = ∫ p, weight r.val x p • f p ∂base r.val := by
  rw [measure, integral_withDensity_eq_integral_toReal_smul
    (weight_measurable r.val x).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [weight, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem mass (r : Window) (x : Circle) :
    (measure r x).real univ = varianceMap (fun _ => 1) r.val x := by
  have hc : (∫ _ : ℝ × Circle, (1 : ℝ) ∂measure r x) = (measure r x).real univ := by simp
  rw [← hc, integral]
  simp only [smul_eq_mul, mul_one]
  rw [base, integral_prod _ (weight_integrable r x), varianceMap, intervalIntegral.integral_of_le r.property.1.le]
  have he : (volume.restrict (Ioo 0 r.val) : Measure ℝ) = volume.restrict (Ioc 0 r.val) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [he]
  apply integral_congr_ae
  filter_upwards with s
  simp only [weight, varianceDensity, mul_one]

theorem mass_bounds (r : Window) (x : Circle) :
    lowerConstant * r.val ^ (1/2 : ℝ) ≤ (measure r x).real univ ∧
      (measure r x).real univ ≤ upperConstant * r.val ^ (1/2 : ℝ) := by
  rw [mass]
  simpa only [mul_one] using varianceMap_elliptic (c := fun _ => 1) measurable_const
    r.property.1 r.property.2 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by intro s hs y; rfl) (by intro s hs y; rfl) x

theorem scalar_integral (r : Window) (x : Circle) (f : ℝ × Circle → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ p, |f p| ≤ B) :
    (∫ p, f p ∂measure r x) = varianceMap f r.val x := by
  have hi : Integrable (fun p => weight r.val x p * f p) (base r.val) :=
    (weight_integrable r x).mul_bdd hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hB p)
  rw [integral]
  simp only [smul_eq_mul]
  rw [base, integral_prod _ hi, varianceMap, intervalIntegral.integral_of_le r.property.1.le]
  have he : (volume.restrict (Ioo 0 r.val) : Measure ℝ) = volume.restrict (Ioc 0 r.val) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [he]
  rfl

end SHEStochastic.HeatCovarianceMeasure
