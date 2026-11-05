module

public import SHE.ObservationFactorCovariance
public import SHE.WordRecursion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat
local instance observationHeat_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance observationHeat_nativePeriodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem nativeFactorAnalysis_real_cross_integral (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (u v : StoppedFourier.CircleL2)
    (hu : ∀ᵐ y ∂haarAddCircle, (u y).im = 0) (hv : ∀ᵐ y ∂haarAddCircle, (v y).im = 0) :
    (inner ℂ (nativeFactorAnalysis f m U hm hfreal hfbound u)
      (nativeFactorAnalysis f m U hm hfreal hfbound v)).re =
      ∫ y : StoppedFourier.HeatCircle, (CircleNormalization.push f y).re * (u y).re * (v y).re ∂haarAddCircle := by
  change (inner ℂ (factorAnalysis f m U hm hfreal hfbound (CircleNormalization.push.symm u))
    (factorAnalysis f m U hm hfreal hfbound (CircleNormalization.push.symm v))).re = _
  rw [factorAnalysis_real_cross_integral f m U hm hfreal hfbound _ _
    (CircleNormalization.push_symm_ae_property u (fun z => z.im = 0) hu)
    (CircleNormalization.push_symm_ae_property v (fun z => z.im = 0) hv)]
  rw [← (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).integral_comp
    (CircleNormalization.scaleMeasurableEquiv (2 * Real.pi) 1).measurableEmbedding
    (fun x : AddCircle (1 : ℝ) => (f x).re * (CircleNormalization.push.symm u x).re *
      (CircleNormalization.push.symm v x).re)]
  have hu := CircleNormalization.push_ae (CircleNormalization.push.symm u)
  have hv := CircleNormalization.push_ae (CircleNormalization.push.symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at hu hv
  apply integral_congr_ae
  filter_upwards [hu, hv, CircleNormalization.push_ae f] with y hu hv hf
  rw [hu, hv, hf]

theorem circleHeat_real_ae {t : ℝ} (ht : 0 < t) (x : StoppedFourier.HeatCircle) :
    ∀ᵐ y ∂haarAddCircle, (StoppedFourier.circleHeat t x y).im = 0 := by
  filter_upwards [ProfileVariance.heatPhysical_ae ht x] with y hy
  rw [← hy]
  have hr := congrArg Complex.im (WordRecursion.heatPhysical_real ht x y)
  simpa only [Complex.ofReal_im] using hr.symm

/-- The actual native common-Haar heat observation rows have exactly
the physical covariance density used by the Gaussian backward/Itô
identity, with the original target times and no bracket assumption. -/
theorem nativeFactorAnalysis_heat_covarianceDensity {n : ℕ}
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (Z : Fin n → WordRecursion.Observation) (t : ℝ) (i j : Fin n)
    (hi : t < (Z i).target) (hj : t < (Z j).target) :
    (inner ℂ
      (nativeFactorAnalysis f m U hm hfreal hfbound
        (StoppedFourier.circleHeat ((Z i).target-t) (Z i).center))
      (nativeFactorAnalysis f m U hm hfreal hfbound
        (StoppedFourier.circleHeat ((Z j).target-t) (Z j).center))).re =
      WordRecursion.covarianceDensity (fun p => (CircleNormalization.push f p.2).re) Z t i j := by
  rw [nativeFactorAnalysis_real_cross_integral f m U hm hfreal hfbound _ _
    (circleHeat_real_ae (sub_pos.mpr hi) _) (circleHeat_real_ae (sub_pos.mpr hj) _)]
  unfold WordRecursion.covarianceDensity WordRecursion.heatRow
  apply integral_congr_ae
  filter_upwards [ProfileVariance.heatPhysical_ae (sub_pos.mpr hi) (Z i).center,
    ProfileVariance.heatPhysical_ae (sub_pos.mpr hj) (Z j).center] with x hxi hxj
  rw [hxi, hxj]

end SHE.FiniteHaar
