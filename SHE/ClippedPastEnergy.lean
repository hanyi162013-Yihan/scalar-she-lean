module
public import SHE.ScalarHeatSubprobabilityOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ClippedPastEnergy
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

/-- Past integration takes place before clipping. Its measure need
only have mass at most one, and F is the genuine past energy. -/
theorem integral_clip (hmass : ν.real univ≤1) (F : X→ℝ) (hF : Measurable F)
    (hi : Integrable F ν) (hF0 : ∀x,0≤F x) {K r : ℝ} (hK : 0≤K) (hr : 0<r) :
    Integrable (fun x=>min 1 (K*F x/r^2)) ν ∧
      (∫x,min 1 (K*F x/r^2) ∂ν)≤min 1 (K*(∫x,F x ∂ν)/r^2) := by
  have hm : Measurable (fun x=>min 1 (K*F x/r^2)):=measurable_const.min ((hF.const_mul K).div_const _)
  have hn(x:X):0≤min 1 (K*F x/r^2):=le_min zero_le_one (div_nonneg (mul_nonneg hK (hF0 x)) (sq_nonneg _))
  have hI : Integrable (fun x=>min 1 (K*F x/r^2)) ν:=by
    apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (hn x)];exact min_le_left _ _)
  refine ⟨hI,le_min ?_ ?_⟩
  · exact (show (∫x,min 1 (K*F x/r^2) ∂ν)≤ν.real univ by
      simpa only [integral_const,smul_eq_mul,mul_one] using
        integral_mono hI (integrable_const (1:ℝ)) (fun _=>min_le_left _ _)).trans hmass
  · have he:=integral_mono hI ((hi.const_mul K).div_const (r^2)) (fun _=>min_le_right _ _)
    simpa only [integral_div,integral_const_mul] using he

/-- Iterated section energies may be bounded before any interchange of
parameterwise stochastic versions. The measurable upper budget is the
actual past energy, so this does not postulate joint reference versions. -/
theorem iterated_bound (hmass : ν.real univ≤1) (F : X→ℝ) (hF : Measurable F)
    (hi : Integrable F ν) (hF0 : ∀x,0≤F x) {K r C : ℝ} (hK : 0≤K) (hr : 0<r) (hC : 0≤C)
    (G : X→ℝ≥0∞) (hG : ∀x,G x≤ENNReal.ofReal (C*min 1 (K*F x/r^2))) :
    (∫⁻x,G x ∂ν)≤ENNReal.ofReal (C*min 1 (K*(∫x,F x ∂ν)/r^2)) := by
  have hc:=integral_clip ν hmass F hF hi hF0 hK hr
  have hp : ∀ᵐx∂ν,0≤C*min 1 (K*F x/r^2):=
    ae_of_all _ (fun x=>mul_nonneg hC (le_min zero_le_one
      (div_nonneg (mul_nonneg hK (hF0 x)) (sq_nonneg _))))
  calc
    _≤∫⁻x,ENNReal.ofReal (C*min 1 (K*F x/r^2)) ∂ν:=lintegral_mono hG
    _=ENNReal.ofReal (C*∫x,min 1 (K*F x/r^2) ∂ν):=by
      rw [←ofReal_integral_eq_lintegral_ofReal (hc.1.const_mul C) hp,integral_const_mul]
    _≤_:=ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc.2 hC)
end SHE.ClippedPastEnergy
