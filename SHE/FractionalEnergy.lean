module

public import SHE.SignedTransport
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.FractionalEnergy
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional
local instance fractionalEnergy_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem nonnegative_tsum_integrable {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (F : I → X → ℝ) (hF : ∀ i, Integrable (F i) μ)
    (hF0 : ∀ i, 0 ≤ᵐ[μ] F i) (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, F i x) μ := by
  have he := integral_tsum_of_summable_integral_norm hF hs
  have hi0 (i : I) : 0 ≤ ∫ x, F i x ∂μ := integral_nonneg_of_ae (hF0 i)
  have hsi : Summable (fun i => ∫ x, F i x ∂μ) :=
    hs.of_norm_bounded (fun i => norm_integral_le_integral_norm _)
  by_cases hz : (∑' i, ∫ x, F i x ∂μ) = 0
  · have hzero (i : I) : (∫ x, F i x ∂μ) = 0 := by
      have hh := hsi.le_tsum i (fun k _ => hi0 k)
      rw [hz] at hh
      exact le_antisymm hh (hi0 i)
    have hae : ∀ᵐ x ∂μ, ∀ i, F i x = 0 := ae_all_iff.mpr (fun i =>
      (integral_eq_zero_iff_of_nonneg_ae (hF0 i) (hF i)).mp (hzero i))
    apply (integrable_zero X ℝ μ).congr
    filter_upwards [hae] with x hx
    change (0:ℝ) = _
    simp only [hx,tsum_zero]
  · by_contra hh
    rw [integral_undef hh] at he
    exact hz he

def spectral (ρ : ℝ) (f : CircleL2) : ℝ :=
  ∑' n : ℤ, |(n:ℝ)|^(2*ρ)*‖fourierCoeff f n‖^2

/-- The exact reverse Fourier--Gagliardo bridge, including actual
integrability of the spatial translation form. No Sobolev identification
is supplied as a hypothesis; only the literal Fourier square summability
defining the fractional space is required. -/
theorem gagliardo_eq {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (f : CircleL2)
    (hf : Summable (fun n : ℤ => |(n:ℝ)|^(2*ρ)*‖fourierCoeff f n‖^2)) :
    IntegrableOn (fun z : ℝ => circleTranslationEnergy f z*z^(-1-2*ρ)) (Ioi 0) ∧
      circleFractionalSq ρ f = unitFractionalMass ρ*spectral ρ f := by
  let F : ℤ → ℝ → ℝ := fun n z => frequencyAmplitude n z*‖fourierCoeff f n‖^2*z^(-1-2*ρ)
  have hF (n : ℤ) : IntegrableOn (F n) (Ioi 0) := by
    have hh := (integrable_frequency_fractional hρ hρhalf n).const_mul (‖fourierCoeff f n‖^2)
    change Integrable (F n) (volume.restrict (Ioi 0))
    have he : F n = fun z => ‖fourierCoeff f n‖^2*(frequencyAmplitude n z*z^(-1-2*ρ)) := by
      funext z
      dsimp only [F]
      ring
    rw [he]
    exact hh
  have hF0 (n : ℤ) : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] F n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hz.le _)
  have hint (n : ℤ) : (∫ z : ℝ in Ioi 0, F n z) =
      unitFractionalMass ρ*(|(n:ℝ)|^(2*ρ)*‖fourierCoeff f n‖^2) := by
    calc
      _ = ‖fourierCoeff f n‖^2*(∫ z : ℝ in Ioi 0, frequencyAmplitude n z*z^(-1-2*ρ)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with z
        dsimp only [F]
        ring
      _ = _ := by rw [frequency_fractional_integral_all hρ]; ring
  have hnorm (n : ℤ) : (∫ z : ℝ in Ioi 0, ‖F n z‖) =
      unitFractionalMass ρ*(|(n:ℝ)|^(2*ρ)*‖fourierCoeff f n‖^2) := by
    rw [← hint n]
    apply integral_congr_ae
    filter_upwards [hF0 n] with z hz
    exact Real.norm_of_nonneg hz
  have hs : Summable (fun n => ∫ z : ℝ in Ioi 0, ‖F n z‖) := by
    simp_rw [hnorm]
    exact hf.mul_left _
  have hsum (z : ℝ) : (∑' n, F n z) = circleTranslationEnergy f z*z^(-1-2*ρ) := by
    have hh := (hasSum_translation_energy f (Lp.memLp f) (z : AddCircle (1:ℝ))).mul_right (z^(-1-2*ρ))
    simpa only [F,frequencyAmplitude,circleTranslationEnergy] using hh.tsum_eq
  have hi := nonnegative_tsum_integrable (volume.restrict (Ioi (0:ℝ))) F hF hF0 hs
  refine ⟨?_, ?_⟩
  · change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    simpa only [hsum] using hi
  unfold circleFractionalSq spectral
  simp_rw [← hsum]
  rw [← integral_tsum_of_summable_integral_norm hF hs]
  simp_rw [hint]
  exact tsum_mul_left

end SHE.FractionalEnergy
