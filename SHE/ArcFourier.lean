module

public import SHE.ArcSobolev

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ArcFourier
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FractionalHardy ArcSobolev
open scoped ENNReal
local instance arcFourier_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def weight (Λ ρ : ℝ) (n : ℤ) : ℝ := (Λ+(n:ℝ)^2)^ρ
def positiveSq (Λ ρ : ℝ) (f : AddCircle (1:ℝ) → ℂ) : ℝ :=
  ∑' n : ℤ, weight Λ ρ n*‖fourierCoeff f n‖^2

theorem translation_congr {f g : AddCircle (1:ℝ) → ℂ} (h : f =ᵐ[haarAddCircle] g) (z : ℝ) :
    circleTranslationEnergy f z = circleTranslationEnergy g z := by
  apply integral_congr_ae
  filter_upwards [h,(measurePreserving_add_right haarAddCircle (z : AddCircle (1:ℝ))).quasiMeasurePreserving.ae h] with x hx hxz
  rw [hx,hxz]

theorem fractional_congr {f g : AddCircle (1:ℝ) → ℂ} (h : f =ᵐ[haarAddCircle] g) (ρ : ℝ) :
    circleFractionalSq ρ f = circleFractionalSq ρ g := by
  unfold circleFractionalSq
  simp only [translation_congr h]

theorem base_summable (f : AddCircle (1:ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖^2) := by
  have he := fourierCoeff_congr_ae (hf.coeFn_toLp)
  simpa only [he] using summable_fourier_sq (hf.toLp f)

theorem base_tsum (f : AddCircle (1:ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle) :
    (∑' n : ℤ, ‖fourierCoeff f n‖^2) = ∫ x, ‖f x‖^2 ∂haarAddCircle := by
  have he := fourierCoeff_congr_ae (hf.coeFn_toLp)
  rw [← he,tsum_sq_fourierCoeff]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖^2))

theorem weight_spectral_le {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 ≤ ρ) (n : ℤ) :
    |(n:ℝ)|^(2*ρ) ≤ weight Λ ρ n := by
  have he : |(n:ℝ)|^(2*ρ) = ((n:ℝ)^2)^ρ := by
    rw [Real.rpow_mul (abs_nonneg (n:ℝ)) 2 ρ,Real.rpow_two,sq_abs]
  rw [he]
  exact Real.rpow_le_rpow (sq_nonneg _) (le_add_of_nonneg_left hΛ) hρ

theorem weight_mass_le {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 ≤ ρ) (n : ℤ) :
    Λ^ρ ≤ weight Λ ρ n :=
  Real.rpow_le_rpow hΛ (le_add_of_nonneg_right (sq_nonneg _)) hρ

theorem massive_summable_of_gagliardo {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f : AddCircle (1:ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle)
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z*z^(-1-2*ρ)) (Ioi 0)) :
    Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff f n‖^2) := by
  apply Summable.of_nonneg_of_le (fun n => by unfold weight; positivity) _
    (((base_summable f hf).mul_left (Λ^ρ)).add (summable_spectral_fractional hρ hρhalf f hf hG))
  intro n
  have hh := CircleStep.scaled_frequency_weight_le (κ := 1) zero_le_one hΛ hρ hρhalf n
  simp only [one_mul,Real.one_rpow] at hh
  simpa only [add_mul,weight] using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fourierCoeff f n‖)

theorem massive_le_base_gagliardo {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f : AddCircle (1:ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle)
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z*z^(-1-2*ρ)) (Ioi 0)) :
    positiveSq Λ ρ f ≤ Λ^ρ*(∫ x, ‖f x‖^2 ∂haarAddCircle)+(unitFractionalMass ρ)⁻¹*circleFractionalSq ρ f := by
  have hs := summable_spectral_fractional hρ hρhalf f hf hG
  have hh : positiveSq Λ ρ f ≤ Λ^ρ*(∑' n : ℤ, ‖fourierCoeff f n‖^2)+
      ∑' n : ℤ, |(n:ℝ)|^(2*ρ)*‖fourierCoeff f n‖^2 := by
    unfold positiveSq
    rw [← tsum_mul_left,← Summable.tsum_add ((base_summable f hf).mul_left (Λ^ρ)) hs]
    apply Summable.tsum_le_tsum _ (massive_summable_of_gagliardo hΛ hρ hρhalf f hf hG)
      (((base_summable f hf).mul_left (Λ^ρ)).add hs)
    intro n
    have hh := CircleStep.scaled_frequency_weight_le (κ := 1) zero_le_one hΛ hρ hρhalf n
    simp only [one_mul,Real.one_rpow] at hh
    simpa only [weight,add_mul] using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fourierCoeff f n‖)
  rw [base_tsum f hf] at hh
  exact hh.trans (add_le_add le_rfl (spectral_fractional_tsum_bound hρ hρhalf f hf hG))

theorem continuous_gagliardo_of_massive {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (u : C(AddCircle (1:ℝ),ℂ))
    (hs : Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff u n‖^2)) :
    IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0) ∧
      circleFractionalSq ρ u ≤ unitFractionalMass ρ*positiveSq Λ ρ u := by
  have hspec := Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (weight_spectral_le hΛ hρ.le n) (sq_nonneg ‖fourierCoeff u n‖)) hs
  let f : CircleL2 := ContinuousMap.toLp 2 haarAddCircle ℂ u
  have he : f =ᵐ[haarAddCircle] u := ContinuousMap.coeFn_toLp haarAddCircle u
  have hcoeff := fourierCoeff_congr_ae he
  have hspecf : Summable (fun n : ℤ => |(n:ℝ)|^(2*ρ)*‖fourierCoeff f n‖^2) := by
    simpa only [hcoeff] using hspec
  have hg := FractionalEnergy.gagliardo_eq hρ hρhalf f hspecf
  refine ⟨?_,?_⟩
  · simpa only [translation_congr he] using! hg.1
  · rw [← fractional_congr he ρ,hg.2]
    apply mul_le_mul_of_nonneg_left _ (unitFractionalMass_pos hρ hρhalf).le
    unfold FractionalEnergy.spectral positiveSq
    rw [hcoeff]
    exact Summable.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_right (weight_spectral_le hΛ hρ.le n) (sq_nonneg _)) hspec hs

theorem cutoff_memLp (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : MemLp (cutoff a b u) 2 haarAddCircle :=
  (u.memLp haarAddCircle ℂ).indicator (ArcGeometry.measurableSet_arcSet a b).nullMeasurableSet

theorem cutoff_square_le (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) :
    (∫ x, ‖cutoff a b u x‖^2 ∂haarAddCircle) ≤ circleSquare u := by
  have hc := cutoff_memLp a b u
  have hu : MemLp u 2 haarAddCircle := u.memLp haarAddCircle ℂ
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc)
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)
  intro x
  change ‖(ArcGeometry.arcSet a b).indicator u x‖^2 ≤ ‖u x‖^2
  by_cases hx : x ∈ ArcGeometry.arcSet a b
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact sq_nonneg _

theorem massive_base_le {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 ≤ ρ)
    (u : C(AddCircle (1:ℝ),ℂ))
    (hs : Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff u n‖^2)) :
    Λ^ρ*circleSquare u ≤ positiveSq Λ ρ u := by
  rw [circleSquare,← base_tsum u (u.memLp haarAddCircle ℂ),← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (weight_mass_le hΛ hρ n) (sq_nonneg _))
    ((base_summable u (u.memLp haarAddCircle ℂ)).mul_left _) hs

/-- A literal interval indicator acts boundedly on the actual massive
Fourier Sobolev norm. The constant is independent of both endpoints and
of the mass parameter Λ ≥ 1. -/
theorem exists_massive_cutoff_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ)),
      Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff u n‖^2) →
      Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff (cutoff a b u) n‖^2) ∧
        positiveSq Λ ρ (cutoff a b u) ≤ C*positiveSq Λ ρ u := by
  obtain ⟨C,hC,hbound⟩ := exists_cutoff_gagliardo_bound hρ hρhalf
  let M := unitFractionalMass ρ
  have hM : 0 < M := unitFractionalMass_pos hρ hρhalf
  refine ⟨1+M⁻¹*C*(1+M),by positivity,?_⟩
  intro Λ hΛ a b u hs
  have hu := continuous_gagliardo_of_massive (zero_le_one.trans hΛ) hρ hρhalf u hs
  have hcut := cutoff_gagliardo_integrable hρ hρhalf a b u hu.1
  refine ⟨massive_summable_of_gagliardo (zero_le_one.trans hΛ) hρ hρhalf _ (cutoff_memLp a b u) hcut,?_⟩
  have hb := massive_le_base_gagliardo (zero_le_one.trans hΛ) hρ hρhalf _ (cutoff_memLp a b u) hcut
  have hcutG := hbound a b u hu.1
  have hbase := massive_base_le (zero_le_one.trans hΛ) hρ.le u hs
  have hsq := cutoff_square_le a b u
  have hmass : 1 ≤ Λ^ρ := Real.one_le_rpow hΛ hρ.le
  have hsq0 := circleSquare_nonneg u
  have hsqE : circleSquare u ≤ positiveSq Λ ρ u := by nlinarith
  have hmulbase := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (zero_le_one.trans hΛ) ρ)
  change _ ≤ Λ^ρ*(∫ x, ‖cutoff a b u x‖^2 ∂haarAddCircle)+M⁻¹*circleFractionalSq ρ (cutoff a b u) at hb
  have huG : circleFractionalSq ρ u ≤ M*positiveSq Λ ρ u := hu.2
  have hscale := mul_le_mul_of_nonneg_left hcutG (inv_nonneg.mpr hM.le)
  have hscale2 := mul_le_mul_of_nonneg_left (add_le_add hsqE huG)
    (mul_nonneg (inv_nonneg.mpr hM.le) hC.le)
  nlinarith

end SHE.ArcFourier
