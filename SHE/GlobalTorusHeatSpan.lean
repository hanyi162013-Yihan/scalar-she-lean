module

public import SHE.HeatTorusKernel
public import SHE.GlobalFourierSpan

/-! Collision-uniform finite heat-span localization on the actual circle,
including arbitrary centers, all age ratios, and exact Fourier coefficients. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.GlobalTorusHeatSpan
open MeasureTheory Set Real SHE.HeatLine SHE.HeatPeriodization SHE.HeatTorus
  SHE.HeatTorusKernel AddCircle
open scoped FourierTransform

def weight (t : ℝ) (a x : UnitAddCircle) : ℝ :=
  (sqrt t)⁻¹ * exp (-(dist x a) ^ 2 / (8 * t))

/-- The full finite torus heat-span theorem. The conclusion gives a genuine
continuous representative of the actual physical L² class and a pointwise
Gaussian envelope. All centers, collisions and age ratios are allowed. -/
theorem finite_torus_heat_span_envelope (q : ℕ) :
    ∃ h C : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ F : CircleL2, F ∈ Submodule.span ℂ (Set.range (fun i => unitHeatKernel (t i) (a i))) →
      ∃ P : C(UnitAddCircle, ℂ), ContinuousMap.toLp 2 haarAddCircle ℂ P = F ∧
        ∀ x : UnitAddCircle, ‖P x‖ ^ 2 ≤ C * ‖F‖ ^ 2 * ∑ i, weight (t i) (a i) x := by
  obtain ⟨h, C, hh, hh1, hC, henv⟩ := exists_periodized_heat_span_envelope q
    (SHE.CircleCut.margin_pos q) (circle_margin_le_one q)
  refine ⟨h, C, hh, hh1, hC, ?_⟩
  intro t a ht hth F hF
  obtain ⟨c, b, f, hf, hb, hmargin, htrans⟩ := exists_cut_line_lift q t a ht F hF
  let P := continuousTranslate c (circlePeriodize t b ht f hf)
  have hrep : ContinuousMap.toLp 2 haarAddCircle ℂ P = F := by
    exact (toLp_continuousTranslate c (circlePeriodize t b ht f hf)).trans htrans
  have hn : ‖periodizationL2 t b ht f hf‖ = ‖F‖ := by
    rw [← htrans, translate_norm]
  refine ⟨P, hrep, ?_⟩
  intro x
  have hbound := henv t b ht hth hmargin f hf (x - c)
  rw [hn] at hbound
  have hd (i : Fin q) : dist (x - c) (b i : UnitAddCircle) = dist x (a i) := by
    rw [← hb i]
    simpa only [add_sub_cancel_right] using (dist_sub_right x ((b i : UnitAddCircle) + c) c)
  simpa only [P, continuousTranslate, ContinuousMap.coe_mk, hd, weight] using hbound

theorem finite_torus_heat_span_envelope_ae (q : ℕ) :
    ∃ h C : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ F : CircleL2, F ∈ Submodule.span ℂ (Set.range (fun i => unitHeatKernel (t i) (a i))) →
      ∀ᵐ x ∂haarAddCircle, ‖F x‖ ^ 2 ≤ C * ‖F‖ ^ 2 * ∑ i, weight (t i) (a i) x := by
  obtain ⟨h, C, hh, hh1, hC, henv⟩ := finite_torus_heat_span_envelope q
  refine ⟨h, C, hh, hh1, hC, ?_⟩
  intro t a ht hth F hF
  obtain ⟨P, hrep, hp⟩ := henv t a ht hth F hF
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle P
  rw [hrep] at h
  filter_upwards [h] with x hx
  rw [hx]
  exact hp x

/-- The full collision-uniform Fourier localization of every physical
finite circle heat span. Its energy is the actual circle L² norm. -/
theorem finite_torus_heat_span_fourier_envelope (q : ℕ) :
    ∃ h C r : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < r ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ F : CircleL2, F ∈ Submodule.span ℂ (Set.range (fun i => unitHeatKernel (t i) (a i))) →
      ∀ n : ℤ, ‖fourierCoeff F n‖ ^ 2 ≤ C * ‖F‖ ^ 2 *
        ∑ i, SHE.GlobalFourierSpan.frequencyWeight r (t i) (n : ℝ) := by
  obtain ⟨D, r, hD, hr, hfourier⟩ := SHE.GlobalFourierSpan.global_heat_span_fourier_envelope q
  obtain ⟨h, hh, hh1, henergy⟩ := exists_heat_span_periodization_energy_bound q
    (SHE.CircleCut.margin_pos q) (circle_margin_le_one q)
  refine ⟨h, 4 * D, r, hh, hh1, by positivity, hr, ?_⟩
  intro t a ht hth F hF n
  obtain ⟨c, b, f, hf, hb, hmargin, htrans⟩ := exists_cut_line_lift q t a ht F hF
  have hn : ‖periodizationL2 t b ht f hf‖ = ‖F‖ := by rw [← htrans, translate_norm]
  have he := henergy t b ht hth hmargin f hf
  rw [hn] at he
  have hc : ‖fourierCoeff F n‖ ^ 2 = ‖𝓕 (fun y : ℝ => f (y : ℂ)) (n : ℝ)‖ ^ 2 := by
    rw [← htrans, fourierCoeff_translate, norm_mul,
      (show ‖fourier (-n) c‖ = 1 from Circle.norm_coe _), one_mul,
      periodizationL2_fourierCoeff]
  rw [hc]
  have hbnd := hfourier t b ht f hf (n : ℝ)
  have hW : 0 ≤ ∑ i, SHE.GlobalFourierSpan.frequencyWeight r (t i) (n : ℝ) :=
    Finset.sum_nonneg (fun i _ => SHE.GlobalFourierSpan.frequencyWeight_nonneg _ _ _)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hD.le) hW
  apply hbnd.trans
  convert! hm using 1
  ring

end SHE.GlobalTorusHeatSpan
