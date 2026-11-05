module

public import SHE.StoppedBoundedBracket
public import SHE.StandardTerminalBDG

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.BoundedStoppedMoments
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (hH : (H:ℝ)≤1)
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H)
include hH

/-- A bounded predictable noise row gives actual sixteenth-moment
time increments of its original stopped integral. This supplies the
proved Kolmogorov construction without an external continuity premise. -/
theorem ordered_increment (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (u : Process (E := C) 𝓕 μ H) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H, ‖u p‖^2≤K)
    (s t : ℝ≥0) (hst : s≤t) (htH : t≤H) :
    (∫⁻ ω,ENNReal.ofReal (‖I.integral (stop 𝓕 μ H t u) ω-
      I.integral (stop 𝓕 μ H s u) ω‖^16) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*K^8*((t:ℝ)-(s:ℝ))^2) := by
  let w := stop 𝓕 μ H (t:ℝ) u-stop 𝓕 μ H (s:ℝ) u
  let δ := (t:ℝ)-(s:ℝ)
  have hδ : 0≤δ := sub_nonneg.mpr (by exact_mod_cast hst)
  have hδ1 : δ≤1 := by
    have ht : (t:ℝ)≤(H:ℝ) := by exact_mod_cast htH
    dsimp [δ]
    linarith [s.2]
  have hp : δ^8≤δ^2 := pow_le_pow_of_le_one hδ hδ1 (by norm_num : (2:ℕ)≤8)
  have he : (fun ω => I.integral (stop 𝓕 μ H (t:ℝ) u) ω-
      I.integral (stop 𝓕 μ H (s:ℝ) u) ω)=ᵐ[μ] I.integral w := by
    rw [show I.integral w=I.integral (stop 𝓕 μ H (t:ℝ) u)-I.integral (stop 𝓕 μ H (s:ℝ) u)
      from map_sub I.integral _ _]
    exact (Lp.coeFn_sub _ _).symm
  have hbr := StoppedBoundedBracket.increment_bound 𝓕 μ H u hK hu s t hst
  have hpow : (∫⁻ ω,(∫⁻ r,ENNReal.ofReal (‖w (r,ω)‖^2) ∂timeMeasure H)^8 ∂μ)≤
      (ENNReal.ofReal (K*δ))^8 := by
    have hh := lintegral_mono_ae (hbr.mono (fun ω hω => pow_le_pow_left₀ (by simp) hω 8))
    simpa only [lintegral_const,measure_univ,mul_one] using hh
  calc
    _ = ∫⁻ ω,ENNReal.ofReal (‖I.integral w ω‖^16) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
    _ ≤ _ := hBDG w
    _ ≤ (B:ENNReal)*(ENNReal.ofReal (K*δ))^8 := mul_le_mul_right hpow _
    _ = ENNReal.ofReal ((B:ℝ)*K^8*δ^8) := by
      rw [←ENNReal.ofReal_pow (mul_nonneg hK hδ),
        show (B:ENNReal)=ENNReal.ofReal (B:ℝ) by simp]
      have hm : ENNReal.ofReal (B:ℝ)*ENNReal.ofReal ((K*δ)^8)=
          ENNReal.ofReal ((B:ℝ)*(K*δ)^8) := (ENNReal.ofReal_mul B.2).symm
      rw [hm]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp (by positivity))

theorem increment (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (u : Process (E := C) 𝓕 μ H) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H, ‖u p‖^2≤K)
    (s t : ℝ≥0) (hsH : s≤H) (htH : t≤H) :
    (∫⁻ ω,ENNReal.ofReal (‖I.integral (stop 𝓕 μ H s u) ω-
      I.integral (stop 𝓕 μ H t u) ω‖^16) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*K^8*((s:ℝ)-(t:ℝ))^2) := by
  rcases le_total s t with hst | hts
  · have he := ordered_increment 𝓕 μ H hH I B hBDG u hK hu s t hst htH
    simpa only [norm_sub_rev,sub_sq_comm] using he
  · exact ordered_increment 𝓕 μ H hH I B hBDG u hK hu t s hts hsH

end SHE.BoundedStoppedMoments
