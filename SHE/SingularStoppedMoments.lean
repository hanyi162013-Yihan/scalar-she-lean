module

public import SHE.SingularStoppedBracket
public import SHE.StandardTerminalBDG

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.SingularStoppedMoments
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (I : StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)

/-- The actual fixed-target inverse-root singularity yields fourth-power
sixteenth-moment increments of the original stopped Hilbert integral. -/
theorem ordered_increment (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (u : Process (E:=C) 𝓕 μ H) (b : ℝ≥0) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p.1≤b → ‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
    (s t : ℝ≥0) (hst : s≤t) (htb : t≤b) (htH : t≤H) :
    (∫⁻ ω,ENNReal.ofReal (‖I.integral (stop 𝓕 μ H t u) ω-
      I.integral (stop 𝓕 μ H s u) ω‖^16) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*(2*K)^8*((t:ℝ)-(s:ℝ))^4) := by
  let w := stop 𝓕 μ H (t:ℝ) u-stop 𝓕 μ H (s:ℝ) u
  let δ := (t:ℝ)-(s:ℝ)
  have hδ : 0≤δ := sub_nonneg.mpr (by exact_mod_cast hst)
  have he : (fun ω => I.integral (stop 𝓕 μ H (t:ℝ) u) ω-
      I.integral (stop 𝓕 μ H (s:ℝ) u) ω)=ᵐ[μ] I.integral w := by
    rw [show I.integral w=I.integral (stop 𝓕 μ H (t:ℝ) u)-I.integral (stop 𝓕 μ H (s:ℝ) u)
      from map_sub I.integral _ _]
    exact (Lp.coeFn_sub _ _).symm
  have hbr := SingularStoppedBracket.increment_bound 𝓕 μ H u b hK hu s t hst htb htH
  have hpow : (∫⁻ ω,(∫⁻ r,ENNReal.ofReal (‖w (r,ω)‖^2) ∂timeMeasure H)^8 ∂μ)≤
      (ENNReal.ofReal (2*K*δ^(1/2:ℝ)))^8 := by
    have hh := lintegral_mono_ae (hbr.mono (fun ω hω => pow_le_pow_left₀ (by simp) hω 8))
    simpa only [lintegral_const,measure_univ,mul_one] using hh
  calc
    _ = ∫⁻ ω,ENNReal.ofReal (‖I.integral w ω‖^16) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
    _ ≤ _ := hBDG w
    _ ≤ (B:ENNReal)*(ENNReal.ofReal (2*K*δ^(1/2:ℝ)))^8 := mul_le_mul_right hpow _
    _ = ENNReal.ofReal ((B:ℝ)*(2*K)^8*δ^4) := by
      rw [←ENNReal.ofReal_pow (by positivity : 0≤2*K*δ^(1/2:ℝ)),
        show (B:ENNReal)=ENNReal.ofReal (B:ℝ) by simp]
      rw [show ENNReal.ofReal (B:ℝ)*ENNReal.ofReal ((2*K*δ^(1/2:ℝ))^8)=
        ENNReal.ofReal ((B:ℝ)*(2*K*δ^(1/2:ℝ))^8) from (ENNReal.ofReal_mul B.2).symm]
      congr 1
      have hp : (δ^(1/2:ℝ))^8=δ^4 := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hδ]
        norm_num
      rw [mul_pow,hp]
      ring

theorem increment (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (u : Process (E:=C) 𝓕 μ H) (b : ℝ≥0) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p.1≤b → ‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
    (s t : ℝ≥0) (hsb : s≤b) (htb : t≤b) (hbH : b≤H) :
    (∫⁻ ω,ENNReal.ofReal (‖I.integral (stop 𝓕 μ H s u) ω-
      I.integral (stop 𝓕 μ H t u) ω‖^16) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*(2*K)^8*((s:ℝ)-(t:ℝ))^4) := by
  rcases le_total s t with hst | hts
  · have he := ordered_increment 𝓕 μ H I B hBDG u b hK hu s t hst htb (htb.trans hbH)
    have hswap : ((t:ℝ)-(s:ℝ))^4=((s:ℝ)-(t:ℝ))^4 := by ring
    simpa only [norm_sub_rev,hswap] using he
  · exact ordered_increment 𝓕 μ H I B hBDG u b hK hu t s hts hsb (hsb.trans hbH)

end SHE.SingularStoppedMoments
