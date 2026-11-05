module

public import SHE.DampedEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory Set

/-- Exact infinite-time annular integral. The cutoff exponential is
kept throughout, including both time endpoints. -/
theorem annular_time_integral {c ν γ : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hγ : 0 < γ) :
    (∫ t in Ioi (0:ℝ), t ^ (γ-1) * Real.exp (-c*ν^2*Real.sqrt t)) =
      (2 * c ^ (-2*γ) * Real.Gamma (2*γ)) * ν ^ (-4*γ) := by
  have hb : 0 < c*ν^2 := mul_pos hc (sq_pos_of_pos hν)
  have hh := integral_rpow_mul_exp_neg_mul_rpow
    (p:=(1/2:ℝ)) (q:=γ-1) (b:=c*ν^2) (by norm_num) (by linarith) hb
  simp only [show -((γ-1)+1)/(1/2:ℝ) = -2*γ by ring,
    show ((γ-1)+1)/(1/2:ℝ) = 2*γ by ring,
    show (1:ℝ)/(1/2) = 2 by norm_num, ← Real.sqrt_eq_rpow] at hh
  rw [show (fun t : ℝ => t ^ (γ-1) * Real.exp (-c*ν^2*Real.sqrt t)) =
    (fun t : ℝ => t ^ (γ-1) * Real.exp (-(c*ν^2)*Real.sqrt t)) by
      funext t; simp only [neg_mul], hh]
  rw [Real.mul_rpow hc.le (sq_nonneg ν), ← Real.rpow_natCast_mul hν.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-2*γ) = -4*γ by ring]
  ring

theorem annular_time_integrable {c ν γ : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hγ : 0 < γ) :
    IntegrableOn (fun t : ℝ => t ^ (γ-1) * Real.exp (-c*ν^2*Real.sqrt t)) (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p:=(1/2:ℝ)) (s:=γ-1) (b:=c*ν^2) (by linarith) (by norm_num)
    (mul_pos hc (sq_pos_of_pos hν))
  simpa only [← Real.sqrt_eq_rpow, neg_mul] using hh

/-- The finite terminal integral is controlled by the full Gamma mass,
with the precise state-frequency power ν^(-4γ). -/
theorem annular_time_integral_le {c ν γ h : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hγ : 0 < γ) :
    (∫ t in Ioc (0:ℝ) h, t ^ (γ-1) * Real.exp (-c*ν^2*Real.sqrt t)) ≤
      (2 * c ^ (-2*γ) * Real.Gamma (2*γ)) * ν ^ (-4*γ) := by
  rw [← annular_time_integral hc hν hγ]
  apply setIntegral_mono_set (annular_time_integrable hc hν hγ)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall fun t ht => ht.1

/-- Squared annular amplitudes contribute their exact frequency
power before any stochastic isometry is applied. -/
theorem annular_scaled_energy {c ν γ a h : ℝ}
    (hc : 0<c) (hν : 0<ν) (hγ : 0<γ) :
    (∫ t in Ioc (0:ℝ) h, ν^(2*a)*t^(γ-1)*Real.exp (-c*ν^2*Real.sqrt t)) ≤
      (2*c^(-2*γ)*Real.Gamma (2*γ))*ν^(2*a-4*γ) := by
  have he : (fun t : ℝ => ν^(2*a)*t^(γ-1)*Real.exp (-c*ν^2*Real.sqrt t)) =
      (fun t : ℝ => ν^(2*a)*(t^(γ-1)*Real.exp (-c*ν^2*Real.sqrt t))) := by funext t; ring
  rw [he,integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left (annular_time_integral_le (h:=h) hc hν hγ)
    (Real.rpow_nonneg hν.le (2*a))
  calc
    _ ≤ ν^(2*a)*((2*c^(-2*γ)*Real.Gamma (2*γ))*ν^(-4*γ)) := hb
    _ = (2*c^(-2*γ)*Real.Gamma (2*γ))*(ν^(2*a)*ν^(-4*γ)) := by ring
    _ = _ := by rw [← Real.rpow_add hν,show 2*a+(-4*γ)=2*a-4*γ by ring]

/-- The nonlinear adapted Itô row has the printed squared state-band
power ν^(-2β-4ρ), derived from the genuine annular integral. -/
theorem annular_nonlinear_energy {c ν β ρ h : ℝ}
    (hc : 0<c) (hν : 0<ν) (hρ : -(1/2:ℝ)<ρ) :
    (∫ t in Ioc (0:ℝ) h,
      ν^(2-2*β)*t^(ρ-1/2)*Real.exp (-c*ν^2*Real.sqrt t)) ≤
      (2*c^(-1-2*ρ)*Real.Gamma (1+2*ρ))*ν^(-2*β-4*ρ) := by
  have hh := annular_scaled_energy (a:=1-β) (γ:=ρ+1/2) (h:=h) hc hν (by linarith)
  have h₁ : (2:ℝ)*(1-β)=2-2*β := by ring
  have h₂ : ρ+1/2-1=ρ-1/2 := by ring
  have h₃ : -(2:ℝ)*(ρ+1/2) = -1-2*ρ := by ring
  have h₄ : (2:ℝ)*(ρ+1/2)=1+2*ρ := by ring
  have h₅ : (2:ℝ)-2*β-4*(ρ+1/2) = -2*β-4*ρ := by ring
  simpa only [h₅,h₁,h₂,h₃,h₄] using hh

end SHE
