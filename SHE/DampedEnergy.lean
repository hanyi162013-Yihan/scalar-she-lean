module

public import SHE.HeatTrace

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory Set

/-- The exact damped power integral used by the signed heat estimate. -/
theorem damped_power_integral {Λ a : ℝ} (hΛ : 0 < Λ) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-2*Λ*t) * t ^ (a-1)) =
      ((1/2 : ℝ) ^ a * Real.Gamma a) * Λ ^ (-a) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi ha (mul_pos (by norm_num : (0:ℝ)<2) hΛ)
  have hi : (fun t : ℝ => Real.exp (-2*Λ*t) * t ^ (a-1)) =
      (fun t : ℝ => t ^ (a-1) * Real.exp (-(2*Λ*t))) := by
    funext t
    rw [show -2*Λ*t = -(2*Λ*t) by ring, mul_comm]
  rw [hi, hh]
  have hrecip : 1/(2*Λ) = (1/2:ℝ) * (1/Λ) := by field_simp
  rw [hrecip, Real.mul_rpow (by positivity) (by positivity)]
  have hinv : (1/Λ) ^ a = Λ ^ (-a) := by rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  rw [hinv]
  ring

theorem damped_power_integrable {Λ a : ℝ} (hΛ : 0 < Λ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*Λ*t) * t ^ (a-1)) (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=a-1) (b:=2*Λ)
    (by linarith) (by norm_num) (by positivity)
  simp only [Real.rpow_one] at hh
  apply hh.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show -(2*Λ)*t = -2*Λ*t by ring, mul_comm]

def dampingPowerConstant (a : ℝ) := (1/2 : ℝ) ^ a * Real.Gamma a

theorem dampingPowerConstant_pos {a : ℝ} (ha : 0 < a) : 0 < dampingPowerConstant a := by
  exact mul_pos (by positivity) (Real.Gamma_pos_of_pos ha)

def signedDampingConstant (ρ : ℝ) :=
  dampingPowerConstant (1/2) + dampingPowerConstant (1/2-ρ) + 1

/-- Integration of the full two singular powers and the large-time
contractive tail. This gives exactly Λ^(ρ−1/2), with no endpoint loss. -/
theorem signed_heat_majorant_integral {Λ ρ : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1/2) :
    (∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) *
      (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) ≤
        signedDampingConstant ρ * Λ ^ (ρ-1/2) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have h1 := damped_power_integrable hΛpos (by norm_num : (0:ℝ)<1/2)
  have h2 := damped_power_integrable hΛpos (by linarith : 0<1/2-ρ)
  have h3 := damped_power_integrable hΛpos (by norm_num : (0:ℝ)<1)
  norm_num only [sub_self, Real.rpow_zero, mul_one, show (1/2:ℝ)-1 = -(1/2:ℝ) by norm_num,
    show (1/2:ℝ)-ρ-1 = -(1/2:ℝ)-ρ by ring] at h1 h2 h3
  have hval1 : (∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) * (Λ ^ ρ * t ^ (-(1/2:ℝ)))) =
      dampingPowerConstant (1/2) * Λ ^ (ρ-1/2) := by
    rw [show (fun t : ℝ => Real.exp (-2*Λ*t) * (Λ ^ ρ * t ^ (-(1/2:ℝ)))) =
      (fun t : ℝ => Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ ((1/2:ℝ)-1))) by funext t; norm_num; ring,
      integral_const_mul, damped_power_integral hΛpos (by norm_num : (0:ℝ)<1/2)]
    dsimp [dampingPowerConstant]
    have hp : Λ ^ ρ * Λ ^ (-(1/2:ℝ)) = Λ ^ (ρ-1/2) := by
      rw [← Real.rpow_add hΛpos]
      congr 1
    calc
      _ = (((1/2:ℝ) ^ (1/2:ℝ)) * Real.Gamma (1/2)) * (Λ ^ ρ * Λ ^ (-(1/2:ℝ))) := by ring
      _ = _ := by rw [hp]
  have hval2 : (∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)-ρ)) =
      dampingPowerConstant (1/2-ρ) * Λ ^ (ρ-1/2) := by
    have hh := damped_power_integral hΛpos (by linarith : 0<1/2-ρ)
    have he : (1/2:ℝ)-ρ-1 = -(1/2:ℝ)-ρ := by ring
    have he' : -((1/2:ℝ)-ρ) = ρ-1/2 := by ring
    simpa only [he, he', dampingPowerConstant] using hh
  have hval3 : (∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) * (Λ ^ ρ+1)) =
      (1/2:ℝ) * (Λ ^ (ρ-1) + Λ ^ (-1:ℝ)) := by
    rw [integral_mul_const]
    have hh := damped_power_integral hΛpos (by norm_num : (0:ℝ)<1)
    norm_num only [sub_self, Real.rpow_zero, mul_one, Real.rpow_one, Real.Gamma_one] at hh
    rw [hh, show ρ-1 = ρ+(-1) by ring, Real.rpow_add hΛpos]
    ring
  have heq : (fun t : ℝ => Real.exp (-2*Λ*t) *
      (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) =
      (fun t : ℝ => Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ))) +
        Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)-ρ) + Real.exp (-2*Λ*t) * (Λ ^ ρ+1)) := by
    funext t
    ring
  have h1' : IntegrableOn (fun t : ℝ => Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)))) (Ioi 0) := h1.const_mul _
  have h3' : IntegrableOn (fun t : ℝ => Real.exp (-2*Λ*t) * (Λ ^ ρ+1)) (Ioi 0) := h3.mul_const _
  have h12 : IntegrableOn (fun t : ℝ => Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ))) +
      Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)-ρ)) (Ioi 0) := h1'.add h2
  rw [heq, integral_add h12 h3', integral_add h1' h2]
  have hval1' : (∫ t in Ioi (0:ℝ), Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)))) =
      dampingPowerConstant (1/2) * Λ ^ (ρ-1/2) := by
    convert hval1 using 1
    congr 1
    funext t
    ring
  rw [hval1', hval2, hval3]
  have hp1 : Λ ^ (ρ-1) ≤ Λ ^ (ρ-1/2) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  have hp2 : Λ ^ (-1:ℝ) ≤ Λ ^ (ρ-1/2) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  dsimp [signedDampingConstant]
  nlinarith only [hp1,hp2]

theorem signed_heat_majorant_integrable {Λ ρ : ℝ}
    (hΛ : 0 < Λ) (hρ : ρ < 1/2) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*Λ*t) *
      (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) (Ioi 0) := by
  have h1 := (damped_power_integrable hΛ (by norm_num : (0:ℝ)<1/2)).const_mul (Λ ^ ρ)
  have h2 := damped_power_integrable hΛ (by linarith : 0<1/2-ρ)
  have h3 := (damped_power_integrable hΛ (by norm_num : (0:ℝ)<1)).mul_const (Λ ^ ρ+1)
  have he₁ : (1/2:ℝ)-1 = -(1/2:ℝ) := by norm_num
  have he₂ : (1/2:ℝ)-ρ-1 = -(1/2:ℝ)-ρ := by ring
  simp only [he₁] at h1
  simp only [he₂] at h2
  simp only [sub_self, Real.rpow_zero, mul_one] at h3
  have h1' : IntegrableOn (fun t : ℝ => Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)))) (Ioi 0) := h1
  have h12 : IntegrableOn (fun t : ℝ => Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ))) +
      Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)-ρ)) (Ioi 0) := h1'.add h2
  apply (h12.add h3).congr_fun _ measurableSet_Ioi
  intro t ht
  change Λ ^ ρ * (Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ))) +
      Real.exp (-2*Λ*t) * t ^ (-(1/2:ℝ)-ρ) + Real.exp (-2*Λ*t) * (Λ ^ ρ+1) =
    Real.exp (-2*Λ*t) * (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))
  ring

/-- A genuine measurable square-energy profile satisfying the signed
heat majorant is integrable against the infinite damped time measure.
The result includes the large-time contribution. -/
theorem damped_signed_energy_of_heat_bound {Λ ρ C F : ℝ} {E : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1/2) (hC : 0 ≤ C)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi 0)))
    (hE0 : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ E t)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), E t ≤ C * F ^ (2:ℕ) *
      (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) :
    IntegrableOn (fun t => Real.exp (-2*Λ*t) * E t) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) * E t) ≤
        (C * F ^ (2:ℕ) * signedDampingConstant ρ) * Λ ^ (ρ-1/2) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hmajor := signed_heat_majorant_integrable hΛ0 hρ1
  have hCF : 0 ≤ C * F ^ (2:ℕ) := mul_nonneg hC (sq_nonneg F)
  have hm : AEStronglyMeasurable (fun t => Real.exp (-2*Λ*t) * E t) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-2*Λ*t))).aestronglyMeasurable.mul hE
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi 0),
      Real.exp (-2*Λ*t) * E t ≤ C * F ^ (2:ℕ) * (Real.exp (-2*Λ*t) *
        (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) := by
    filter_upwards [hbound] with t ht
    simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
  have hi : IntegrableOn (fun t => Real.exp (-2*Λ*t) * E t) (Ioi 0) := by
    apply (hmajor.const_mul (C * F ^ (2:ℕ))).mono' hm
    filter_upwards [hpoint, hE0] with t ht ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le ht0)]
    exact ht
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), C * F ^ (2:ℕ) * (Real.exp (-2*Λ*t) *
      (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) :=
      integral_mono_ae hi (hmajor.const_mul _) hpoint
    _ = C * F ^ (2:ℕ) * ∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) *
      (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1)) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (signed_heat_majorant_integral hΛ hρ0 hρ1) hCF
      simpa only [mul_assoc] using hh

end SHE
