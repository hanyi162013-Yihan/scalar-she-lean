module

public import SHE.MovingPastEnergy
public import SHE.FiniteMomentFractional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.MovingPastFractional
open Set MeasureTheory
open scoped ENNReal

/-- The power is taken on the physical window before zero extension.
This convention also treats exponent zero correctly. -/
def powerWindow (T χ : ℝ) (F : ℝ→ℝ≥0∞) : ℝ→ℝ≥0∞ :=
  (Ioc (0:ℝ) T).indicator (fun r=>F r^χ)

theorem powerWindow_measurable {F : ℝ→ℝ≥0∞} (hF : Measurable F) (T χ : ℝ) :
    Measurable (powerWindow T χ F) := (hF.pow_const χ).indicator measurableSet_Ioc

/-- Finite-horizon fractional energy averaging retains the true global
energy, with the exact horizon power; no uniform-in-time cap is used. -/
theorem powerWindow_mass {F : ℝ→ℝ≥0∞} (hF : Measurable F)
    {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) (T : ℝ) :
    (∫⁻ r,powerWindow T χ F r)≤
      (∫⁻ r in Ioc (0:ℝ) T,F r)^χ*(ENNReal.ofReal T)^(1-χ) := by
  rw [powerWindow,lintegral_indicator measurableSet_Ioc]
  have hh:=FiniteMomentFractional.lintegral_fraction_mass
    (μ:=volume.restrict (Ioc (0:ℝ) T)) hF.aemeasurable hχ hχ1
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero] using hh

/-- A true current input at v+s may share all randomness with the old
past. Translating and integrating the moving past counts its global
fractional energy once, including the terminal physical-window cut. -/
theorem current_window (K F : ℝ→ℝ≥0∞) (hK : Measurable K) (hF : Measurable F)
    {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) (T h : ℝ) :
    (∫⁻ v in Ioc (0:ℝ) T,∫⁻ s in Ioc (0:ℝ) h,K s*powerWindow T χ F (v+s))≤
      (∫⁻ s in Ioc (0:ℝ) h,K s)*
        ((∫⁻ r in Ioc (0:ℝ) T,F r)^χ*(ENNReal.ofReal T)^(1-χ)) := by
  exact (MovingPastEnergy.window_bound K (powerWindow T χ F) hK
    (powerWindow_measurable hF T χ) T h).trans
      (by gcongr;exact powerWindow_mass hF hχ hχ1 T)

/-- The past-profile slot has the same exact global fractional-energy
mass, with the independent relative-time kernel integrated only once. -/
theorem past_window (K F : ℝ→ℝ≥0∞) (hK : Measurable K) (hF : Measurable F)
    {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) (T h : ℝ) :
    (∫⁻ v in Ioc (0:ℝ) T,∫⁻ s in Ioc (0:ℝ) h,K s*(F v)^χ)≤
      (∫⁻ s in Ioc (0:ℝ) h,K s)*
        ((∫⁻ r in Ioc (0:ℝ) T,F r)^χ*(ENNReal.ofReal T)^(1-χ)) := by
  have he (v : ℝ) : (∫⁻ s in Ioc (0:ℝ) h,K s*(F v)^χ)=
      (∫⁻ s in Ioc (0:ℝ) h,K s)*(F v)^χ:=lintegral_mul_const _ hK
  simp_rw [he]
  rw [lintegral_const_mul _ (hF.pow_const χ)]
  gcongr
  have hh:=FiniteMomentFractional.lintegral_fraction_mass (μ:=volume.restrict (Ioc (0:ℝ) T)) hF.aemeasurable hχ hχ1
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero] using hh

end SHE.MovingPastFractional
