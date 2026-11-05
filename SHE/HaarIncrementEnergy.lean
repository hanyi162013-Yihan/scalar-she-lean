module

public import SHE.TimeCausalSplit
public import SHE.HaarKernelTimeIncrement
public import SHE.HaarFixedTerminalEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarIncrementEnergy
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar HaarIntegrandEnergy
open scoped NNReal ENNReal
local instance haarIncrementEnergy_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def oldConstant (M : ℝ) : ℝ := (2:ℝ)^(3/4:ℝ)*singleConstant M

theorem oldConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ oldConstant M :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (singleConstant_nonneg hM)

def energy {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 → EllipticField ell M)
    (s t r : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(r:ℝ),f r)-
    RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(r:ℝ),f r)‖^2)

theorem old_energy_bound {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {h s t : ℝ≥0} (hh : (h:ℝ) ≤ 1) (hst : s ≤ t) (hth : t ≤ h)
    (f : ℝ≥0 → EllipticField ell M) :
    (∫⁻ r,energy hell f s t r ∂timeMeasure s) ≤
      ENNReal.ofReal (oldConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)*(4*(s:ℝ)^(1/4:ℝ))) := by
  have hδ : 0 ≤ (t:ℝ)-(s:ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
  calc
    _ ≤ ∫⁻ r,ENNReal.ofReal (oldConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ))*
        ENNReal.ofReal (((s:ℝ)-(r:ℝ))^(-(3/4:ℝ))) ∂timeMeasure s := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem s,(timeMeasure s).ae_ne s] with r hr hrs
      have hrs' : r < s := lt_of_le_of_ne hr.2 hrs
      have hτ : 0 < (s:ℝ)-(r:ℝ) := sub_pos.mpr (by exact_mod_cast hrs')
      have hτ1 : (s:ℝ)-(r:ℝ) ≤ 1 := by
        have ht' : (t:ℝ) ≤ (h:ℝ) := by exact_mod_cast hth
        have hs' : (s:ℝ) ≤ (t:ℝ) := by exact_mod_cast hst
        linarith [r.2]
      have hb := HaarKernelTimeIncrement.real_kernel_increment_rate hell hτ hτ1 hδ (f r)
      rw [show ((s:ℝ)-(r:ℝ))+((t:ℝ)-(s:ℝ))=(t:ℝ)-(r:ℝ) by ring] at hb
      change ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(r:ℝ),f r)-
        RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(r:ℝ),f r)‖^2) ≤ _
      rw [← ENNReal.ofReal_mul (mul_nonneg (oldConstant_nonneg hM) (Real.rpow_nonneg hδ _))]
      exact ENNReal.ofReal_le_ofReal hb
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,causal_rpow_mass (by norm_num : (-1:ℝ) < -(3/4:ℝ))]
      norm_num only [show -(3/4:ℝ)+1=1/4 by norm_num]
      rw [← ENNReal.ofReal_mul (mul_nonneg (oldConstant_nonneg hM) (Real.rpow_nonneg hδ _))]
      congr 1
      ring

theorem new_energy_bound {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {h s t : ℝ≥0} (hh : (h:ℝ) ≤ 1) (hst : s ≤ t) (hth : t ≤ h)
    (f : ℝ≥0 → EllipticField ell M) :
    (∫⁻ r,energy hell f s t r ∂intervalTimeMeasure s t) ≤
      ENNReal.ofReal (singleConstant M*(2*((t:ℝ)-(s:ℝ))^(1/2:ℝ))) := by
  calc
    _ ≤ ∫⁻ r,ENNReal.ofReal (singleConstant M)*
        ENNReal.ofReal (((t:ℝ)-(r:ℝ))^(-(1/2:ℝ))) ∂intervalTimeMeasure s t := by
      apply lintegral_mono_ae
      filter_upwards [intervalTimeMeasure_ae_mem s hth] with r hr
      have hz : (s:ℝ)-(r:ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hr.1.le)
      unfold energy
      rw [HaarKernelApproximation.kernel_zero hell hz,sub_zero,
        ← ENNReal.ofReal_mul (singleConstant_nonneg hM)]
      exact ENNReal.ofReal_le_ofReal (HaarFixedTerminalEnergy.kernel_causal_power_bound hell hh hth hr.2 (f r))
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,interval_causal_rpow_mass
        (by norm_num : (-1:ℝ) < -(1/2:ℝ)) hst]
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      rw [← ENNReal.ofReal_mul (singleConstant_nonneg hM)]
      congr 1
      ring

def incrementConstant (M : ℝ) : ℝ := 4*oldConstant M+2*singleConstant M

theorem incrementConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ incrementConstant M :=
  add_nonneg (mul_nonneg (by norm_num) (oldConstant_nonneg hM))
    (mul_nonneg (by norm_num) (singleConstant_nonneg hM))

/-- Uniform PATHWISE quadratic energy of the actual stochastic
convolution increment. Both old noise and the newly entered interval are
retained, and every coefficient field may depend arbitrarily on time. -/
theorem total_increment_energy {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {h s t : ℝ≥0} (hh : (h:ℝ) ≤ 1) (hst : s ≤ t) (hth : t ≤ h)
    (f : ℝ≥0 → EllipticField ell M) :
    (∫⁻ r,energy hell f s t r ∂timeMeasure h) ≤
      ENNReal.ofReal (incrementConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)) := by
  have hst' : (s:ℝ) ≤ (t:ℝ) := by exact_mod_cast hst
  have hth' : (t:ℝ) ≤ (h:ℝ) := by exact_mod_cast hth
  have hδ : 0 ≤ (t:ℝ)-(s:ℝ) := sub_nonneg.mpr hst'
  have hδ1 : (t:ℝ)-(s:ℝ) ≤ 1 := by linarith [s.2]
  have hsz : ∀ r,t < r → energy hell f s t r=0 := by
    intro r hr
    have htr : (t:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr.le
    rw [energy,HaarKernelApproximation.kernel_zero hell (sub_nonpos.mpr htr),
      HaarKernelApproximation.kernel_zero hell (sub_nonpos.mpr (hst'.trans htr)),sub_self,norm_zero]
    simp
  rw [causal_lintegral_of_zero hth _ hsz,timeMeasure_split hst,lintegral_add_measure]
  have ho := old_energy_bound hell hM hh hst hth f
  have hn := new_energy_bound hell hM hh hst hth f
  have hs1 : (s:ℝ)^(1/4:ℝ) ≤ 1 := Real.rpow_le_one s.2 (hst'.trans (hth'.trans hh)) (by norm_num)
  have hd : ((t:ℝ)-(s:ℝ))^(1/2:ℝ) ≤ ((t:ℝ)-(s:ℝ))^(1/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by norm_num) (by norm_num)
  have hC := singleConstant_nonneg hM
  have hO := oldConstant_nonneg hM
  have hp : 0 ≤ ((t:ℝ)-(s:ℝ))^(1/4:ℝ) := Real.rpow_nonneg hδ _
  have ho' : oldConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)*(4*(s:ℝ)^(1/4:ℝ)) ≤
      4*oldConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ) := by
    have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs1 (by norm_num : (0:ℝ) ≤ 4))
      (mul_nonneg hO hp)
    nlinarith only [hb]
  have hn' : singleConstant M*(2*((t:ℝ)-(s:ℝ))^(1/2:ℝ)) ≤
      2*singleConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ) := by
    have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 2)) hC
    nlinarith only [hb]
  calc
    _ ≤ ENNReal.ofReal (4*oldConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ))+
        ENNReal.ofReal (2*singleConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)) :=
      add_le_add (ho.trans (ENNReal.ofReal_le_ofReal ho')) (hn.trans (ENNReal.ofReal_le_ofReal hn'))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold incrementConstant
      ring

end SHE.HaarIncrementEnergy
