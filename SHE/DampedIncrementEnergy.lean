module

public import SHE.DampedKernelIncrement

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DampedIncrementEnergy
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar HaarIntegrandEnergy
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem fixed_path_energy {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {h s : ℝ≥0} (hh : (h:ℝ) ≤ 1) (hsh : s ≤ h) (f : ℝ≥0 → EllipticField ell M) :
    (∫⁻ r,ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(r:ℝ),f r)‖^2) ∂timeMeasure h) ≤
      ENNReal.ofReal (singleConstant M*(2*(s:ℝ)^(1/2:ℝ))) := by
  simpa only [lintegral_const,measure_univ,mul_one] using
    HaarFixedTerminalEnergy.fixed_energy_bound (Measure.dirac ()) hell hM hh hsh
      (fun p : ℝ≥0 × Unit => f p.1)

def energy {Λ ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 → EllipticField ell M)
    (s t r : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (‖DampedHeatKernel.kernel Λ ell M hell ((t:ℝ)-(r:ℝ),f r)-
    DampedHeatKernel.kernel Λ ell M hell ((s:ℝ)-(r:ℝ),f r)‖^2)

def incrementConstant (Λ M : ℝ) : ℝ :=
  2*HaarIncrementEnergy.incrementConstant M+4*Λ^2*singleConstant M

theorem incrementConstant_nonneg {Λ M : ℝ} (hM : 0 ≤ M) : 0 ≤ incrementConstant Λ M := by
  unfold incrementConstant
  exact add_nonneg (by positivity [HaarIncrementEnergy.incrementConstant_nonneg hM])
    (by positivity [singleConstant_nonneg hM])

/-- The full pathwise quadratic energy of the actual damped stochastic
convolution increment, including arbitrary time-dependent coefficients. -/
theorem total_increment_energy {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    {h s t : ℝ≥0} (hh : (h:ℝ) ≤ 1) (hst : s ≤ t) (hth : t ≤ h)
    (f : ℝ≥0 → EllipticField ell M) (hf : Measurable f) :
    (∫⁻ r,energy (Λ := Λ) hell f s t r ∂timeMeasure h) ≤
      ENNReal.ofReal (incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)) := by
  let δ : ℝ := (t:ℝ)-(s:ℝ)
  have hδ : 0 ≤ δ := sub_nonneg.mpr (by exact_mod_cast hst)
  have hδ1 : δ ≤ 1 := by
    have ht' : (t:ℝ) ≤ (h:ℝ) := by exact_mod_cast hth
    dsimp only [δ]
    linarith [s.2]
  have hm (q : ℝ≥0) : Measurable (fun r : ℝ≥0 => RealHaarIntegrand.kernel ell M hell ((q:ℝ)-(r:ℝ),f r)) :=
    (RealHaarIntegrand.kernel_measurable ell M hell).comp
      ((measurable_const.sub measurable_coe_nnreal_real).prodMk hf)
  have ha : Measurable (fun r => (2:ℝ≥0∞)*HaarIncrementEnergy.energy hell f s t r) :=
    measurable_const.mul (ENNReal.continuous_ofReal.measurable.comp (((hm t).sub (hm s)).norm.pow_const 2))
  have hb : (∫⁻ r,energy (Λ := Λ) hell f s t r ∂timeMeasure h) ≤
      2*(∫⁻ r,HaarIncrementEnergy.energy hell f s t r ∂timeMeasure h)+
      ENNReal.ofReal (2*(Λ*δ)^2)*
        (∫⁻ r,ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(r:ℝ),f r)‖^2) ∂timeMeasure h) := by
    calc
      _ ≤ ∫⁻ r,(2:ℝ≥0∞)*HaarIncrementEnergy.energy hell f s t r+
          ENNReal.ofReal (2*(Λ*δ)^2)*ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(r:ℝ),f r)‖^2) ∂timeMeasure h := by
        apply lintegral_mono
        intro r
        have hh := DampedKernelIncrement.kernel_increment_sq hΛ hell hδ (f r) (τ := (s:ℝ)-(r:ℝ))
        rw [show (s:ℝ)-(r:ℝ)+δ=(t:ℝ)-(r:ℝ) by dsimp only [δ]; ring] at hh
        have he := ENNReal.ofReal_le_ofReal hh
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(Λ*δ)^2)] at he
        simpa only [energy,HaarIncrementEnergy.energy,ENNReal.ofReal_ofNat] using he
      _ = _ := by
        rw [lintegral_add_left ha,lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have ho := HaarIncrementEnergy.total_increment_energy hell hM hh hst hth f
  have hn := fixed_path_energy hell hM hh (hst.trans hth) f
  have hC := singleConstant_nonneg hM
  have hO := HaarIncrementEnergy.incrementConstant_nonneg hM
  have hs1 : (s:ℝ)^(1/2:ℝ) ≤ 1 :=
    Real.rpow_le_one s.2 (by exact_mod_cast (hst.trans hth) |>.trans (by exact_mod_cast hh)) (by norm_num)
  have hd : δ^2 ≤ δ^(1/4:ℝ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by norm_num) (by norm_num)
  have hbound : 2*(HaarIncrementEnergy.incrementConstant M*δ^(1/4:ℝ))+
      (2*(Λ*δ)^2)*(singleConstant M*(2*(s:ℝ)^(1/2:ℝ))) ≤ incrementConstant Λ M*δ^(1/4:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ 4*Λ^2*δ^2*singleConstant M)
    have h2 := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4*Λ^2*singleConstant M)
    unfold incrementConstant
    nlinarith only [h1,h2]
  calc
    _ ≤ 2*ENNReal.ofReal (HaarIncrementEnergy.incrementConstant M*δ^(1/4:ℝ))+
        ENNReal.ofReal (2*(Λ*δ)^2)*ENNReal.ofReal (singleConstant M*(2*(s:ℝ)^(1/2:ℝ))) :=
      hb.trans (add_le_add (mul_le_mul_right ho 2) (mul_le_mul_right hn _))
    _ = ENNReal.ofReal (2*(HaarIncrementEnergy.incrementConstant M*δ^(1/4:ℝ))+
        (2*(Λ*δ)^2)*(singleConstant M*(2*(s:ℝ)^(1/2:ℝ)))) := by
      have he1 : ENNReal.ofReal (2*(HaarIncrementEnergy.incrementConstant M*δ^(1/4:ℝ)))=
          2*ENNReal.ofReal (HaarIncrementEnergy.incrementConstant M*δ^(1/4:ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
      have he2 : ENNReal.ofReal ((2*(Λ*δ)^2)*(singleConstant M*(2*(s:ℝ)^(1/2:ℝ))))=
          ENNReal.ofReal (2*(Λ*δ)^2)*ENNReal.ofReal (singleConstant M*(2*(s:ℝ)^(1/2:ℝ))) :=
        ENNReal.ofReal_mul (by positivity)
      rw [ENNReal.ofReal_add (by positivity) (by positivity),he1,he2]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end SHE.DampedIncrementEnergy
