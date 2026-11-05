module
public import SHE.DefectGapFrequency
public import SHE.StateBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.DefectGapBandCost
open Set MeasureTheory Real
open scoped BigOperators

def clock (Λ ρ:ℝ)(k:ℕ):ℝ:=((1+k:ℕ):ℝ)^2*(4+2/ρ+log (2+Λ))

theorem clock_nonneg {Λ ρ:ℝ}(hΛ:0≤Λ)(hρ:0<ρ)(k:ℕ):0≤clock Λ ρ k:=by
  have hl:0≤log (2+Λ):=log_nonneg (by linarith)
  unfold clock
  positivity

theorem clock_le {Λ h ρ:ℝ}(hΛ:0≤Λ)(hh1:h≤1)(hh:0≤h)(k:ℕ):
    DefectGapKernelMass.cost Λ ρ h k≤clock Λ ρ k:=by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have harg:2+Λ*h≤2+Λ:=by nlinarith only [mul_le_mul_of_nonneg_left hh1 hΛ]
  have hl:=log_le_log (by positivity:0<2+Λ*h) harg
  linarith only [hl]

/-- The actual first-defect convolution cost retains the root band
amplitude and loses only an arbitrarily small frequency power. The
remaining clock factor is common to every physical window in [0,1]. -/
theorem cost_le (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h A β η ν:ℝ}
    (hell:0<ell)(hΛ:0≤Λ)(hρ:0<ρ)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)
    (hh:0≤h)(hh1:h≤1)(hA:0≤A)(hη:0<η)(hν:1≤ν):
    DefectGapMixture.cost P ell C Λ ρ h (A*ν^(-β)) ν k≤
      (A*DefectGapFrequency.constant P ell C k 1 η*(2:ℝ)^η)*
        ν^(-(β-η))*clock Λ ρ k:=by
  have hνp:0<ν:=zero_lt_one.trans_le hν
  have hAmp:0≤A*ν^(-β):=mul_nonneg hA (rpow_nonneg hνp.le _)
  have hm:=DefectGapFrequency.mass_le P hell C hC k hAmp hη hh hh1 (zero_le_one.trans hν)
  rw [DefectGapFrequency.constant_amplitude] at hm
  have hK:=DefectGapFrequency.constant_nonneg P hell C hC k (by norm_num:0≤(1:ℝ)) hη
  have hweight:ν^(-β)*(1+ν)^η≤(2:ℝ)^η*ν^(-(β-η)):=by
    have hp:(1+ν)^η≤(2:ℝ)^η*ν^η:=by
      have hh:=rpow_le_rpow (by positivity:0≤1+ν) (show 1+ν≤2*ν by linarith) hη.le
      rwa [mul_rpow (by norm_num:0≤(2:ℝ)) hνp.le] at hh
    calc
      _≤ν^(-β)*((2:ℝ)^η*ν^η):=mul_le_mul_of_nonneg_left hp (rpow_nonneg hνp.le _)
      _=(2:ℝ)^η*(ν^(-β)*ν^η):=by ring
      _=_:=by rw [←rpow_add hνp];congr 2;ring
  have hm':DefectGapDensity.mass P ell C k h (A*ν^(-β)) ν≤
      (A*DefectGapFrequency.constant P ell C k 1 η*(2:ℝ)^η)*ν^(-(β-η)):=by
    apply hm.trans
    have hw:=mul_le_mul_of_nonneg_left hweight (mul_nonneg hA hK)
    convert! hw using 1 <;> ring
  unfold DefectGapMixture.cost
  exact mul_le_mul hm' (clock_le hΛ hh1 hh k)
    (by unfold DefectGapKernelMass.cost;have :=log_nonneg (by nlinarith [mul_nonneg hΛ hh]:1≤2+Λ*h);positivity)
    (mul_nonneg (mul_nonneg (mul_nonneg hA hK) (rpow_nonneg (by norm_num) _)) (rpow_nonneg hνp.le _))
end SHE.DefectGapBandCost
