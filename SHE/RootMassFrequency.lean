module

public import SHE.RootConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace SHE
open Set MeasureTheory Real

/-- Genuine clipped root mass grows more slowly than every positive
frequency power, uniformly on the FULL fixed time interval [0,1]. -/
theorem rootMass_frequency_bound {ν t ε : ℝ} (hν : 0≤ν) (ht : 0≤t) (ht1 : t≤1) (hε : 0<ε) :
    rootMass ν t≤(4+1/ε)*(1+ν)^(4*ε) := by
  by_cases hzero : ν=0
  · subst ν
    simp only [rootMass,rootKernel,zero_mul,min_eq_right zero_le_one,mul_zero,intervalIntegral.integral_zero,add_zero,one_rpow,mul_one]
    positivity
  have hνp : 0<ν:=lt_of_le_of_ne hν (Ne.symm hzero)
  have hC : 0≤4+1/ε:=by positivity
  have hbase : 1≤1+ν:=by linarith
  have hpow : 1≤(1+ν)^(4*ε):=one_le_rpow hbase (by positivity)
  by_cases hcut : t≤ν^(-(4:ℝ))
  · have hm : rootMass ν t≤4:=(rootMass_mono hν ht hcut).trans_eq (root_mass_at_cutoff hνp)
    apply hm.trans
    have hc : (4:ℝ)≤4+1/ε:=le_add_of_nonneg_right (div_nonneg zero_le_one hε.le)
    exact hc.trans (le_mul_of_one_le_right hC hpow)
  · have hmain:=root_mass_le_rescaled_power hνp hε (le_of_not_ge hcut)
    have htp : t^ε≤1:=rpow_le_one ht ht1 hε.le
    have hνpow : ν^(4*ε)≤(1+ν)^(4*ε):=rpow_le_rpow hν (by linarith) (by positivity)
    exact hmain.trans ((mul_le_of_le_one_right (mul_nonneg hC (rpow_nonneg hν _)) htp).trans
      (mul_le_mul_of_nonneg_left hνpow hC))

/-- The actual scalar rescaling of the root frequency is retained in a
constant independent of that frequency. -/
theorem rootMass_scaled_frequency_bound {ν c t ε : ℝ} (hν : 0≤ν) (hc : 0≤c)
    (ht : 0≤t) (ht1 : t≤1) (hε : 0<ε) :
    rootMass (ν*c) t≤((4+1/ε)*(1+c)^(4*ε))*(1+ν)^(4*ε) := by
  have hh:=rootMass_frequency_bound (mul_nonneg hν hc) ht ht1 hε
  have hbase : 1+ν*c≤(1+c)*(1+ν):=by nlinarith
  have hpow:=rpow_le_rpow (show 0≤1+ν*c by positivity) hbase (show 0≤4*ε by positivity)
  apply (hh.trans (mul_le_mul_of_nonneg_left hpow (by positivity))).trans_eq
  rw [mul_rpow (by positivity : 0≤1+c) (by positivity : 0≤1+ν)]
  ring
end SHE
