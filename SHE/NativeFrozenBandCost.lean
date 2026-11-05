module
public import SHE.GaussianSeparatedBand
public import SHE.NativeGaussianCircleMass

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeFrozenBandCost
open Real ScalarHeatBandEnvelope

theorem square_min {a:ℝ}(ha:0≤a):(min 1 a)^2=min 1 (a^2):=by
  by_cases h:a≤1
  · have hs:a^2≤1:=by nlinarith
    rw [min_eq_right h,min_eq_right hs]
  · have h':1≤a:=le_of_not_ge h
    have hs:1≤a^2:=by nlinarith
    rw [min_eq_left h',min_eq_left hs,one_pow]

theorem decay_square {r v s:ℝ}(hr:0<r)(hv:0≤v):
    (decay r v (s/2))^2=min 1 ((v/r^2)^(-s)):=by
  unfold decay
  rw [square_min (Real.rpow_nonneg (div_nonneg hv (sq_nonneg r)) _),
    ←Real.rpow_mul_natCast (div_nonneg hv (sq_nonneg r)) (-(s/2)) 2]
  congr 2
  norm_num

/-- The actual native additive reserve yields radial polynomial decay
plus the explicit long-range window tail. -/
theorem kernel {κ r h d s:ℝ}(hκ:0≤κ)(hr:0<r)(hh:0≤h)(hd:0≤d):
    (decay r (κ*min d (sqrt h)/128) (s/2))^2≤
      GaussianCircleMass.decay s (κ/(128*r^2)) d+
        GaussianCircleMass.decay s (κ/(128*r^2)) (sqrt h):=by
  rw [decay_square hr (div_nonneg (mul_nonneg hκ (le_min hd (sqrt_nonneg h))) (by norm_num))]
  have hL:0≤κ/(128*r^2):=div_nonneg hκ (by positivity)
  have he (x:ℝ):κ*x/128/r^2=(κ/(128*r^2))*x:=by
    field_simp
  by_cases hds:d≤sqrt h
  · rw [min_eq_left hds,he]
    exact le_add_of_nonneg_right (GaussianCircleMass.decay_nonneg hL (sqrt_nonneg h))
  · rw [min_eq_right (le_of_not_ge hds),he]
    exact le_add_of_nonneg_left (GaussianCircleMass.decay_nonneg hL hd)

end SHE.NativeFrozenBandCost
