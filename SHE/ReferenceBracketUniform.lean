module

public import SHE.PastReferenceInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ReferenceBracketUniform
open Real PastReferenceBracket

/-- The genuine compatible reference bracket constant is uniform in
all current and terminal times below one, with no damping dependence. -/
theorem energy_constant_le (P:CanonicalCovariance.ProfileParameters)
    {κ h:ℝ} (hκ:κ<P.lower) (hh:0≤h) (hh1:h≤1) (θ η:ℝ):
    energyConstant P κ θ η h≤energyConstant P κ θ η 1:=by
  have hupper:0≤P.upper-κ:=by
    have hl:=P.lower_bound 0
    have hu:=P.upper_bound 0
    linarith
  have hrow:=HaarReference.rowConstant_nonneg (ell:=P.lower-κ) hupper
  have hpower:0≤ProfileVolterra.powerConstant ((P.exponent-1)/2):=
    (ProfileVolterra.powerConstant_pos (by linarith [P.exponent_pos])).le
  have hbase:0≤HaarReference.rowConstant (P.lower-κ) (P.upper-κ)*
      (2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2*
      ProfileVolterra.powerConstant ((P.exponent-1)/2):=
    mul_nonneg (mul_nonneg hrow (sq_nonneg _)) hpower
  unfold energyConstant
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh hh1 (by linarith [P.exponent_pos])) hbase

theorem damped_square_le {Λ t a:ℝ} (hΛ:0≤Λ) (ht:0≤t):
    (a*exp (-Λ*t))^2≤a^2:=by
  have he:exp (-Λ*t)≤1:=exp_le_one_iff.mpr (by nlinarith)
  have h0:0≤exp (-Λ*t):=(exp_pos _).le
  have h1:exp (-Λ*t)^2≤1:=(pow_le_pow_left₀ h0 he 2).trans_eq (by norm_num)
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_left h1 (sq_nonneg a)).trans_eq (mul_one _)

end SHE.ReferenceBracketUniform
