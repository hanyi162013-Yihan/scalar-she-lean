module
public import SHE.TerminalCovarianceSquared
public import SHE.QuarterBudgetScaling
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.PastReferenceBudgetFrequency
open Real PhysicalAssignmentGapScale GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry
open scoped BigOperators

theorem fresh_identity(P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)
    {h f:ℝ}(hh:0<h)(hf:0<f)(A0 ν:ℝ):
    QuarterRMSTimeFactors.oldTimeBudget P ell C k h 0 f A0 ν=
      (1/f)*h^(f-1)*QuarterRMSTimeFactors.oldTimeBudget P ell C k h 0 1 A0 ν:=by
  have hs:=QuarterRMSTimeFactors.oldTimeBudget_scaling P ell C k h 0 f 1 A0 ν hh hf zero_lt_one
  simp only [sub_zero] at hs
  have hp:h^(f-1)*h^(1-f)=1:=by rw [←rpow_add hh];simp
  calc
    _=h^(f-1)*(h^(1-f)*QuarterRMSTimeFactors.oldTimeBudget P ell C k h 0 f A0 ν):=by rw [←mul_assoc,hp,one_mul]
    _=_:=by rw [hs];ring

/-- Every positive fresh degree retains the full old-age gain at the
past endpoint, with an arbitrarily small root-frequency loss. -/
theorem budget_bound(P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)
    {h f η A0 ν:ℝ}(hh:0<h)(hh1:h≤1)(hf:0<f)(hη:0<η)(hA:0≤A0)(hν:0≤ν):
    QuarterRMSTimeFactors.oldTimeBudget P ell C k h 0 f A0 ν≤
      A0*(TerminalCovarianceBudget.constant P ell C k η/f)*(1+ν)^η*
        h^(f-1+(k:ℝ)*P.exponent/4):=by
  rw [fresh_identity P ell C k hh hf]
  have hb:=TerminalCovarianceBudget.frequency_bound P ell C k hh hh1 hη hA hν
  have hs:=mul_le_mul_of_nonneg_left hb
    (mul_nonneg (div_nonneg zero_le_one hf.le) (rpow_nonneg hh.le (f-1)))
  apply hs.trans_eq
  rw [rpow_add hh]
  ring

/-- Squaring is legitimate for the literal nonnegative assignment
budget; the same frequency and root-age powers survive exactly. -/
theorem square_bound(P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ){h f η A0 ν:ℝ}
    (hh:0<h)(hh1:h≤1)(hf:0<f)(hη:0<η)(hA:0≤A0)(hν:0≤ν):
    (QuarterRMSTimeFactors.oldTimeBudget P ell C k h 0 f A0 ν)^2≤
      A0^2*(TerminalCovarianceBudget.constant P ell C k η/f)^2*(1+ν)^(2*η)*
        h^(2*f-2+(k:ℝ)*P.exponent/2):=by
  have hb:=budget_bound P ell C k hh hh1 hf hη hA hν
  have hn:0≤QuarterRMSTimeFactors.oldTimeBudget P ell C k h 0 f A0 ν:=by
    rw [fresh_identity P ell C k hh hf]
    exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one hf.le) (rpow_nonneg hh.le _))
      (TerminalCovarianceBudget.budget_nonneg P hell C hC k hh hA hν)
  have hs:=pow_le_pow_left₀ hn hb 2
  apply hs.trans_eq
  rw [mul_pow,mul_pow,mul_pow,←rpow_mul_natCast (by positivity:0≤1+ν),←rpow_mul_natCast hh.le]
  congr 1
  · congr 1
    ring
  · congr 1
    ring
end SHE.PastReferenceBudgetFrequency
