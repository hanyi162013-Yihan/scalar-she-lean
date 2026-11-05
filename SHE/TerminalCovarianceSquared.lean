module

public import SHE.TerminalCovarianceBudget

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.TerminalCovarianceBudget
open Real GaussianAssignmentBlocks PhysicalAssignmentGapScale AllocatedAssignmentKernel CoveredHistoryGeometry
open scoped BigOperators

/-- Positivity of the literal finite terminal covariance budget is
proved from the original elliptic score and rough/root prefactors. -/
theorem budget_nonneg (P:CanonicalCovariance.ProfileParameters) {ell:ℝ} (hell:0<ell)
    (C:ℕ→ℝ) (hC:∀j,0≤C j) (k:ℕ) {span A0 ν:ℝ}
    (hs:0<span) (hA0:0≤A0) (hν:0≤ν):
    0≤QuarterRMSTimeFactors.oldTimeBudget P ell C k span 0 1 A0 ν:=by
  rw [budget_eq_root_sum P ell C k hs A0 ν]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  rw [PairedBudgetFactors.mass_factorization]
  have hInv:=inverseDegreeProduct_nonneg
    ((assignments (m:=k+1) (List.finRange k)).get i) (List.get_mem _ i)
    (show 0<P.exponent/4 by linarith [P.exponent_pos]) (show P.exponent/4≤1 by linarith [P.exponent_le_one])
  have hc:0≤PairedBudgetFactors.coefficient P ell C
      ((assignments (m:=k+1) (List.finRange k)).get i) (List.get_mem _ i) 0 A0 0:=by
    simp only [PairedBudgetFactors.coefficient,Fin.cases_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (scorePrefactor_nonneg hell C hC k))
      (prefactor_nonneg P _ hA0 1)) (mul_nonneg (sq_nonneg _) hInv)
  exact mul_nonneg (mul_nonneg hc (rpow_nonneg hs.le _))
    (pow_nonneg (rootMass_nonneg (mul_nonneg hν (sqrt_nonneg _)) hs.le) _)

/-- Squaring the genuine finite budget retains the full N beta/2
energy gain and only the arbitrary root-frequency loss. -/
theorem frequency_square_bound (P:CanonicalCovariance.ProfileParameters) {ell:ℝ} (hell:0<ell)
    (C:ℕ→ℝ) (hC:∀j,0≤C j) (k:ℕ) {span η A0 ν:ℝ}
    (hs:0<span) (hs1:span≤1) (hη:0<η) (hA0:0≤A0) (hν:0≤ν):
    (QuarterRMSTimeFactors.oldTimeBudget P ell C k span 0 1 A0 ν/2)^2≤
      A0^2*(constant P ell C k η/2)^2*(1+ν)^(2*η)*span^((k:ℝ)*P.exponent/2):=by
  have hb:=frequency_bound P ell C k hs hs1 hη hA0 hν
  have h0:=budget_nonneg P hell C hC k hs hA0 hν
  have hd:=div_le_div_of_nonneg_right hb (by norm_num:(0:ℝ)≤2)
  have hsquare:=mul_self_le_mul_self (div_nonneg h0 (by norm_num:(0:ℝ)≤2)) hd
  have hrν:((1+ν)^η)^2=(1+ν)^(2*η):=by
    rw [←rpow_mul_natCast (show 0≤1+ν by positivity)]
    congr 1
    ring
  have hrh:(span^((k:ℝ)*P.exponent/4))^2=span^((k:ℝ)*P.exponent/2):=by
    rw [←rpow_mul_natCast hs.le]
    congr 1
    ring
  calc
    _≤(A0*constant P ell C k η*(1+ν)^η*span^((k:ℝ)*P.exponent/4)/2)^2:=by
      simpa only [pow_two] using hsquare
    _=_:=by rw [div_pow,mul_pow,mul_pow,mul_pow,hrν,hrh];ring

end SHE.TerminalCovarianceBudget
