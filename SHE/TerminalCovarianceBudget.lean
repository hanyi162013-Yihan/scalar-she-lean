module

public import SHE.QuarterRMSOldTime
public import SHE.PairedBudgetFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.TerminalCovarianceBudget
open Real GaussianAssignmentBlocks PhysicalAssignmentGapScale AllocatedAssignmentKernel CoveredHistoryGeometry
open scoped BigOperators

/-- The terminal covariance time budget has the FULL old-age gain:
empty rough ages and assigned rough degrees sum to the original depth. -/
theorem budget_eq_root_sum (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (k:ℕ) {span:ℝ} (hs:0<span) (A0 ν:ℝ):
    QuarterRMSTimeFactors.oldTimeBudget P ell C k span 0 1 A0 ν=
      (1/2:ℝ)*∑i:Fin (assignments (m:=k+1) (List.finRange k)).length,
        PairedRMSTimeBudget.mass P ell C
          ((assignments (m:=k+1) (List.finRange k)).get i)
          (List.get_mem _ i) span 0 A0 ν 0:=by
  unfold QuarterRMSTimeFactors.oldTimeBudget
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PairedRMSTimeBudget.mass,Fin.cases_zero,sub_zero,div_one]
  have he:(P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)+
      (1+(P.exponent/4)*(roughCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)-1)=
      (k:ℝ)*P.exponent/4:=by
    have hh:=empty_rough_count (cs:=(assignments (m:=k+1) (List.finRange k)).get i)
    have hc:(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)+
        (roughCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)=(k:ℝ):=by exact_mod_cast hh
    rw [←hc]
    ring
  have hp:span^((P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ))*
      span^(1+(P.exponent/4)*(roughCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)-1)=
      span^((k:ℝ)*P.exponent/4):=by rw [←rpow_add hs,he]
  calc
    _=(scorePrefactor ell C k*prefactor P ((assignments (m:=k+1) (List.finRange k)).get i) A0 1)*
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct ((assignments (m:=k+1) (List.finRange k)).get i)
        (List.get_mem _ i) (P.exponent/4))*
      (span^((P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ))*
        span^(1+(P.exponent/4)*(roughCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)-1))*
      rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span^
        rootCount ((assignments (m:=k+1) (List.finRange k)).get i):=by ring
    _=_:=by rw [hp];ring

def constant (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ) (k:ℕ) (η:ℝ):ℝ:=
  (1/2:ℝ)*∑i:Fin (assignments (m:=k+1) (List.finRange k)).length,
    |PairedBudgetFactors.coefficient P ell C ((assignments (m:=k+1) (List.finRange k)).get i)
      (List.get_mem _ i) 0 1 0| *
    PastMeanTimeFactors.frequencyRootConstant P k η^rootCount ((assignments (m:=k+1) (List.finRange k)).get i)

/-- Uniform terminal covariance budget, at fixed finite depth and any
positive root-frequency loss. No fresh-gap loss is introduced. -/
theorem frequency_bound (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ) (k:ℕ)
    {span η A0 ν:ℝ} (hs:0<span) (hs1:span≤1) (hη:0<η) (hA0:0≤A0) (hν:0≤ν):
    QuarterRMSTimeFactors.oldTimeBudget P ell C k span 0 1 A0 ν≤
      A0*constant P ell C k η*(1+ν)^η*span^((k:ℝ)*P.exponent/4):=by
  rw [budget_eq_root_sum P ell C k hs A0 ν]
  let cs:=assignments (m:=k+1) (List.finRange k)
  have hh(i:Fin cs.length):PairedRMSTimeBudget.mass P ell C (cs.get i) (List.get_mem cs i)
      span 0 A0 ν 0≤
      A0*|PairedBudgetFactors.coefficient P ell C (cs.get i) (List.get_mem cs i) 0 1 0| *
        PastMeanTimeFactors.frequencyRootConstant P k η^rootCount (cs.get i)*
        (1+ν)^η*span^((k:ℝ)*P.exponent/4):=by
    rw [PairedBudgetFactors.mass_factorization,PairedBudgetFactors.coefficient_amplitude]
    simp only [PairedBudgetFactors.degree,Fin.cases_zero]
    have hr:=PairedBudgetFactors.rootPower_frequency_bound P (cs.get i) (List.get_mem cs i) hs.le hs1 hν hη
    have hc:=le_abs_self (PairedBudgetFactors.coefficient P ell C (cs.get i) (List.get_mem cs i) 0 1 0)
    have h0:=mul_le_mul_of_nonneg_left hc hA0
    have h1:=mul_le_mul_of_nonneg_right h0 (rpow_nonneg hs.le ((k:ℝ)*P.exponent/4))
    have h2:=mul_le_mul_of_nonneg_right h1
      (pow_nonneg (rootMass_nonneg (mul_nonneg hν (sqrt_nonneg (ProfileVariance.upperConstant*(P.lower/2)))) hs.le) (rootCount (cs.get i)))
    have h3:=mul_le_mul_of_nonneg_left hr
      (mul_nonneg (mul_nonneg hA0 (abs_nonneg (PairedBudgetFactors.coefficient P ell C (cs.get i) (List.get_mem cs i) 0 1 0))) (rpow_nonneg hs.le ((k:ℝ)*P.exponent/4)))
    exact h2.trans (by convert! h3 using 1 <;> ring)
  have hsum:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hh i)
  have ht:=mul_le_mul_of_nonneg_left hsum (by norm_num:(0:ℝ)≤1/2)
  convert! ht using 1
  dsimp only [constant,cs]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SHE.TerminalCovarianceBudget
