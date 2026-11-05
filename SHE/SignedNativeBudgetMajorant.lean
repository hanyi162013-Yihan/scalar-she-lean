module

public import SHE.PastSignedEndpointBudget
public import SHE.NativeCurrentBudgetFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.SignedNativeBandFrequency
open Real RawTraceTimeEnvelope QuarterRMSTimeFactors

/-- The actual two signed old-time budgets are dominated by the exact
frequency envelopes used in the moving current-energy ledger. -/
theorem budget_square_bound (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ρ η T A0 ν G B:ℝ)(hT:0<T)(hT1:T≤1){w:ℝ}(hw:0<w)
    (hG:0≤G)(hB:0≤B):
    (G*w^((ρ+η)/2)*oldTimeBudget P ell Cs k T (T-w) (freshDegree ρ η) A0 ν+
      B*oldTimeBudget P ell Cs k T (T-w) (1/2:ℝ) A0 ν)^2≤
      2*A0^2*(G^2*NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν w^2+
        B^2*NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν w^2):=by
  have hg:=NativeCurrentBudgetFrequency.budget_le P ell Cs k (ρ+η) (2*(ρ+η)) ν T A0 hT hT1 hw
  have hf:freshDegree ρ η=(2-2*(ρ+η))/4:=by unfold freshDegree freshExponent;ring
  rw [←hf] at hg
  have hb:=NativeCurrentBudgetFrequency.budget_le P ell Cs k 0 0 ν T A0 hT hT1 hw
  norm_num only [zero_div,rpow_zero,one_mul,show (2-(0:ℝ))/4=1/2 by norm_num] at hb
  have hga:=mul_le_mul_of_nonneg_left hg hG
  have hba:=mul_le_mul_of_nonneg_left hb hB
  have hGm:=NativeCurrentBudgetFrequency.majorant_nonneg P ell Cs k (ρ+η) (2*(ρ+η)) ν w
  have hBm:=NativeCurrentBudgetFrequency.majorant_nonneg P ell Cs k 0 0 ν w
  have hga2: (G*w^((ρ+η)/2)*oldTimeBudget P ell Cs k T (T-w) (freshDegree ρ η) A0 ν)^2≤
      A0^2*G^2*NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν w^2:=by
    have hh:=pow_le_pow_left₀ (mul_nonneg hG (abs_nonneg _)) hga 2
    convert! hh using 1 <;> simp only [mul_pow,sq_abs] <;> ring
  have hba2: (B*oldTimeBudget P ell Cs k T (T-w) (1/2:ℝ) A0 ν)^2≤
      A0^2*B^2*NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν w^2:=by
    have hh:=pow_le_pow_left₀ (mul_nonneg hB (abs_nonneg _)) hba 2
    convert! hh using 1 <;> simp only [mul_pow,sq_abs] <;> ring
  nlinarith [sq_nonneg (G*w^((ρ+η)/2)*oldTimeBudget P ell Cs k T (T-w) (freshDegree ρ η) A0 ν-
    B*oldTimeBudget P ell Cs k T (T-w) (1/2:ℝ) A0 ν)]

end SHE.SignedNativeBandFrequency
