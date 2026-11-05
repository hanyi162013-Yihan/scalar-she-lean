module

public import SHE.PairedRMSWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.PairedCoefficientFrequency
open Real
open scoped NNReal

theorem source_bound {H β χ ν:ℝ} (hH:0≤H) (hχ:0≤χ) (hν:0≤ν):
    PairedSourceBudget.coefficient H β χ ν≤
      PairedSourceBudget.coefficient H β χ 1*((1+ν)^χ)^2:=by
  have hv:0≤ν^χ:=rpow_nonneg hν _
  have hz:0≤(1+ν)^χ:=rpow_nonneg (by positivity) _
  have hb:1≤(1+ν)^χ:=one_le_rpow (by linarith) hχ
  have hn:ν^χ≤(1+ν)^χ:=rpow_le_rpow hν (by linarith) hχ
  have hs:(ν^χ)^2≤((1+ν)^χ)^2:=(sq_le_sq₀ hv hz).mpr hn
  have ht:1≤((1+ν)^χ)^2:=by nlinarith
  have hp:0≤(max 1 (H^(χ/β)))^2:=sq_nonneg _
  have hq:0≤(2*H)^(2*χ/β):=rpow_nonneg (by positivity) _
  unfold PairedSourceBudget.coefficient
  rw [one_rpow]
  nlinarith [mul_nonneg hp (sub_nonneg.mpr ht),mul_nonneg hq (sub_nonneg.mpr ht)]

/-- Only the root source costs a chi frequency power. Rough sources
retain coefficient one; their paired age loss is handled separately. -/
theorem coefficient_bound {k:ℕ} (P:CanonicalCovariance.ProfileParameters)
    {κ M:ℝ} (hκ:0≤κ) (hM:0≤M) (B0:ℝ≥0) (cs:List (Fin k×Fin (k+1)))
    {χ ν:ℝ} (hχ:0≤χ) (hν:0≤ν) (order:ℕ) (i:Fin (k+1)):
    sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ ν order i)≤
      sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ 1 order i)*
        Fin.cases ((1+ν)^χ) (fun _=>1) i:=by
  refine Fin.cases ?_ (fun j=>?_) i
  · have hs:=source_bound (β:=P.exponent) P.holder_nonneg hχ hν
    have hb:0≤2*(PairedTerminalConstants.constant P κ M B0 cs χ order 0)^(1/(order:ℝ)):=
      mul_nonneg (by norm_num) (rpow_nonneg (PairedTerminalConstants.constant_nonneg P hκ hM B0 cs χ order 0) _)
    have hc:PairedRMSWeights.coefficient P κ M B0 cs χ ν order 0≤
        PairedRMSWeights.coefficient P κ M B0 cs χ 1 order 0*((1+ν)^χ)^2:=by
      have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hb)
        (sq_nonneg (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ))
      convert! hh using 1 <;> simp only [PairedRMSWeights.coefficient,Fin.cases_zero] <;> ring
    have hc1:=PairedRMSWeights.coefficient_nonneg P hκ hM B0 cs χ 1 order (0:Fin (k+1))
    have hz:0≤(1+ν)^χ:=rpow_nonneg (by positivity) _
    exact (sqrt_le_sqrt hc).trans_eq (by rw [sqrt_mul hc1,sqrt_sq hz];rfl)
  · simp only [PairedRMSWeights.coefficient,Fin.cases_succ,mul_one,le_refl]

end SHE.PairedCoefficientFrequency
