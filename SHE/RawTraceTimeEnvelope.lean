module

public import SHE.NormalizedCostScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.RawTraceTimeEnvelope
open Real SignedKernelTruncation NormalizedKernelSplit

def logLossConstant (η : ℝ) : ℝ := 1+(2:ℝ)^η/η

theorem logLossConstant_pos {η : ℝ} (hη : 0 < η) : 0 < logLossConstant η := by
  unfold logLossConstant
  positivity

/-- The true scale-ratio logarithm costs only a chosen positive fresh-gap
loss. This loss is explicit, so its integrability margin can be checked. -/
theorem log_ratio_bound {δ w η : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w) (hη : 0 < η) :
    1+log (2*w/δ) ≤ logLossConstant η*(w/δ)^η := by
  have hw : 0 < w := hδ.trans_le hδw
  have ha : 1 ≤ w/δ := (le_div_iff₀ hδ).mpr (by simpa using hδw)
  have ha0 : 0 ≤ w/δ := (zero_lt_one.trans_le ha).le
  have hh := Real.log_le_rpow_div (show 0 ≤ 2*(w/δ) by positivity) hη
  have hp : 1 ≤ (w/δ)^η := Real.one_le_rpow ha hη.le
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2:ℝ)) ha0] at hh
  calc
    _ = 1+log (2*(w/δ)) := by congr 2;ring
    _ ≤ (w/δ)^η+((2:ℝ)^η*(w/δ)^η)/η := add_le_add hp hh
    _ = _ := by unfold logLossConstant;ring

theorem goodCost_loss {δ w η : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w) (hη : 0 < η)
    {J : ℝ} (hJ : 0 ≤ J) (ρ R D : ℝ) :
    goodCost J ρ δ w R (heatAmplitude D δ w) ≤
      J*nativeCostConstant ρ*logLossConstant η*R^2*D^2*
        δ^(-1-ρ-η)*w^(ρ+η) := by
  have hw : 0 < w := hδ.trans_le hδw
  rw [goodCost_physical hδ hw]
  have hpre : 0 ≤ J*nativeCostConstant ρ*R^2*D^2*δ^(-1-ρ)*w^ρ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hJ
      (nativeCostConstant_pos ρ).le) (sq_nonneg _)) (sq_nonneg _))
        (Real.rpow_nonneg hδ.le _)) (Real.rpow_nonneg hw.le _)
  apply (mul_le_mul_of_nonneg_left (log_ratio_bound hδ hδw hη) hpre).trans_eq
  rw [Real.div_rpow hw.le hδ.le,div_eq_mul_inv,←Real.rpow_neg hδ.le]
  have hd : δ^(-1-ρ)*δ^(-η)=δ^(-1-ρ-η) := by
    rw [←Real.rpow_add hδ]
    congr 1
  have hw' : w^ρ*w^η=w^(ρ+η) := (Real.rpow_add hw _ _).symm
  calc
    _ = J*nativeCostConstant ρ*logLossConstant η*R^2*D^2*
        (δ^(-1-ρ)*δ^(-η))*(w^ρ*w^η) := by ring
    _ = _ := by rw [hd,hw']

def freshExponent (ρ η : ℝ) : ℝ := (1+ρ+η)/2

theorem freshExponent_lt_one {ρ η : ℝ} (h : ρ+η < 1) : freshExponent ρ η < 1 := by
  unfold freshExponent
  linarith

theorem freshExponent_pos {ρ η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 ≤ η) : 0 < freshExponent ρ η := by
  unfold freshExponent
  linarith

end SHE.RawTraceTimeEnvelope
