module

public import SHE.NormalizedKernelSplit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open Set Filter MeasureTheory AddCircle Real StoppedFourier
local instance normalizedHeatMass_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩

def heatAmplitude (D δ w : ℝ) : ℝ := D*δ^(-(1/2:ℝ))*w^(1/4:ℝ)
def heatEnvelope (D δ w : ℝ) (p : Space) : ℝ :=
  heatAmplitude D δ w*‖ProfileVariance.heatPhysical (8*w) p.1 p.2‖
def heatMassConstant : ℝ := 1+StoppedFourier.heatConstant

theorem heatMassConstant_pos : 0 < heatMassConstant := by
  unfold heatMassConstant
  linarith [StoppedFourier.heatConstant_pos]

theorem heatEnvelope_continuous {D δ w : ℝ} (hw : 0 < w) : Continuous (heatEnvelope D δ w) :=
  continuous_const.mul (NativeHeatSpan.continuous_heatPhysical_space (by positivity)).norm

theorem heatEnvelope_sq_integrable {D δ w : ℝ} (hw : 0 < w) :
    Integrable (fun p : Space => heatEnvelope D δ w p^2)
      ((haarAddCircle (T:=2*π)).prod haarAddCircle) :=
  ((heatEnvelope_continuous hw).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The outside w^(1/2) cancels the actual native heat-square mass.
Thus the bad branch has only the manuscript's D² δ^(-1) density. -/
theorem heatEnvelope_sq_mass {D δ w : ℝ} (hδ : 0 < δ) (hw : 0 < w) (hw1 : w ≤ 1) :
    (∫ p : Space, heatEnvelope D δ w p^2 ∂(haarAddCircle (T:=2*π)).prod haarAddCircle) ≤
      heatMassConstant*D^2*δ^(-1:ℝ) := by
  have hk (y : HeatCircle) : (∫ x : HeatCircle, ‖ProfileVariance.heatPhysical (8*w) y x‖^2 ∂haarAddCircle)=
      ‖circleHeat (8*w) y‖^2 := by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    exact (ProfileVariance.heatPhysical_ae (t:=8*w) (by positivity) y).mono (fun x hx => by
      change ‖ProfileVariance.heatPhysical (8*w) y x‖^2=‖circleHeat (8*w) y x‖^2
      rw [hx])
  have hpoint (y : HeatCircle) : (∫ x : HeatCircle, heatEnvelope D δ w (y,x)^2 ∂haarAddCircle) ≤
      (heatAmplitude D δ w)^2*(1+StoppedFourier.heatConstant*w^(-(1/2:ℝ))) := by
    simp only [heatEnvelope,mul_pow]
    rw [integral_const_mul,hk]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have ht := circleHeat_norm_sq_bound (by positivity : 0 < 8*w) y
    have hp : (8*w)^(-(1/2:ℝ)) ≤ w^(-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hw (by linarith) (by norm_num)
    exact ht.trans (by linarith [mul_le_mul_of_nonneg_left hp StoppedFourier.heatConstant_pos.le])
  have hi := (heatEnvelope_sq_integrable (D:=D) (δ:=δ) hw).integral_prod_left
  have hb : (∫ p : Space, heatEnvelope D δ w p^2 ∂(haarAddCircle (T:=2*π)).prod haarAddCircle) ≤
      (heatAmplitude D δ w)^2*(1+StoppedFourier.heatConstant*w^(-(1/2:ℝ))) := by
    rw [integral_prod _ (heatEnvelope_sq_integrable hw)]
    exact (integral_mono hi (integrable_const _) hpoint).trans_eq (by simp)
  have hδpow : (δ^(-(1/2:ℝ)))^2=δ^(-1:ℝ) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    norm_num
  have hwpow : (w^(1/4:ℝ))^2=w^(1/2:ℝ) := by
    rw [← Real.rpow_mul_natCast hw.le]
    norm_num
  have hcancel : w^(1/2:ℝ)*w^(-(1/2:ℝ))=1 := by
    rw [← Real.rpow_add hw]
    norm_num
  have hwHalf : w^(1/2:ℝ) ≤ 1 := Real.rpow_le_one hw.le hw1 (by norm_num)
  apply hb.trans
  unfold heatAmplitude heatMassConstant
  rw [mul_pow,mul_pow,hδpow,hwpow]
  have he : D^2*δ^(-1:ℝ)*w^(1/2:ℝ)*(1+StoppedFourier.heatConstant*w^(-(1/2:ℝ)))=
      D^2*δ^(-1:ℝ)*(w^(1/2:ℝ)+StoppedFourier.heatConstant) := by
    rw [mul_add,mul_one]
    have hh := congrArg (fun z : ℝ => D^2*δ^(-1:ℝ)*StoppedFourier.heatConstant*z) hcancel
    nlinarith only [hh]
  rw [he]
  calc
    _ ≤ D^2*δ^(-1:ℝ)*(1+StoppedFourier.heatConstant) :=
      mul_le_mul_of_nonneg_left (by linarith : w^(1/2:ℝ)+StoppedFourier.heatConstant ≤ 1+StoppedFourier.heatConstant)
        (mul_nonneg (sq_nonneg D) (Real.rpow_nonneg hδ.le _))
    _ = (1+StoppedFourier.heatConstant)*D^2*δ^(-1:ℝ) := by ring

end SHE.NormalizedKernelSplit
