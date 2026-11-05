module

public import SHE.SignedKernelTruncation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.SignedKernelTruncation
open Real NativeHeatSpan NormalizedKernelSplit

/-- The fixed period-2π conversion constant in the good-kernel time
density. It is independent of both physical ages and the spectral mass. -/
def nativeCostConstant (ρ : ℝ) : ℝ := (clock 1)^(ρ-1/2)*(clock (1/2))^(-ρ)

theorem nativeCostConstant_pos (ρ : ℝ) : 0 < nativeCostConstant ρ := by
  unfold nativeCostConstant
  have h1 : 0 < clock 1 := clock_pos (by norm_num)
  have hh : 0 < clock (1/2) := clock_pos (by norm_num)
  positivity

/-- The exact physical time density after the normalized heat amplitude
is inserted into the genuine signed two-time estimate. -/
theorem goodCost_physical {δ w : ℝ} (hδ : 0 < δ) (hw : 0 < w)
    (J ρ R D : ℝ) :
    goodCost J ρ δ w R (heatAmplitude D δ w)=
      J*nativeCostConstant ρ*R^2*D^2*δ^(-1-ρ)*w^ρ*(1+log (2*w/δ)) := by
  have hc1 : 0 < clock 1 := clock_pos (by norm_num)
  have hch : 0 < clock (1/2) := clock_pos (by norm_num)
  have hcw : clock w=clock 1*w := by unfold clock; ring
  have hcd : clock (δ/2)=clock (1/2)*δ := by unfold clock; ring
  have hratio : clock w/clock (δ/2)=2*w/δ := by
    unfold clock
    field_simp
  have hd : (δ^(-(1/2:ℝ)))^2=δ^(-1:ℝ) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    norm_num
  have hw' : (w^(1/4:ℝ))^2=w^(1/2:ℝ) := by
    rw [← Real.rpow_mul_natCast hw.le]
    norm_num
  have hwp : w^(1/2:ℝ)*w^(ρ-1/2)=w^ρ := by
    rw [← Real.rpow_add hw]
    congr 1
    ring
  have hdp : δ^(-1:ℝ)*δ^(-ρ)=δ^(-1-ρ) := by
    rw [← Real.rpow_add hδ]
    congr 1
  unfold goodCost heatAmplitude nativeCostConstant
  rw [hratio,hcw,hcd,Real.mul_rpow hc1.le hw.le,Real.mul_rpow hch.le hδ.le]
  simp only [mul_pow,hd,hw']
  calc
    _ = J*((clock 1)^(ρ-1/2)*(clock (1/2))^(-ρ))*R^2*D^2*
        (δ^(-1:ℝ)*δ^(-ρ))*(w^(1/2:ℝ)*w^(ρ-1/2))*(1+log (2*w/δ)) := by ring
    _ = _ := by rw [hwp,hdp]

end SHE.SignedKernelTruncation
