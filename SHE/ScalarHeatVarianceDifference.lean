module

public import SHE.ScalarHeatBandEnvelope
public import SHE.ScalarGaussianHeatEquation
public import SHE.ScalarHeatGradientEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ScalarHeatVarianceDifference
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal

/-- ACTUAL remaining-variance changed slot of the complete martingale.
The scalar heat equation supplies the two extra state derivatives and
the same proved polynomial Gaussian cancellation at positive variance. -/
theorem gradient_difference {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (x : ℝ)
    {v w : ℝ} (hv : lo≤v) (hw : lo≤w) :
    |deriv (heat w.toNNReal (ScalarHeatBands.band a (j+1))) x-
      deriv (heat v.toNNReal (ScalarHeatBands.band a (j+1))) x|≤
      ((1/2:ℝ)*H*constant β 2*CompactMollifier.radius (j+1)^(β-3)*
        decay (CompactMollifier.radius (j+1)) lo ((5-β)/2))*|w-v| := by
  let f : ℝ→ℝ:=fun t=>deriv (heat t.toNNReal (ScalarHeatBands.band a (j+1))) x
  have hd (t : ℝ) (ht : t∈Ici lo) : HasDerivAt f
      ((1/2:ℝ)*iteratedDeriv 3 (heat t.toNNReal (ScalarHeatBands.band a (j+1))) x) t:=by
    simpa only [f,iteratedDeriv_one] using ScalarGaussianHeatEquation.hasDerivAt_jet
      (ScalarHeatBands.band_boundedSmooth ha (j+1)) (hlo.trans_le ht) 1 x
  have hb (t : ℝ) (ht : t∈Ici lo) : ‖deriv f t‖≤
      (1/2:ℝ)*H*constant β 2*CompactMollifier.radius (j+1)^(β-3)*
        decay (CompactMollifier.radius (j+1)) lo ((5-β)/2) := by
    rw [(hd t ht).deriv,norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hj:=jet_bound ha hH hβ hβ1 hh t.toNNReal (Real.toNNReal_pos.mpr (hlo.trans_le ht)) j 2 x
    simp only [Nat.reduceAdd,Nat.cast_ofNat,Real.coe_toNNReal _ (hlo.le.trans ht)] at hj
    rw [show β-2-1=β-3 by ring,show (2+3-β)/2=(5-β)/2 by ring] at hj
    have hd':=ScalarHeatGradientEnergy.decay_variance (CompactMollifier.radius_pos (j+1)) hlo
      (show 0≤(5-β)/2 by linarith) ht
    have hn : 0≤H*constant β 2*CompactMollifier.radius (j+1)^(β-3):=
      mul_nonneg (mul_nonneg hH (constant_nonneg β 2)) (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _)
    have he : |iteratedDeriv 3 (heat t.toNNReal (ScalarHeatBands.band a (j+1))) x|≤
      H*constant β 2*CompactMollifier.radius (j+1)^(β-3)*decay (CompactMollifier.radius (j+1)) lo ((5-β)/2):=by
      convert hj.trans (mul_le_mul_of_nonneg_left hd' hn) using 1 <;> congr 2 <;> ring
    simpa only [Real.norm_eq_abs,mul_assoc] using mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤1/2)
  have hi:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=f) (s:=Ici lo) (fun t ht=>(hd t ht).differentiableAt) hb (convex_Ici lo) hv hw
  simpa only [f,Real.norm_eq_abs] using hi

end SHE.ScalarHeatVarianceDifference
