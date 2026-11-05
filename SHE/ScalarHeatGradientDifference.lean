module

public import SHE.ScalarHeatBandEnvelope

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.ScalarHeatGradientDifference
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal

theorem decay_order {r σ s t : ℝ} (hr : 0<r) (hσ : 0<σ) (hs : 0≤s) (hst : s≤t) :
    decay r σ t≤decay r σ s := by
  have hb : 0<σ/r^2:=div_pos hσ (sq_pos_of_pos hr)
  by_cases h : σ/r^2≤1
  · have hps : 1≤(σ/r^2)^(-s):=by
      simpa only [one_rpow] using rpow_le_rpow_of_nonpos hb h (neg_nonpos.mpr hs)
    have hpt : 1≤(σ/r^2)^(-t):=by
      simpa only [one_rpow] using rpow_le_rpow_of_nonpos hb h (neg_nonpos.mpr (hs.trans hst))
    simp only [decay,min_eq_left hps,min_eq_left hpt,le_refl]
  · exact min_le_min_left 1 (rpow_le_rpow_of_exponent_le (le_of_not_ge h) (neg_le_neg hst))

def constant (β : ℝ) : ℝ:=max (ScalarHeatBandEnvelope.constant β 0) (ScalarHeatBandEnvelope.constant β 1)

theorem constant_nonneg (β : ℝ) : 0≤constant β:=
  (ScalarHeatBandEnvelope.constant_nonneg β 0).trans (le_max_left _ _)

/-- The gradient-displacement term of the COMPLETE martingale has the
true minimum of a uniform bound and a Lipschitz bound, retaining the
same polynomial variance decay as the original gradient. -/
theorem gradient_difference {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ : ℝ≥0) (hσ : 0<σ)
    (j : ℕ) (x y : ℝ) :
    |deriv (heat σ (ScalarHeatBands.band a (j+1))) y-deriv (heat σ (ScalarHeatBands.band a (j+1))) x|≤
      (2*H*constant β)*CompactMollifier.radius (j+1)^(β-1)*
        decay (CompactMollifier.radius (j+1)) σ ((3-β)/2)*
        min 1 (|y-x|/CompactMollifier.radius (j+1)) := by
  let r:=CompactMollifier.radius (j+1)
  let g:=deriv (heat σ (ScalarHeatBands.band a (j+1)))
  let d:=decay r σ ((3-β)/2)
  let G:=H*constant β*r^(β-1)*d
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hs : 0<(σ:ℝ):=by exact_mod_cast hσ
  have hd : 0≤d:=le_min (by norm_num) (rpow_nonneg (div_nonneg hs.le (sq_nonneg r)) _)
  have hG : 0≤G:=mul_nonneg (mul_nonneg (mul_nonneg hH (constant_nonneg β)) (rpow_nonneg hr.le _)) hd
  have hsmall (z : ℝ) : |g z|≤G := by
    have hb:=ScalarHeatBandEnvelope.jet_bound ha hH hβ hβ1 hh σ hσ j 0 z
    simp only [Nat.cast_zero,sub_zero,zero_add,iteratedDeriv_one] at hb
    apply hb.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left (ScalarHeatBandEnvelope.constant β 0)
        (ScalarHeatBandEnvelope.constant β 1)) hH) (rpow_nonneg hr.le _)) hd
  have hsecond (z : ℝ) : |deriv g z|≤H*constant β*r^(β-2)*d := by
    have hb:=ScalarHeatBandEnvelope.jet_bound ha hH hβ hβ1 hh σ hσ j 1 z
    have hdec := decay_order hr hs (show 0≤(3-β)/2 by linarith)
      (show (3-β)/2≤(4-β)/2 by linarith)
    have hc : 0≤H*ScalarHeatBandEnvelope.constant β 1*r^(β-2):=
      mul_nonneg (mul_nonneg hH (ScalarHeatBandEnvelope.constant_nonneg β 1)) (rpow_nonneg hr.le _)
    have he : β-(1:ℝ)-1=β-2:=by ring
    norm_num only [Nat.cast_one,show (1:ℕ)+1=2 by rfl,show ((1:ℝ)+3-β)/2=(4-β)/2 by ring] at hb
    rw [he] at hb
    have hb': |deriv g z|≤H*ScalarHeatBandEnvelope.constant β 1*r^(β-2)*decay r σ ((4-β)/2):=by
      simpa only [g,show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hb
    exact hb'.trans ((mul_le_mul_of_nonneg_left hdec hc).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right (ScalarHeatBandEnvelope.constant β 0)
          (ScalarHeatBandEnvelope.constant β 1)) hH) (rpow_nonneg hr.le _)) hd))
  have hgs : BoundedSmooth g:=deriv_boundedSmooth (heat_boundedSmooth σ (ScalarHeatBands.band_boundedSmooth ha (j+1)))
  have hlip:=Convex.norm_image_sub_le_of_norm_deriv_le (s:=univ)
    (fun z _=>hgs.smooth.differentiable (by simp) z)
    (fun z _=>show ‖deriv g z‖≤H*constant β*r^(β-2)*d by simpa only [Real.norm_eq_abs] using hsecond z)
    convex_univ (mem_univ x) (mem_univ y)
  have he : r^(β-2)=r^(β-1)/r:=by
    rw [←Real.rpow_sub_one hr.ne']
    congr 1
    ring
  have hlarge : |g y-g x|≤2*G*(|y-x|/r):=by
    simp only [Real.norm_eq_abs] at hlip
    rw [he] at hlip
    have hratio : 0≤|y-x|/r:=div_nonneg (abs_nonneg _) hr.le
    have hlow : |g y-g x|≤G*(|y-x|/r):=by
      simpa only [G,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hlip
    exact hlow.trans (by nlinarith [mul_nonneg hG hratio])
  have hsmall' : |g y-g x|≤2*G:=(abs_sub _ _).trans ((add_le_add (hsmall y) (hsmall x)).trans_eq (by ring))
  have hhmin:=le_min hsmall' hlarge
  have heq : (2*H*constant β)*r^(β-1)*d=2*G:=by dsimp only [G]; ring
  change _≤(2*H*constant β)*r^(β-1)*d*min 1 (|y-x|/r)
  rw [heq,mul_min_of_nonneg _ _ (mul_nonneg (by norm_num) hG),mul_one]
  exact hhmin

end SHE.ScalarHeatGradientDifference
