module
public import SHE.ScalarHeatGradientDifference
public import SHE.ScalarHeatBandCancellation
public import SHE.ScalarHeatBandEnvelope

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.GaussianHeatBandRootEnvelope
open Set MeasureTheory ProbabilityTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup
open ScalarHeatBandEnvelope
open scoped NNReal ENNReal

def constant(β:ℝ):ℝ:=3*gaussianAbsMoment β+2*ScalarGaussianJetScale.constant β 1+ScalarHeatBandEnvelope.constant β 0

theorem constant_nonneg(β:ℝ):0≤constant β:=by
  unfold constant
  positivity [gaussianAbsMoment_nonneg β,ScalarGaussianJetScale.constant_nonneg β 1,
    ScalarHeatBandEnvelope.constant_nonneg β 0]

private theorem factor {r σ β:ℝ}(hr:0<r)(hσ:0<σ):
    r^β*(σ/r^2)^(-((2-β)/2))=r^2*σ^((β-2)/2):=by
  rw [show -((2-β)/2)=(β-2)/2 by ring,
    Real.div_rpow hσ.le (sq_nonneg r),←Real.rpow_natCast_mul hr.le,div_eq_mul_inv,
    ←Real.rpow_neg hr.le]
  calc
    _=σ^((β-2)/2)*(r^β*r^(-((2:ℝ)*((β-2)/2)))):=by ring
    _=r^2*σ^((β-2)/2):=by
      rw [←Real.rpow_add hr,show β+ -((2:ℝ)*((β-2)/2))=2 by ring,Real.rpow_two]
      ring

/-- Actual Gaussian heat bands retain polynomial root cancellation in
any extra variance. No annular Fourier support is assumed. -/
theorem root_bound {a:ℝ→ℝ}(ha:BoundedSmooth a){B H β:ℝ}
    (hB:∀x,|a x|≤B)(hH:0≤H)(hβ:0≤β)(hβ1:β≤1)
    (hh:∀x y,|a x-a y|≤H*|x-y|^β)(σ:ℝ≥0)(hσ:0<σ)(j:ℕ)(x:ℝ):
    |heat σ (ScalarHeatBands.band a (j+1)) x|≤
      H*constant β*CompactMollifier.radius (j+1)^β*
        decay (CompactMollifier.radius (j+1)) σ ((2-β)/2):=by
  let r:=CompactMollifier.radius (j+1)
  have hr:0<r:=CompactMollifier.radius_pos (j+1)
  have hs:0<(σ:ℝ):=by exact_mod_cast hσ
  have hc0:3*gaussianAbsMoment β≤constant β:=by
    unfold constant
    linarith [ScalarGaussianJetScale.constant_nonneg β 1,ScalarHeatBandEnvelope.constant_nonneg β 0]
  have hc1:2*ScalarGaussianJetScale.constant β 1≤constant β:=by
    unfold constant
    linarith [gaussianAbsMoment_nonneg β,ScalarHeatBandEnvelope.constant_nonneg β 0]
  have hsmall:|heat σ (ScalarHeatBands.band a (j+1)) x|≤H*constant β*r^β:=by
    have hb:=heat_bound σ (ScalarHeatBands.band_succ_bound ha.smooth.continuous.measurable hB hH hβ hβ1 hh j) x
    have hc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc0 hH) (rpow_nonneg hr.le β)
    calc
      _≤3*(H*gaussianAbsMoment β)*r^β:=hb
      _=(H*(3*gaussianAbsMoment β))*r^β:=by ring
      _≤_:=hc

  have hlarge:|heat σ (ScalarHeatBands.band a (j+1)) x|≤
      H*constant β*r^β*((σ:ℝ)/r^2)^(-((2-β)/2)):=by
    have hb:=ScalarHeatBandCancellation.jet_cancellation ha hH hβ hβ1 hh σ hσ j 0 x
    simp only [iteratedDeriv_zero,Nat.cast_zero,sub_zero,Nat.zero_add] at hb
    have hb':|heat σ (ScalarHeatBands.band a (j+1)) x|≤
        (H*(2*ScalarGaussianJetScale.constant β 1))*r^2*(σ:ℝ)^((β-2)/2):=by
      convert! hb using 1 <;> dsimp only [r] <;> ring
    rw [mul_assoc _ (r^β),factor hr hs]
    simpa only [mul_assoc] using hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hH) (sq_nonneg r))
      (rpow_nonneg hs.le ((β-2)/2)))

  change _≤(H*constant β*r^β)*min 1 (((σ:ℝ)/r^2)^(-((2-β)/2)))
  rw [mul_min_of_nonneg _ _ (mul_nonneg (mul_nonneg hH (constant_nonneg β)) (rpow_nonneg hr.le _)),mul_one]
  exact le_min hsmall hlarge

/-- The exact root translation difference retains BOTH its clipped
state displacement and polynomial future-variance cancellation. -/
theorem difference {a:ℝ→ℝ}(ha:BoundedSmooth a){B H β:ℝ}
    (hB:∀x,|a x|≤B)(hH:0≤H)(hβ:0≤β)(hβ1:β≤1)
    (hh:∀x y,|a x-a y|≤H*|x-y|^β)(σ:ℝ≥0)(hσ:0<σ)(j:ℕ)(x y:ℝ):
    |heat σ (ScalarHeatBands.band a (j+1)) y-heat σ (ScalarHeatBands.band a (j+1)) x|≤
      (2*H*constant β)*CompactMollifier.radius (j+1)^β*
        decay (CompactMollifier.radius (j+1)) σ ((2-β)/2)*
        min 1 (|y-x|/CompactMollifier.radius (j+1)):=by
  let r:=CompactMollifier.radius (j+1)
  let g:=heat σ (ScalarHeatBands.band a (j+1))
  let d:=decay r σ ((2-β)/2)
  let G:=H*constant β*r^β*d
  have hr:0<r:=CompactMollifier.radius_pos (j+1)
  have hs:0<(σ:ℝ):=by exact_mod_cast hσ
  have hd:0≤d:=le_min (by norm_num) (rpow_nonneg (div_nonneg hs.le (sq_nonneg r)) _)
  have hG:0≤G:=mul_nonneg (mul_nonneg (mul_nonneg hH (constant_nonneg β)) (rpow_nonneg hr.le _)) hd
  have hb(z:ℝ):|g z|≤G:=root_bound ha hB hH hβ hβ1 hh σ hσ j z
  have hder(z:ℝ):|deriv g z|≤H*constant β*r^(β-1)*d:=by
    have he:=ScalarHeatBandEnvelope.jet_bound ha hH hβ hβ1 hh σ hσ j 0 z
    simp only [Nat.cast_zero,sub_zero,zero_add,Nat.zero_add,iteratedDeriv_one] at he
    have hdec:=ScalarHeatGradientDifference.decay_order hr hs (show 0≤(2-β)/2 by linarith)
      (show (2-β)/2≤(3-β)/2 by linarith)
    have hc:ScalarHeatBandEnvelope.constant β 0≤constant β:=by
      unfold constant
      linarith [gaussianAbsMoment_nonneg β,ScalarGaussianJetScale.constant_nonneg β 1]
    exact he.trans ((mul_le_mul_of_nonneg_left hdec
      (mul_nonneg (mul_nonneg hH (ScalarHeatBandEnvelope.constant_nonneg β 0)) (rpow_nonneg hr.le (β-1)))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hH)
        (rpow_nonneg hr.le (β-1))) hd))
  have hgs:BoundedSmooth g:=heat_boundedSmooth σ (ScalarHeatBands.band_boundedSmooth ha (j+1))
  have hlip:=Convex.norm_image_sub_le_of_norm_deriv_le (s:=univ)
    (fun z _=>hgs.smooth.differentiable (by simp) z)
    (fun z _=>show ‖deriv g z‖≤H*constant β*r^(β-1)*d by simpa only [Real.norm_eq_abs] using hder z)
    convex_univ (mem_univ x) (mem_univ y)
  have hpow:r^(β-1)=r^β/r:=Real.rpow_sub_one hr.ne' β
  have hlarge:|g y-g x|≤2*G*(|y-x|/r):=by
    simp only [Real.norm_eq_abs] at hlip
    rw [hpow] at hlip
    have hratio:0≤|y-x|/r:=div_nonneg (abs_nonneg _) hr.le
    have hlo:|g y-g x|≤G*(|y-x|/r):=by
      simpa only [G,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hlip
    exact hlo.trans (by nlinarith [mul_nonneg hG hratio])
  have hsmall:|g y-g x|≤2*G:=(abs_sub _ _).trans ((add_le_add (hb y) (hb x)).trans_eq (by ring))
  have heq:(2*H*constant β)*r^β*d=2*G:=by dsimp only [G];ring
  change _≤(2*H*constant β)*r^β*d*min 1 (|y-x|/r)
  rw [heq,mul_min_of_nonneg _ _ (mul_nonneg (by norm_num) hG),mul_one]
  exact le_min hsmall hlarge

end SHE.GaussianHeatBandRootEnvelope
