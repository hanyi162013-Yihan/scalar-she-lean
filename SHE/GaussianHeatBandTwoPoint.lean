module
public import SHE.GaussianHeatBandRootEnvelope
public import SHE.GaussianHeatBandTranslations
public import SHE.GaussianTwoPointReserve

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.GaussianHeatBandTwoPoint
open Set MeasureTheory ProbabilityTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup
open GaussianConvolution WordRecursion ScalarHeatBandEnvelope
open scoped NNReal ENNReal

/-- A full correlated two-point Gaussian law has the actual polynomial
Gaussian-band cancellation and BOTH root displacement minima. The
independent reserve is derived from the supplied PSD subtraction. -/
theorem bound {a:ℝ→ℝ}(ha:BoundedSmooth a){B H β:ℝ}
    (hB:∀x,|a x|≤B)(hH:0≤H)(hβ:0≤β)(hβ1:β≤1)
    (hh:∀x y,|a x-a y|≤H*|x-y|^β)
    (A:Matrix (Fin 2) (Fin 2) ℝ)(σ:ℝ≥0)(hσ:0<σ)
    (hres:(A-GaussianTwoPointReserve.covariance σ).PosSemidef)
    (j:ℕ)(u w m:State 2):
    |gaussianAverage A
      (fun z=>GaussianHeatBandTranslations.difference a j (u 0) (w 0) (z 0)*
        GaussianHeatBandTranslations.difference a j (u 1) (w 1) (z 1)) m|≤
      ((2*H*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
        decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2*
        min 1 (|u 0-w 0|/CompactMollifier.radius (j+1))*
        min 1 (|u 1-w 1|/CompactMollifier.radius (j+1)):=by
  let r:=CompactMollifier.radius (j+1)
  let D:=(2*H*GaussianHeatBandRootEnvelope.constant β)*r^β*decay r σ ((2-β)/2)
  let f:=GaussianHeatBandTranslations.difference a j (u 0) (w 0)
  let g:=GaussianHeatBandTranslations.difference a j (u 1) (w 1)
  let c0:=min 1 (|u 0-w 0|/r)
  let c1:=min 1 (|u 1-w 1|/r)
  have hr:0<r:=CompactMollifier.radius_pos (j+1)
  have hD:0≤D:=mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) (GaussianHeatBandRootEnvelope.constant_nonneg β))
      (rpow_nonneg hr.le β))
    (le_min (by norm_num) (rpow_nonneg (div_nonneg σ.2 (sq_nonneg r)) _))
  have hc0:0≤c0:=le_min (by norm_num) (div_nonneg (abs_nonneg _) hr.le)
  have hc1:0≤c1:=le_min (by norm_num) (div_nonneg (abs_nonneg _) hr.le)
  have hheat(i:Fin 2)(x:ℝ):
      |heat σ (GaussianHeatBandTranslations.difference a j (u i) (w i)) x|≤D*min 1 (|u i-w i|/r):=by
    rw [GaussianHeatBandTranslations.heat_difference ha]
    have he:=GaussianHeatBandRootEnvelope.difference ha hB hH hβ hβ1 hh σ hσ j (x+w i) (x+u i)
    simpa only [add_sub_add_left_eq_sub] using he
  have hBb:0≤B:=(abs_nonneg (a 0)).trans (hB 0)
  have he:=GaussianTwoPointReserve.bound hres σ f g
    (GaussianHeatBandTranslations.measurable ha j _ _) (GaussianHeatBandTranslations.measurable ha j _ _)
    (Bf:=4*B) (Bg:=4*B) (Uf:=D*c0) (Ug:=D*c1)
    (mul_nonneg (by norm_num) hBb) (mul_nonneg (by norm_num) hBb)
    (GaussianHeatBandTranslations.bounded hB j _ _) (GaussianHeatBandTranslations.bounded hB j _ _)
    (mul_nonneg hD hc0) (mul_nonneg hD hc1) (hheat 0) (hheat 1) m
  rw [sub_add_cancel] at he
  exact he.trans_eq (by change (D*c0)*(D*c1)=D^2*c0*c1;ring)

end SHE.GaussianHeatBandTwoPoint
