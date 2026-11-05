module
public import SHE.GaussianSeparatedCoordinates
public import SHE.GaussianHeatBandTwoPoint

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.GaussianSeparatedBand
open Set MeasureTheory ProbabilityTheory WordRecursion GaussianConvolution GaussianCoordinates
open GaussianHeatBandTranslations ScalarHeatBandEnvelope
open scoped NNReal ENNReal

def additive:Fin 2→Fin 6:=Fin.castAdd 4
def residual:Fin 4→Fin 6:=Fin.natAdd 2

def pair (a:ℝ→ℝ) (j:ℕ) (z:State 6):ℝ:=
  (ScalarHeatBands.band a (j+1) (z 0+z 2)-ScalarHeatBands.band a (j+1) (z 0+z 4))*
    (ScalarHeatBands.band a (j+1) (z 1+z 3)-ScalarHeatBands.band a (j+1) (z 1+z 5))

def amplitude (j:ℕ) (z:State 6):ℝ:=
  min 1 (|z 2-z 4|/CompactMollifier.radius (j+1))*
    min 1 (|z 3-z 5|/CompactMollifier.radius (j+1))

theorem amplitude_nonneg (j:ℕ) (z:State 6):0≤amplitude j z:=
  mul_nonneg (le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le))
    (le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le))

theorem amplitude_le_one (j:ℕ) (z:State 6):amplitude j z≤1:=by
  exact (mul_le_mul (min_le_left _ _) (min_le_left _ _)
    (le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le)) zero_le_one).trans_eq (by ring)

/-- Polynomial cancellation applies only to the genuine independent
additive block. Every residual cross covariance and BOTH displacement
minima remain in the same Gaussian expectation. -/
theorem bound {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){B H β:ℝ}
    (hB:∀x,|a x|≤B)(hH:0≤H)(hβ:0≤β)(hβ1:β≤1)
    (hh:∀x y,|a x-a y|≤H*|x-y|^β)
    (A:Matrix (Fin 6) (Fin 6) ℝ) (hA:A.PosSemidef)
    (hc:∀i:Fin 4,∀j:Fin 2,A (residual i) (additive j)=0)
    (σ:ℝ≥0) (hσ:0<σ)
    (hres:(A.submatrix additive additive-GaussianTwoPointReserve.covariance σ).PosSemidef)
    (j:ℕ) (m:State 6):
    |gaussianAverage A (pair a j) m|≤
      ((2*H*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
        decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2*
      gaussianAverage A (amplitude j) m:=by
  have hb:Measurable (ScalarHeatBands.band a (j+1)):=(ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable
  let U:State 4→State 2:=fun y=>WithLp.toLp 2 ![m 2+y 0,m 3+y 1]
  let W:State 4→State 2:=fun y=>WithLp.toLp 2 ![m 4+y 2,m 5+y 3]
  let am:State 2:=projection additive m
  let Hf:State 4×State 2→ℝ:=fun z=>
    difference a j (U z.1 0) (W z.1 0) (am 0+z.2 0)*
      difference a j (U z.1 1) (W z.1 1) (am 1+z.2 1)
  let Hm:State 4×State 2→ℝ:=fun z=>
    min 1 (|U z.1 0-W z.1 0|/CompactMollifier.radius (j+1))*
      min 1 (|U z.1 1-W z.1 1|/CompactMollifier.radius (j+1))
  have hU:Continuous U:=by
    unfold U
    apply (PiLp.continuous_toLp 2 (fun _:Fin 2=>ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one] <;> fun_prop
  have hW:Continuous W:=by
    unfold W
    apply (PiLp.continuous_toLp 2 (fun _:Fin 2=>ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one] <;> fun_prop
  have hfm:Measurable Hf:=by unfold Hf difference;fun_prop
  have hmm:Measurable Hm:=by unfold Hm U W;fun_prop
  have hB0:0≤B:=(abs_nonneg (a 0)).trans (hB 0)
  have hfb:∀z,|Hf z|≤(4*B)^2:=by
    intro z
    rw [abs_mul]
    exact (mul_le_mul (GaussianHeatBandTranslations.bounded hB j _ _ _)
      (GaussianHeatBandTranslations.bounded hB j _ _ _) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hmb:∀z,|Hm z|≤1:=by
    intro z
    have hn:0≤Hm z:=mul_nonneg
      (le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le))
      (le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le))
    rw [abs_of_nonneg hn]
    exact (mul_le_mul (min_le_left _ _) (min_le_left _ _)
      (le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le)) zero_le_one).trans_eq (by ring)
  have hf:=GaussianSeparatedCoordinates.integral_product residual additive hA hc Hf hfm hfb
  have hm:=GaussianSeparatedCoordinates.integral_product residual additive hA hc Hm hmm hmb
  have hfe:(fun z:State 6=>pair a j (m+z))=fun z=>Hf (projection residual z,projection additive z):=by
    funext z
    rfl
  have hme:(fun z:State 6=>amplitude j (m+z))=fun z=>Hm (projection residual z,projection additive z):=by
    funext z
    rfl
  change |∫z:State 6,pair a j (m+z) ∂multivariateGaussian 0 A|≤_
  rw [hfe,hf]
  change _≤_*(∫z:State 6,amplitude j (m+z) ∂multivariateGaussian 0 A)
  rw [hme,hm]
  let D:=((2*H*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
    decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2
  have hD:0≤D:=sq_nonneg _
  let ν:=multivariateGaussian (0:State 4) (A.submatrix residual residual)
  have him:Integrable (fun y:State 4=>D*Hm (y,0)) ν:=by
    apply (integrable_const D).mono' (measurable_const.mul (hmm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    filter_upwards with y
    change ‖D*Hm (y,0)‖≤D
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hD]
    exact (mul_le_mul_of_nonneg_left (hmb (y,0)) hD).trans_eq (by ring)
  have hn:=norm_integral_le_of_norm_le (μ:=ν)
    (f:=fun y:State 4=>∫x:State 2,Hf (y,x) ∂multivariateGaussian 0 (A.submatrix additive additive)) him
    (ae_of_all _ (fun y=>by
      have he:=GaussianHeatBandTwoPoint.bound ha hB hH hβ hβ1 hh
        (A.submatrix additive additive) σ hσ hres j (U y) (W y) am
      simpa only [Real.norm_eq_abs,gaussianAverage,Hf,Hm,D,PiLp.add_apply,mul_assoc] using he))
  rw [integral_const_mul] at hn
  simpa only [Real.norm_eq_abs,Hm,integral_const,probReal_univ,one_smul] using hn

end SHE.GaussianSeparatedBand
