module
public import SHE.GaussianStandardRealization
public import SHE.GaussianSeparatedBand

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.GaussianMixtureBand
open Set MeasureTheory ProbabilityTheory WordRecursion GaussianContinuity GaussianConvolution
open GaussianSeparatedBand ScalarHeatBandEnvelope
open scoped NNReal ENNReal
variable {X Ω:Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]
variable (μ:Measure Ω) [IsProbabilityMeasure μ]
variable {n:ℕ} (C:X→PositiveCovariance n) (m:X→State n)
variable (hC:Continuous C) (hm:Continuous m) (u:Ω→X) (hu:Measurable u)

include hC hm hu in
theorem integral_eq (Y:Ω→State n)
    (hY:HasLaw Y ((μ.prod (stdGaussian (State n))).map (GaussianStandardRealization.simulated C m u)) μ)
    (F:State n→ℝ) (hF:Continuous F) {B:ℝ} (hB:∀z,‖F z‖≤B):
    (∫ω,F (Y ω) ∂μ)=∫ω,gaussianAverage (C (u ω)).val F (m (u ω)) ∂μ:=by
  have hs:=GaussianStandardRealization.simulated_measurable C m hC hm u hu
  have he:=hY.integral_comp (f:=F) hF.measurable.aestronglyMeasurable
  change (∫ω,F (Y ω) ∂μ)=_ at he
  rw [integral_map hs.aemeasurable hF.measurable.aestronglyMeasurable] at he
  have hi:Integrable (fun z:Ω×State n=>F (GaussianStandardRealization.simulated C m u z))
      (μ.prod (stdGaussian (State n))):=
    (integrable_const B).mono' (hF.measurable.comp hs).aestronglyMeasurable
      (ae_of_all _ (fun z=>hB _))
  rw [integral_prod _ hi] at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω=>(GaussianStandardRealization.average C m (u ω) F hF).symm)

variable {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {B H β:ℝ}
variable (hB:∀x,|a x|≤B) (hH:0≤H) (hβ:0≤β) (hβ1:β≤1)
variable (hh:∀x y,|a x-a y|≤H*|x-y|^β)

include ha hB hH hβ hβ1 hh in
/-- The sharp uncentered covariance bound keeps BOTH dependent random
root displacement minima inside the SAME original expectation. The
covariance may depend on arbitrary past data. -/
theorem bound (C:X→PositiveCovariance 6) (m:X→State 6)
    (hC:Continuous C) (hm:Continuous m) (u:Ω→X) (hu:Measurable u)
    (Y:Ω→State 6)
    (hY:HasLaw Y ((μ.prod (stdGaussian (State 6))).map (GaussianStandardRealization.simulated C m u)) μ)
    (hc:∀p,∀i:Fin 4,∀j:Fin 2,(C p).val (residual i) (additive j)=0)
    (σ:ℝ≥0) (hσ:0<σ)
    (hres:∀p,((C p).val.submatrix additive additive-GaussianTwoPointReserve.covariance σ).PosSemidef)
    (j:ℕ):
    |∫ω,pair a j (Y ω) ∂μ|≤
      ((2*H*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
        decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2*
      ∫ω,amplitude j (Y ω) ∂μ:=by
  have hb:Continuous (ScalarHeatBands.band a (j+1)):=
    (ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous
  have hp:Continuous (pair a j):=by unfold pair;fun_prop
  have hA:Continuous (amplitude j):=by unfold amplitude;fun_prop
  have hB0:0≤B:=(abs_nonneg (a 0)).trans (hB 0)
  have hpb:∀z:State 6,‖pair a j z‖≤(4*B)^2:=by
    intro z
    change |GaussianHeatBandTranslations.difference a j (z 2) (z 4) (z 0)*
      GaussianHeatBandTranslations.difference a j (z 3) (z 5) (z 1)|≤_
    rw [abs_mul]
    exact (mul_le_mul (GaussianHeatBandTranslations.bounded hB j _ _ _)
      (GaussianHeatBandTranslations.bounded hB j _ _ _) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hab:∀z:State 6,‖amplitude j z‖≤1:=by
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (amplitude_nonneg j z)]
    exact amplitude_le_one j z
  have he:=integral_eq μ C m hC hm u hu Y hY (pair a j) hp hpb
  have hea:=integral_eq μ C m hC hm u hu Y hY (amplitude j) hA hab
  rw [he,hea]
  let D:=((2*H*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
    decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2
  have hD:0≤D:=sq_nonneg _
  let Z:X→ℝ:=fun p=>gaussianAverage (C p).val (amplitude j) (m p)
  have hZm:Measurable Z:=
    ((GaussianContinuity.continuous_gaussian_average (amplitude j) hA hab).comp
      (hC.prodMk hm)).measurable
  have hZb(p:X):‖Z p‖≤1:=by
    have hn:=norm_integral_le_of_norm_le (μ:=multivariateGaussian (0:State 6) (C p).val)
      (f:=fun z=>amplitude j (m p+z)) (integrable_const (1:ℝ))
      (ae_of_all _ (fun z=>hab _))
    simpa only [Z,gaussianAverage,integral_const,probReal_univ,one_smul] using hn
  have hi:Integrable (fun ω=>D*Z (u ω)) μ:=by
    apply (integrable_const D).mono' (measurable_const.mul (hZm.comp hu)).aestronglyMeasurable
    filter_upwards with ω
    change ‖D*Z (u ω)‖≤D
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hD]
    exact (mul_le_mul_of_nonneg_left (hZb _) hD).trans_eq (by ring)
  have hn:=norm_integral_le_of_norm_le (μ:=μ)
    (f:=fun ω=>gaussianAverage (C (u ω)).val (pair a j) (m (u ω))) hi
    (ae_of_all _ (fun ω=>by
      simpa only [Real.norm_eq_abs] using GaussianSeparatedBand.bound ha hB hH hβ hβ1 hh
        (C (u ω)).val (C (u ω)).property (hc (u ω)) σ hσ (hres (u ω)) j (m (u ω))))
  rw [integral_const_mul] at hn
  simpa only [Real.norm_eq_abs] using hn

end SHE.GaussianMixtureBand
