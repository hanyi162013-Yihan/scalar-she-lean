module
public import SHE.NativeGaussianBesselCost
public import SHE.NativeGaussianCovarianceEnergy
public import SHE.NativeBesselExpectation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeGaussianBesselEnergy
open Set MeasureTheory Real AddCircle StoppedFourier NativeGaussianCovarianceKernel
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]

/-- True native Bessel energy from uncentered covariance, with the exact
positive Laplace normalization and the explicit finite-window floor. -/
theorem bound {s L Λ ρ η B A0:ℝ}(hs:1<s)(hL:0<L)(hΛ:1≤Λ)
    (hρ:0<ρ)(hρhalf:ρ<1/2)(hη:0≤η)(hB:0≤B)(hA0:0≤A0)
    (f:Ω→CircleL2)(F A:Ω×HeatCircle→ℝ)(hfm:Measurable f)
    (hfi:Integrable (fun ω=>‖f ω‖^2) μ)
    (hF:Measurable F)(hA:Measurable A)(hFb:∀p,|F p|≤B)(hAb:∀p,|A p|≤A0)
    (hf:∀ᵐω∂μ,(f ω:HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>(F (ω,x):ℂ))
    (hcov:∀ᵐz:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      BoundedSpatialCovariance.value μ F z≤
        (NativeGaussianCircleMass.G s L z+η)*BoundedSpatialCovariance.value μ A z):
    Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) μ ∧
    (∫ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2 ∂μ)≤
      NativeGaussianBesselCost.bound s L Λ ρ η*(∫ω,∫x:HeatCircle,A (ω,x)^2 ∂haarAddCircle ∂μ):=by
  let EA:ℝ:=∫ω,∫x:HeatCircle,A (ω,x)^2 ∂haarAddCircle ∂μ
  have hEA:0≤EA:=integral_nonneg (fun _=>integral_nonneg (fun _=>sq_nonneg _))
  have hΛ0:0<Λ:=zero_lt_one.trans_le hΛ
  have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
  have hiB:Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) μ:=by
    apply hfi.mono' (((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).continuous.measurable.comp hfm).norm.pow_const 2).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ.le _) 2
  have hiH(t:ℝ)(ht:0<t):Integrable (fun ω=>‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2) μ:=by
    apply hfi.mono' (((circleHeatOperator (t/2) (by positivity)).continuous.measurable.comp hfm).norm.pow_const 2).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (circleHeatOperator_norm_le _ (by positivity) _) 2
  obtain ⟨hic,hbc⟩:=NativeGaussianBesselCost.integral_bound hs hL hΛ0 hρ hρhalf hη
  have hip:IntegrableOn (fun t=>NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ*cost s L t η*EA) (Ioi 0):=
    hic.mul_const EA
  have hnn:∀ᵐt:ℝ∂volume.restrict (Ioi 0),
      0≤NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ*cost s L t η*EA:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (div_nonneg
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)) hg.le)
      (NativeGaussianBesselCost.cost_nonneg hs hL.le ht hη)) hEA
  have hlin:(∫⁻ω,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) ∂μ)≤
      ∫⁻t in Ioi (0:ℝ),ENNReal.ofReal
        (NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ*cost s L t η*EA):=by
    rw [NativeBesselExpectation.energy μ f hfm Λ ρ hΛ hρ]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he:(∫⁻ω,NativeBesselHeatEnergy.heatMass t (f ω) ∂μ)=
        ENNReal.ofReal (∫ω,‖circleHeatOperator (t/2) (div_nonneg ht.le (by norm_num)) (f ω)‖^2 ∂μ):=by
      simp_rw [NativeBesselHeatEnergy.heat_norm t ht.le]
      exact (ofReal_integral_eq_lintegral_ofReal (hiH t ht) (ae_of_all _ (fun _=>sq_nonneg _))).symm
    rw [he]
    have hb:=NativeGaussianCovarianceEnergy.bound μ hs hL ht hη hB hA0 f F A hF hA hFb hAb hf hcov
    have hw0:0≤NativeBesselSchurIntegral.weight ρ Λ t:=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
    have hk:NativeBesselLaplace.kernel ρ Λ t=
        ENNReal.ofReal (NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ):=by
      unfold NativeBesselLaplace.kernel NativeBesselSchurIntegral.weight
      rw [ENNReal.ofReal_div_of_pos hg]
      rfl
    rw [hk]
    calc
      _≤ENNReal.ofReal (NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ)*
          ENNReal.ofReal (cost s L t η*EA):=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hb) (by exact zero_le)
      _=_:=by rw [←ENNReal.ofReal_mul (div_nonneg hw0 hg.le)];congr 1;ring
  rw [←ofReal_integral_eq_lintegral_ofReal hiB (ae_of_all _ (fun _=>sq_nonneg _)),
    ←ofReal_integral_eq_lintegral_ofReal hip hnn,integral_mul_const] at hlin
  have hcost0:0≤(∫t in Ioi (0:ℝ),NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ*cost s L t η):=by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)) hg.le)
      (NativeGaussianBesselCost.cost_nonneg hs hL.le ht hη)
  have hr: (∫ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2 ∂μ)≤
      (∫t in Ioi (0:ℝ),NativeBesselSchurIntegral.weight ρ Λ t/Real.Gamma ρ*cost s L t η)*EA:=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcost0 hEA)).mp hlin
  exact ⟨hiB,hr.trans (mul_le_mul_of_nonneg_right hbc hEA)⟩
end SHE.NativeGaussianBesselEnergy
