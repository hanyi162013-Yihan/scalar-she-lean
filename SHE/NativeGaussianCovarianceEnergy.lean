module
public import SHE.NativeGaussianCovarianceKernel
public import SHE.NativeHeatCovariance
public import SHE.AveragedPositiveKernelSchur
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeGaussianCovarianceEnergy
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatQuadratic NativeGaussianCovarianceKernel
open BoundedSpatialCovariance
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]

/-- Concrete native heat covariance estimate with both actual random
spatial displacement amplitudes. Only the covariance inequality itself
is left for the original-J conditional Gaussian law to establish. -/
theorem bound {s L t η B A0:ℝ}(hs:1<s)(hL:0<L)(ht:0<t)(hη:0≤η)
    (hB:0≤B)(hA0:0≤A0)(f:Ω→CircleL2)(F A:Ω×HeatCircle→ℝ)
    (hF:Measurable F)(hA:Measurable A)(hFb:∀p,|F p|≤B)(hAb:∀p,|A p|≤A0)
    (hf:∀ᵐω∂μ,(f ω:HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>(F (ω,x):ℂ))
    (hcov:∀ᵐz:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      value μ F z≤(NativeGaussianCircleMass.G s L z+η)*value μ A z):
    (∫ω,‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2 ∂μ)≤
      cost s L t η*(∫ω,∫x:HeatCircle,A (ω,x)^2 ∂haarAddCircle ∂μ):=by
  let C:ℝ:=1+heatConstant*(t/2)^(-(1/2:ℝ))
  have hC:0≤C:=by
    dsimp [C]
    exact add_nonneg (by norm_num) (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (by positivity) _))
  have hmass:0≤NativeGaussianCircleMass.mass s L:=by
    have hsm:0<s-1:=by linarith
    unfold NativeGaussianCircleMass.mass
    positivity
  have hcost:0≤cost s L t η:=by
    exact add_nonneg (le_min (by norm_num) (mul_nonneg hC hmass)) hη
  have hiF:Integrable (fun z:HeatCircle×HeatCircle=>K t ht z*value μ F z)
      (haarAddCircle.prod haarAddCircle):=by
    apply BoundedSpatialCovariance.integrable _ _
      ((measurable_K ht).mul (BoundedSpatialCovariance.measurable μ F hF)) (C*B^2)
    intro z
    change ‖K t ht z*value μ F z‖≤C*B^2
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (show 0≤K t ht z from norm_nonneg _)]
    exact mul_le_mul (K_bound ht z) (norm_bound μ F hB hFb z) (norm_nonneg _) hC
  have hiA:Integrable (fun z:HeatCircle×HeatCircle=>Q s L t η ht z*value μ A z)
      (haarAddCircle.prod haarAddCircle):=by
    apply BoundedSpatialCovariance.integrable _ _
      ((NativeGaussianCovarianceKernel.measurable s L t η ht).mul
        (BoundedSpatialCovariance.measurable μ A hA)) (sup t η*A0^2)
    intro z
    change ‖Q s L t η ht z*value μ A z‖≤sup t η*A0^2
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (NativeGaussianCovarianceKernel.nonneg hL.le hη ht z)]
    exact mul_le_mul (NativeGaussianCovarianceKernel.bounded hL.le hη ht z)
      (norm_bound μ A hA0 hAb z) (norm_nonneg _) (sup_nonneg ht hη)
  rw [NativeHeatCovariance.energy μ ht f F hF hB hFb hf]
  change (∫z:HeatCircle×HeatCircle,K t ht z*value μ F z ∂haarAddCircle.prod haarAddCircle)≤_
  calc
    _≤∫z:HeatCircle×HeatCircle,Q s L t η ht z*value μ A z ∂haarAddCircle.prod haarAddCircle:=by
      apply integral_mono_ae hiF hiA
      filter_upwards [hcov] with z hz
      exact (mul_le_mul_of_nonneg_left hz (show 0≤K t ht z from norm_nonneg _)).trans_eq (by dsimp [Q];ring)
    _≤_:=AveragedPositiveKernelSchur.bound μ haarAddCircle (Q s L t η ht)
      (NativeGaussianCovarianceKernel.measurable s L t η ht) (sup_nonneg ht hη) hcost hA0
      (NativeGaussianCovarianceKernel.nonneg hL.le hη ht) (NativeGaussianCovarianceKernel.bounded hL.le hη ht)
      (row hs hL hη ht) (col hs hL hη ht) A hA hAb

end SHE.NativeGaussianCovarianceEnergy
