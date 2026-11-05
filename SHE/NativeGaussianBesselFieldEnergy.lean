module
public import SHE.NativeGaussianBesselEnergy
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeGaussianBesselFieldEnergy
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]

/-- Bounded genuine scalar fields have the actual canonical native
Hilbert realization; no spatial or sample integrability is supplied. -/
theorem bound {s L Λ ρ η B A0:ℝ}(hs:1<s)(hL:0<L)(hΛ:1≤Λ)
    (hρ:0<ρ)(hρhalf:ρ<1/2)(hη:0≤η)(hB:0≤B)(hA0:0≤A0)
    (F A:Ω×HeatCircle→ℝ)(hF:Measurable F)(hA:Measurable A)
    (hFb:∀p,|F p|≤B)(hAb:∀p,|A p|≤A0)
    (hcov:∀ᵐz:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      BoundedSpatialCovariance.value μ F z≤
        (NativeGaussianCircleMass.G s L z+η)*BoundedSpatialCovariance.value μ A z):
    let Fc:=fun p=>(F p:ℂ)
    Integrable (fun ω=>‖NativeBesselFieldAE.value Λ ρ hΛ hρ.le Fc ω‖^2) μ ∧
    (∫ω,‖NativeBesselFieldAE.value Λ ρ hΛ hρ.le Fc ω‖^2 ∂μ)≤
      NativeGaussianBesselCost.bound s L Λ ρ η*(∫ω,∫x:HeatCircle,A (ω,x)^2 ∂haarAddCircle ∂μ):=by
  intro Fc
  have hFc:Measurable Fc:=Complex.measurable_ofReal.comp hF
  let f:=MeasurableL2FieldAE.realization haarAddCircle Fc
  have hfm:Measurable f:=MeasurableL2FieldAE.realization_measurable haarAddCircle Fc hFc
  have hsq(ω:Ω):Integrable (fun x:HeatCircle=>‖Fc (ω,x)‖^2) haarAddCircle:=by
    apply (integrable_const (B^2)).mono'
      (((hFc.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change ‖(F (ω,x):ℂ)‖^2≤B^2
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hFb (ω,x)) 2
  have hf(ω:Ω):(f ω:HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>(F (ω,x):ℂ):=by
    apply MeasurableL2FieldAE.realization_ae haarAddCircle Fc hFc
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x=>sq_nonneg ‖Fc (ω,x)‖))).mp (hsq ω).hasFiniteIntegral
  have hn(ω:Ω):‖f ω‖^2≤B^2:=by
    rw [L2_norm_sq_eq_integral]
    calc
      _=(∫x:HeatCircle,‖Fc (ω,x)‖^2 ∂haarAddCircle):=
        integral_congr_ae ((hf ω).mono (fun x hx=>congrArg (fun z:ℂ=>‖z‖^2) hx))
      _≤∫x:HeatCircle,B^2 ∂haarAddCircle:=by
        apply integral_mono_ae (hsq ω) (integrable_const _)
        filter_upwards with x
        change ‖(F (ω,x):ℂ)‖^2≤B^2
        rw [Complex.norm_real,Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hFb (ω,x)) 2
      _=B^2:=by simp
  have hfi:Integrable (fun ω=>‖f ω‖^2) μ:=by
    apply (integrable_const (B^2)).mono' (hfm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f ω‖)]
    exact hn ω
  exact NativeGaussianBesselEnergy.bound μ hs hL hΛ hρ hρhalf hη hB hA0 f F A hfm hfi hF hA hFb hAb
    (ae_of_all _ hf) hcov
end SHE.NativeGaussianBesselFieldEnergy
