module

public import SHE.NativeCurrentPathEnergy
public import SHE.NativePathZeroExtension
public import SHE.ScalarHeatSubprobabilityOpen
public import SHE.ControlledVarianceGammaTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.NativeMovingCurrentGamma
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatObservation DyadicApproximation
open ScalarGaussianSemigroup SmoothCylinders ControlledProfile
open scoped NNReal ENNReal
local instance nativeMovingCurrentGamma_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeMovingCurrentGamma_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeMovingCurrentGamma_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev space (Ω : Type*) := (ℝ×Ω)×HeatCircle

def current (U : ℝ×Ω→RealL2) (h : ℝ) (p : ℝ×space Ω) : ℝ:=
  functional p.1 p.2.2 (U (p.2.1.1+h-p.1,p.2.1.2))
def correction (D : ℝ×Ω→RealL2) (Λ h : ℝ) (p : ℝ×space Ω) : ℝ:=
  NativeCurrentPathEnergy.direction D Λ (h-p.1) p.1 p.2

theorem current_measurable (U : ℝ×Ω→RealL2) (hU : Measurable U) (h : ℝ) : Measurable (current U h):=by
  have ht : Measurable (fun p : ℝ×space Ω=>(p.2.1.1+h-p.1,p.2.1.2)):=
    ((measurable_snd.fst.fst.add_const h).sub measurable_fst).prodMk measurable_snd.fst.snd
  have hc:=functional_joint_measurable.comp
    ((hU.comp ht).prodMk (measurable_fst.prodMk measurable_snd.snd))
  change Measurable (fun p : ℝ×space Ω=>functional p.1 p.2.2 (U (p.2.1.1+h-p.1,p.2.1.2))) at hc
  exact hc

theorem correction_measurable (D : ℝ×Ω→RealL2) (hD : Measurable D) (Λ h : ℝ) : Measurable (correction D Λ h):=by
  have ht : Measurable (fun p : ℝ×space Ω=>(p.2.1.1+(h-p.1),p.2.1.2)):=
    (measurable_snd.fst.fst.add (measurable_const.sub measurable_fst)).prodMk measurable_snd.fst.snd
  have h0:=functional_joint_measurable.comp
    ((hD.comp ht).prodMk (measurable_fst.prodMk measurable_snd.snd))
  have h1:=functional_joint_measurable.comp
    ((hD.comp measurable_snd.fst).prodMk
      ((((measurable_const (a:=h)).sub measurable_fst).add measurable_fst).prodMk measurable_snd.snd))
  have hc : Measurable (fun p : ℝ×space Ω=>exp (-Λ*(h-p.1))*(1-exp (-Λ*p.1))) := by fun_prop
  exact h0.sub (hc.mul h1)

/-- The actual canonical remaining variance with the past input indexed
by the original moving past, expressed in its exact relative clock. -/
def variance (P : CanonicalCovariance.ProfileParameters) (U D : ℝ×Ω→RealL2)
    (Λ h ξ : ℝ) (p : ℝ×space Ω) : ℝ:=
  ControlledScalarCovarianceTailEnergy.field P Λ 0 h ξ
    (((embed (U p.2.1),embed (D p.2.1)),h-p.1),p.2.2)

theorem variance_measurable (P : CanonicalCovariance.ProfileParameters) (U D : ℝ×Ω→RealL2)
    (hU : Measurable U) (hD : Measurable D) (Λ h ξ : ℝ) : Measurable (variance P U D Λ h ξ):=by
  exact (ControlledScalarCovarianceTailEnergy.field_measurable P Λ 0 h ξ).comp
    (((((embed.continuous.measurable.comp hU).comp measurable_snd.fst).prodMk
      ((embed.continuous.measurable.comp hD).comp measurable_snd.fst)).prodMk
        (measurable_const.sub measurable_fst)).prodMk measurable_snd.snd)

/-- Complete-Gamma current displacement, with ORIGINAL moving-past
integration before clipping. Its gain uses true integrated D energy.
The actual canonical covariance, native roots, endpoint integrability
and both time faces are all discharged. -/
theorem energy (μ : Measure Ω) [IsProbabilityMeasure μ] (P : CanonicalCovariance.ProfileParameters)
    (U D : ℝ×Ω→RealL2) (hU : Measurable U) (hD : Measurable D)
    (hi : Integrable (fun z=>‖D z‖^2) ((volume : Measure ℝ).prod μ))
    {Λ h W ρ A : ℝ} (hΛ : 0≤Λ) (hh0 : 0<h) (hh1 : h≤1) (hW0 : 0≤W) (hW1 : W≤1)
    (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2)
    {a : ℝ→ℝ} (ha : BoundedSmooth a) (hA : 0≤A)
    (hholder : ∀ x y,|a x-a y|≤A*|x-y|^P.exponent) (ξ : ℝ) (j : ℕ) :
    let ν:=((volume.restrict (Ioc (0:ℝ) W)).prod μ).prod (haarAddCircle (T:=2*π))
    let σ:=variance P U D Λ h ξ
    let x:=current U h
    let y:=fun p=>x p+correction D Λ h p
    let g:=fun p=>deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
      deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
    let r:=CompactMollifier.radius (j+1)
    IntegrableOn (fun τ=>τ^(ρ-1/2)*(∫ z,|g (τ,z)|^2 ∂ν)) (Ioc 0 h) ∧
      (∫τ in Ioc 0 h,τ^(ρ-1/2)*(∫z,|g (τ,z)|^2 ∂ν))≤
        (2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
          ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
            r^(2*P.exponent+4*ρ)*min 1 ((4*∫z,‖D z‖^2 ∂((volume : Measure ℝ).prod μ))/r^2) := by
  intro ν σ x y g r
  have hν : ν≤(((volume : Measure ℝ).prod μ).prod haarAddCircle):=
    Measure.prod_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) le_rfl
  have hmass : ν.real univ≤1:=by
    have he : ν.real univ=W:=by
      change ((((volume.restrict (Ioc (0:ℝ) W)).prod μ).prod (haarAddCircle (T:=2*π))) univ).toReal=W
      rw [←univ_prod_univ,Measure.prod_prod]
      simp only [measure_univ,mul_one]
      rw [←univ_prod_univ,Measure.prod_prod]
      simp [Measure.restrict_apply_univ,Real.volume_Ioc,hW0]
    rw [he]
    exact hW1
  have hdisp (τ : ℝ) (ht : τ∈Ioo (0:ℝ) h) :
      Integrable (fun z=>(y (τ,z)-x (τ,z))^2) ν ∧
        (∫z,(y (τ,z)-x (τ,z))^2 ∂ν)≤4*∫z,‖D z‖^2 ∂((volume : Measure ℝ).prod μ):=by
    have he:=NativeCurrentPathEnergy.energy μ D hD hi hΛ (by linarith [ht.2] : 0≤h-τ) ht.1
    have hid:=he.1.mono_measure hν
    have hle:=(integral_mono_measure hν (ae_of_all _ (fun _=>sq_nonneg _)) he.1).trans he.2
    simpa only [y,x,Pi.add_apply,add_sub_cancel_left,correction] using And.intro hid hle
  have hlo (τ : ℝ) (ht : τ∈Ioo (0:ℝ) h) :
      ∀ᵐz∂ν,ProfileVariance.lowerConstant*P.lower*sqrt τ≤σ (τ,z):=by
    apply ae_of_all
    intro z
    change _≤ControlledScalarCovarianceTailEnergy.field P Λ 0 h ξ
      (((embed (U z.1),embed (D z.1)),h-τ),z.2)
    unfold ControlledScalarCovarianceTailEnergy.field ControlledScalarCovarianceTail.tail
    rw [min_eq_left (by linarith [ht.1] : h-τ≤h)]
    have hc:=ControlledReferenceWindows.coefficient_section_measurable P Λ ξ 0 (embed (U z.1),embed (D z.1))
    have he:=ScalarCovarianceTailScale.elliptic hc (by linarith [ht.1] : h-τ<h)
      (by linarith [ht.2]) P.lower_pos.le P.upper_nonneg
      (ControlledReferenceWindows.coefficient_bounds P Λ ξ 0 (embed (U z.1),embed (D z.1))) z.2
    convert he.1 using 1 <;> simp only [ControlledReferenceWindows.coefficient,show h-(h-τ)=τ by ring,Real.sqrt_eq_rpow]
    rfl
  exact ScalarHeatSubprobabilityOpen.energy ν hmass ha hA P.exponent_pos.le P.exponent_le_one
    hρ0 hρ1 (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos)
    (mul_nonneg (by norm_num) (integral_nonneg (fun _=>sq_nonneg _))) hholder
    σ x y (variance_measurable P U D hU hD Λ h ξ) (current_measurable U hU h)
    ((current_measurable U hU h).add (correction_measurable D hD Λ h)) hlo
    (fun τ ht=>(hdisp τ ht).1) (fun τ ht=>(hdisp τ ht).2) j

end SHE.NativeMovingCurrentGamma
