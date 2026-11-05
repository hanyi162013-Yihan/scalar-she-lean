module

public import SHE.InitialScalarCovarianceTail
public import SHE.NativeMovingJointGamma
public import SHE.NativeMovingCurrentGamma
public import SHE.NativePathZeroExtension
public import SHE.ScalarHeatSubprobabilityOpen
public import SHE.ControlledVarianceGammaTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.InitialJointGradientEnergy
open NativeMovingCurrentGamma
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatObservation DyadicApproximation
open ScalarGaussianSemigroup SmoothCylinders ControlledProfile
open scoped NNReal ENNReal
local instance nativeMovingCurrentGamma_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeMovingCurrentGamma_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeMovingCurrentGamma_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]


def variance(P:CanonicalCovariance.ProfileParameters)(Λ h:ℝ)(past:Ω→Inputs)
    (p:ℝ×space Ω):ℝ:=max (ProfileVariance.lowerConstant*P.lower*sqrt p.1)
      (InitialScalarCovarianceTail.field P Λ 0
        (((past p.2.1.2,p.2.1.1+h-p.1),p.2.1.1+h),p.2.2))

theorem variance_measurable(P:CanonicalCovariance.ProfileParameters)(Λ h:ℝ)(past:Ω→Inputs)
    (hp:Measurable past):Measurable (variance P Λ h past):=by
  have ht:Measurable (fun p:ℝ×space Ω=>p.2.1.1+h):=measurable_snd.fst.fst.add_const h
  have hq:Measurable (fun p:ℝ×space Ω=>p.2.1.1+h-p.1):=ht.sub measurable_fst
  have hm:Measurable (fun p:ℝ×space Ω=>(((past p.2.1.2,p.2.1.1+h-p.1),p.2.1.1+h),p.2.2)):=
    ((((hp.comp measurable_snd.fst.snd).prodMk hq).prodMk ht).prodMk measurable_snd.snd)
  have hc:Measurable (fun p:ℝ×space Ω=>ProfileVariance.lowerConstant*P.lower*sqrt p.1):=by fun_prop
  exact hc.max ((InitialScalarCovarianceTail.field_measurable P Λ 0).comp hm)

/-- Actual initial-window current gain. The terminal parameter runs over
(0,h] through v+h with v∈(-h,0]; clipping retains the true global path
energy before frequency summation. -/
theorem energy (μ:Measure Ω)[IsProbabilityMeasure μ](P:CanonicalCovariance.ProfileParameters)
    (U D:ℝ×Ω→RealL2)(hU:Measurable U)(hD:Measurable D)
    (hi:Integrable (fun z=>‖D z‖^2) ((volume:Measure ℝ).prod μ))
    (past:Ω→Inputs)(hp:Measurable past)
    {Λ h ρ A:ℝ}(hΛ:0≤Λ)(hh:0<h)(hh1:h≤1)(hρ0:-(1/2:ℝ)<ρ)(hρ1:ρ<1/2)
    {a:ℝ→ℝ}(ha:BoundedSmooth a)(hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)(j:ℕ):
    let ν:=((volume.restrict (Ioc (-h) (0:ℝ))).prod μ).prod (haarAddCircle (T:=2*π))
    let σ:=variance P Λ h past
    let x:=current U h
    let y:=fun p=>x p+NativeMovingJointGamma.direction D Λ h p
    let g:=fun p=>deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
      deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
    let r:=CompactMollifier.radius (j+1)
    IntegrableOn (fun τ=>τ^(ρ-1/2)*(∫z,|g (τ,z)|^2 ∂ν)) (Ioc 0 h) ∧
      (∫τ in Ioc 0 h,τ^(ρ-1/2)*(∫z,|g (τ,z)|^2 ∂ν))≤
        (2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
          ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
            r^(2*P.exponent+4*ρ)*min 1 ((4*∫z,‖D z‖^2 ∂((volume:Measure ℝ).prod μ))/r^2):=by
  intro ν σ x y g r
  have hν:ν≤(((volume:Measure ℝ).prod μ).prod haarAddCircle):=
    Measure.prod_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) le_rfl
  have hmass:ν.real univ≤1:=by
    have he:ν.real univ=h:=by
      change ((((volume.restrict (Ioc (-h) (0:ℝ))).prod μ).prod (haarAddCircle (T:=2*π))) univ).toReal=h
      rw [←univ_prod_univ,Measure.prod_prod]
      simp only [measure_univ,mul_one]
      rw [←univ_prod_univ,Measure.prod_prod]
      simp [Measure.restrict_apply_univ,Real.volume_Ioc,hh.le]
    rw [he]
    exact hh1
  have hdisp(τ:ℝ)(ht:τ∈Ioo (0:ℝ) h):
      Integrable (fun z=>(y (τ,z)-x (τ,z))^2) ν ∧
        (∫z,(y (τ,z)-x (τ,z))^2 ∂ν)≤4*∫z,‖D z‖^2 ∂((volume:Measure ℝ).prod μ):=by
    have hb:=NativeCurrentPathEnergy.energy μ D hD hi (Λ:=0) (by norm_num)
      (by linarith [ht.2]:0≤h-τ) ht.1
    have heB:(fun z:space Ω=>NativeCurrentPathEnergy.direction D 0 (h-τ) τ z^2)=
        (fun z:space Ω=>current D h (τ,z)^2):=by
      funext z
      simp only [NativeCurrentPathEnergy.direction,neg_zero,zero_mul,exp_zero,sub_self,mul_zero,zero_mul,sub_zero,current]
      rw [show z.1.1+(h-τ)=z.1.1+h-τ by ring]
    rw [heB] at hb
    have hbν:Integrable (fun z:space Ω=>current D h (τ,z)^2) ν:=hb.1.mono_measure hν
    have hEν:(∫z,current D h (τ,z)^2 ∂ν)≤4*∫z,‖D z‖^2 ∂((volume:Measure ℝ).prod μ):=
      (integral_mono_measure hν (ae_of_all _ (fun _=>sq_nonneg _)) hb.1).trans hb.2
    have heq:(fun z:space Ω=>(y (τ,z)-x (τ,z))^2)=
        (fun z:space Ω=>exp (-Λ*τ)^2*current D h (τ,z)^2):=by
      funext z
      simp only [y,x,add_sub_cancel_left,NativeMovingJointGamma.direction,mul_pow]
    have hI:Integrable (fun z:space Ω=>(y (τ,z)-x (τ,z))^2) ν:=by
      rw [heq]
      exact hbν.const_mul _
    refine ⟨hI,?_⟩
    rw [heq,integral_const_mul]
    have he0:0≤exp (-Λ*τ):=(exp_pos _).le
    have he1:exp (-Λ*τ)≤1:=exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) ht.1.le)
    have he2:exp (-Λ*τ)^2≤1:=by nlinarith
    exact (mul_le_of_le_one_left (integral_nonneg (fun _=>sq_nonneg _)) he2).trans hEν
  have hlo(τ:ℝ)(ht:τ∈Ioo (0:ℝ) h):∀ᵐz∂ν,ProfileVariance.lowerConstant*P.lower*sqrt τ≤σ (τ,z):=
    ae_of_all _ (fun z=>le_max_left _ _)
  exact ScalarHeatSubprobabilityOpen.energy ν hmass ha hA P.exponent_pos.le P.exponent_le_one
    hρ0 hρ1 (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos)
    (mul_nonneg (by norm_num) (integral_nonneg (fun _=>sq_nonneg _))) hholder
    σ x y (variance_measurable P Λ h past hp) (current_measurable U hU h)
    ((current_measurable U hU h).add (NativeMovingJointGamma.direction_measurable D hD Λ h)) hlo
    (fun τ ht=>(hdisp τ ht).1) (fun τ ht=>(hdisp τ ht).2) j
end SHE.InitialJointGradientEnergy
