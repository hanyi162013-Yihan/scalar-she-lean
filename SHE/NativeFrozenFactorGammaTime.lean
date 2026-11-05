module
public import SHE.ControlledProfilePastEnergy
public import SHE.ControlledReferenceEnergy
public import SHE.ScalarHeatBandInitialMass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.NativeFrozenFactorGammaTime
open Set MeasureTheory Real AddCircle StoppedFourier ControlledProfile ProfileL2 ScalarHeatBandEnvelope
local instance nativeFrozenFactorGammaTime_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeFrozenFactorGammaTime_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeFrozenFactorGammaTime_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeFrozenFactorGammaTime_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFrozenFactorGammaTime_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFrozenFactorGammaTime_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFrozenFactorGammaTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : κ<P.lower)
variable (u d : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d)
def coefficient (θ s : ℝ) (ω : Ω) : CircleHeat.CircleL2:=
  (ControlledResidualField.field P Λ κ hκ (((u ω,d ω),θ),s)).val
include hu hd in
theorem coefficient_measurable (θ : ℝ) : Measurable (fun p : ℝ×Ω=>coefficient P Λ κ hκ u d θ p.1 p.2):=by
  have hm:= (ControlledResidualField.field_measurable P Λ κ hκ).comp
    ((((hu.comp measurable_snd).prodMk (hd.comp measurable_snd)).prodMk (measurable_const (a:=θ))).prodMk measurable_fst)
  exact measurable_subtype_coe.comp hm
include hu hd in
theorem section_energy (hΛ : 0≤Λ) {s : ℝ} (hs : s∈Ioc 0 P.horizon)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hi : Integrable (fun ω=>‖d ω‖^2) μ) (θ η : ℝ) :
    Integrable (fun ω=>‖coefficient P Λ κ hκ u d θ s ω-coefficient P Λ κ hκ u d η s ω‖^2) μ ∧
      (∫ω,‖coefficient P Λ κ hκ u d θ s ω-coefficient P Λ κ hκ u d η s ω‖^2 ∂μ)≤
        (2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2*|θ-η|^2*
          s^((P.exponent-1)/2)*(∫ω,‖d ω‖^2 ∂μ) := by
  have he:=ControlledProfilePastEnergy.actual_energy P μ hΛ hs hsmall u d hu hd hi θ η
  have hp (ω : Ω) : ‖coefficient P Λ κ hκ u d θ s ω-coefficient P Λ κ hκ u d η s ω‖^2=
      ∫x,(profile P Λ (u ω) (d ω) (θ,(s,x))-profile P Λ (u ω) (d ω) (η,(s,x)))^2 ∂haarAddCircle:=by
    have hn:=CircleNormalization.push.norm_map
      (coefficient P Λ κ hκ u d θ s ω-coefficient P Λ κ hκ u d η s ω)
    dsimp only [coefficient] at hn ⊢
    rw [map_sub,ControlledResidualField.push_field,ControlledResidualField.push_field] at hn
    rw [←hn,ControlledReferenceEnergy.native_difference_norm P Λ κ hκ,ProfileL2.normTwo_sq]
  refine ⟨?_,?_⟩
  · simpa only [hp] using he.1.integral_prod_left
  · rw [integral_congr_ae (ae_of_all _ hp),←integral_prod _ he.1]
    exact he.2
attribute [local irreducible] coefficient
include hu hd in
/-- Actual changed frozen-factor energy with full frequency gain on
both the future and original initial-age faces. -/
theorem energy (hΛ : 0≤Λ) {h ρ A : ℝ} (hh : 0<h) (hhP : h≤P.horizon)
    (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hi : Integrable (fun ω=>‖d ω‖^2) μ) (θ η : ℝ) (j : ℕ) :
    let r:=CompactMollifier.radius (j+1)
    let c:=ProfileVariance.lowerConstant*P.lower
    let p:=(P.exponent-1)/2
    let G:=fun τ=>τ^(ρ-1/2)*(A*r^(P.exponent-1)*decay r (c*sqrt τ) ((3-P.exponent)/2))^2*
      (∫ω,‖coefficient P Λ κ hκ u d θ (h-τ) ω-coefficient P Λ κ hκ u d η (h-τ) ω‖^2 ∂μ)
    IntegrableOn G (Ioc (0:ℝ) h) ∧
      (∫τ in Ioc (0:ℝ) h,G τ)≤
        A^2*(2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2*|θ-η|^2*
          (∫ω,‖d ω‖^2 ∂μ)*
          (((1/2:ℝ)^p)*(1/(ρ+1/2)+1/(1-P.exponent/2-ρ))+2/(p+1))*
          c^(-1-2*ρ)*r^(2*P.exponent+4*ρ)*h^p := by
  intro r c p G
  let K:=A^2*(2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2*|θ-η|^2*(∫ω,‖d ω‖^2 ∂μ)
  let B:=fun τ=>τ^(ρ-1/2)*(r^(P.exponent-1)*decay r (c*sqrt τ) ((3-P.exponent)/2))^2*(h-τ)^p
  have hc : 0<c:=mul_pos ProfileVariance.lowerConstant_pos P.lower_pos
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hK : 0≤K:=by dsimp only [K];positivity
  have hb:=ScalarHeatBandInitialMass.mass (r:=r) (c:=c) (h:=h) (β:=P.exponent) (ρ:=ρ) (p:=p) hr hc hh P.exponent_le_one hρ0 hρ1
    (by dsimp only [p];linarith [P.exponent_pos]) (by dsimp only [p];linarith [P.exponent_le_one])
  have hcm(ξ:ℝ):Measurable (fun z:ℝ×Ω=>coefficient P Λ κ hκ u d ξ (h-z.1) z.2):=
    (coefficient_measurable P Λ κ hκ u d hu hd ξ).comp (((measurable_const (a:=h)).sub measurable_fst).prodMk measurable_snd)
  have hG:Measurable G:=by
    have hm:=((hcm θ).sub (hcm η)).norm.pow_const 2
    have hm' : Measurable (fun z:ℝ×Ω=>‖coefficient P Λ κ hκ u d θ (h-z.1) z.2-
        coefficient P Λ κ hκ u d η (h-z.1) z.2‖^2):=by simpa only [Pi.sub_apply] using hm
    have hi:=(hm'.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable
    have hw:Measurable (fun τ:ℝ=>τ^(ρ-1/2)*(A*r^(P.exponent-1)*decay r (c*sqrt τ) ((3-P.exponent)/2))^2):=by
      unfold decay
      fun_prop
    exact hw.mul hi
  have hmem:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) h),τ∈Ioo (0:ℝ) h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hdom:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) h),G τ≤K*B τ:=by
    filter_upwards [hmem] with τ hτ
    have he:=section_energy μ P Λ κ hκ u d hu hd hΛ
      (show h-τ∈Ioc 0 P.horizon from ⟨by linarith [hτ.2],by linarith [hτ.1]⟩) hsmall hi θ η
    have hn:0≤τ^(ρ-1/2)*(A*r^(P.exponent-1)*decay r (c*sqrt τ) ((3-P.exponent)/2))^2:=
      mul_nonneg (rpow_nonneg hτ.1.le _) (sq_nonneg _)
    have hm:=mul_le_mul_of_nonneg_left he.2 hn
    convert hm using 1 <;> dsimp only [G,K,B,p] <;> ring
  have hI:IntegrableOn G (Ioc (0:ℝ) h):=by
    apply (hb.1.const_mul K).mono' hG.aestronglyMeasurable
    filter_upwards [hdom,hmem] with τ hτ ht
    have hnon:0≤G τ:=mul_nonneg (mul_nonneg (rpow_nonneg ht.1.le _) (sq_nonneg _))
      (integral_nonneg (fun _=>sq_nonneg _))
    rw [Real.norm_of_nonneg hnon]
    exact hτ
  refine ⟨hI,?_⟩
  calc
    _≤∫τ in Ioc (0:ℝ) h,K*B τ:=integral_mono_ae hI (hb.1.const_mul K) hdom
    _=K*∫τ in Ioc (0:ℝ) h,B τ:=integral_const_mul _ _
    _≤_:=by
      have hm:=mul_le_mul_of_nonneg_left hb.2 hK
      convert hm using 1 <;> dsimp only [K] <;> ring
end SHE.NativeFrozenFactorGammaTime
