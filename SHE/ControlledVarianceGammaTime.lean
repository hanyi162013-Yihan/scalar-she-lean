module

public import SHE.ControlledScalarCovarianceTailEnergy
public import SHE.ScalarHeatVarianceInitialTime

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ControlledVarianceGammaTime
open Set MeasureTheory Real AddCircle StoppedFourier ProfileVariance ProfileL2
  ControlledProfile ProfileStability ControlledScalarCovarianceTail
  ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal
local instance varianceGamma_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance varianceGamma_circleSigma : MeasurableSpace CircleL2:=borel _
local instance varianceGamma_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)
variable {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]

/-- Actual random-past remaining variance, jointly Borel in future age,
original sample and native spatial point. -/
def variance (Λ v b θ:ℝ) (u d:Ω→CircleL2) (p:ℝ×(Ω×HeatCircle)):ℝ:=
  ControlledScalarCovarianceTailEnergy.field P Λ v b θ (((u p.2.1,d p.2.1),b-p.1),p.2.2)

theorem variance_measurable (Λ v b θ:ℝ) (u d:Ω→CircleL2)
    (hu:Measurable u) (hd:Measurable d):Measurable (variance P Λ v b θ u d):=by
  exact (ControlledScalarCovarianceTailEnergy.field_measurable P Λ v b θ).comp
    ((((hu.comp measurable_snd.fst).prodMk (hd.comp measurable_snd.fst)).prodMk
      (measurable_const.sub measurable_fst)).prodMk measurable_snd.snd)

/-- BOTH actual changed-variance Gamma slots have the required physical
time/frequency bound for arbitrary dependent means. Original past
energy, canonical tail covariance, both endpoint faces and integrability
are all derived. Only ordinary analytic band hypotheses remain. -/
theorem actual_energy {Λ v b ρ H0:ℝ} (hΛ:0≤Λ) (hvb:v<b)
    (hspan:b-v≤P.horizon) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (u d:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d)
    (hi:Integrable (fun ω=>‖d ω‖^2) μ) (θ η:ℝ)
    {a:ℝ→ℝ} (ha:BoundedSmooth a) (hH0:0≤H0)
    (hholder:∀x y,|a x-a y|≤H0*|x-y|^P.exponent)
    (m:ℝ×(Ω×HeatCircle)→ℝ) (hm:Measurable m) (j:ℕ):
    let σ0:=variance P Λ v b θ u d
    let σ1:=variance P Λ v b η u d
    let g:=fun p=>deriv (heat (σ1 p).toNNReal (ScalarHeatBands.band a (j+1))) (m p)-
      deriv (heat (σ0 p).toNNReal (ScalarHeatBands.band a (j+1))) (m p)
    let r:=CompactMollifier.radius (j+1)
    let p:=(P.exponent-1)/2
    let c:=lowerConstant*P.lower
    let E:=(ControlledScalarCovarianceTail.constant P)^2*|θ-η|^2*(∫ω,‖d ω‖^2 ∂μ)
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫z,|g (t,z)|^2 ∂μ.prod haarAddCircle)) (Ioc 0 (b-v)) ∧
      (∫t in Ioc 0 (b-v),t^(ρ-1/2)*(∫z,|g (t,z)|^2 ∂μ.prod haarAddCircle))≤
        ((1/2:ℝ)*H0*ScalarHeatBandEnvelope.constant P.exponent 2)^2*
          (((1/2:ℝ)^p)*(1/(ρ+3/2)+1/(1-P.exponent/2-ρ))+2/(p+1))*
          c^(-3-2*ρ)*r^(2*P.exponent+4*ρ)*E*(b-v)^p:=by
  intro σ0 σ1 g r p c E
  have hσ(ξ:ℝ):Measurable (variance P Λ v b ξ u d):=variance_measurable P Λ v b ξ u d hu hd
  have heq(ξ:ℝ)(t:ℝ)(ht:t∈Ioo 0 (b-v))(z:Ω×HeatCircle):
      variance P Λ v b ξ u d (t,z)=tail P Λ v (b-t) b ξ (u z.1) (d z.1) z.2:=by
    unfold variance ControlledScalarCovarianceTailEnergy.field
    rw [min_eq_left (by linarith [ht.1] : b-t≤b)]
  have hlo(ξ:ℝ)(t:ℝ)(ht:t∈Ioo 0 (b-v)):
      ∀ᵐz:Ω×HeatCircle ∂μ.prod haarAddCircle,c*sqrt t≤variance P Λ v b ξ u d (t,z):=by
    apply ae_of_all
    intro z
    rw [heq ξ t ht z]
    have hc:Measurable (fun w:Domain=>profile P Λ (u z.1) (d z.1) (ξ,(w.1-v,w.2))):=
      (ControlledProfile.profile_measurable P Λ (u z.1) (d z.1)).comp
        (measurable_const.prodMk ((measurable_fst.sub_const v).prodMk measurable_snd))
    have hh:=ScalarCovarianceTailScale.elliptic hc (by linarith [ht.1] : b-t<b)
      (by linarith [ht.2,P.horizon_le_one]) P.lower_pos.le P.upper_nonneg
      (fun w=>profile_bounds P Λ (u z.1) (d z.1) _) z.2
    simpa only [show b-(b-t)=t by ring,Real.sqrt_eq_rpow,c,tail] using hh.1
  have he(t:ℝ)(ht:t∈Ioo 0 (b-v)):
      Integrable (fun z=>(σ1 (t,z)-σ0 (t,z))^2) (μ.prod haarAddCircle) ∧
      (∫z,(σ1 (t,z)-σ0 (t,z))^2 ∂μ.prod haarAddCircle)≤E*t*((b-v)-t)^p:=by
    have hh:=ControlledScalarCovarianceTailEnergy.actual_energy P μ hΛ
      (by linarith [ht.2] : v<b-t) (by linarith [ht.1] : b-t<b) hspan hsmall
      u d hu hd hi η θ
    simp only [show b-(b-t)=t by ring,show b-t-v=(b-v)-t by ring,abs_sub_comm] at hh
    have heq':(fun z:Ω×HeatCircle=>(σ1 (t,z)-σ0 (t,z))^2)=
        (fun z=>(tail P Λ v (b-t) b η (u z.1) (d z.1) z.2-
          tail P Λ v (b-t) b θ (u z.1) (d z.1) z.2)^2):=by
      funext z
      dsimp only [σ0,σ1]
      rw [heq η t ht z,heq θ t ht z]
    rw [heq']
    refine ⟨hh.1,hh.2.trans_eq ?_⟩
    dsimp only [E,p]
    ring
  have hc:0<c:=mul_pos lowerConstant_pos P.lower_pos
  have hE:0≤E:=by dsimp only [E];positivity
  exact ScalarHeatVarianceInitialTime.energy (μ.prod haarAddCircle) ha hH0 P.exponent_pos.le
    P.exponent_le_one hρ0 hρ1 hc hE (sub_pos.mpr hvb)
    (by dsimp only [p];linarith [P.exponent_pos])
    (by dsimp only [p];linarith [P.exponent_le_one]) hholder
    σ0 σ1 m (hσ θ) (hσ η) hm (hlo θ) (hlo η)
    (fun t ht=>(he t ht).1) (fun t ht=>(he t ht).2) j

end SHE.ControlledVarianceGammaTime
