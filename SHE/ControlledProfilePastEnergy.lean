module

public import SHE.ControlledScalarCovarianceTailEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ControlledProfilePastEnergy
open Set MeasureTheory AddCircle StoppedFourier ProfileL2 ControlledProfile ProfileStability
open scoped NNReal
local instance profileEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance profileEnergy_circleSigma : MeasurableSpace CircleL2:=borel _
local instance profileEnergy_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)
variable {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]

/-- TRUE random-past frozen profile difference, with its original
initial-time stability power. This is the coefficient energy used by
the native changed-reference Haar trace; subtracting the common
additive covariance leaves exactly the same difference. -/
theorem actual_energy {Λ s:ℝ} (hΛ:0≤Λ) (hs:s∈Ioc 0 P.horizon)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (u d:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d)
    (hi:Integrable (fun ω=>‖d ω‖^2) μ) (θ η:ℝ):
    let Diff:=fun p:Ω×HeatCircle=>profile P Λ (u p.1) (d p.1) (θ,(s,p.2))-
      profile P Λ (u p.1) (d p.1) (η,(s,p.2))
    Integrable (fun p=>Diff p^2) (μ.prod haarAddCircle) ∧
      (∫p,Diff p^2 ∂μ.prod haarAddCircle)≤
        (2*meanConstant P.lower P.holder P.exponent)^2*|θ-η|^2*
          s^((P.exponent-1)/2)*(∫ω,‖d ω‖^2 ∂μ):=by
  intro Diff
  have hmap:Measurable (fun p:Ω×HeatCircle=>((u p.1,d p.1),(s,p.2))):=
    ((hu.comp measurable_fst).prodMk (hd.comp measurable_fst)).prodMk
      (measurable_const.prodMk measurable_snd)
  have hmξ(ξ:ℝ):Measurable (fun p:Ω×HeatCircle=>profile P Λ (u p.1) (d p.1) (ξ,(s,p.2))):=by
    have hh:=(ControlledReferenceWindows.coefficient_measurable P Λ ξ 0).comp hmap
    simpa only [ControlledReferenceWindows.coefficient,Function.comp_def,sub_zero] using hh
  have hm:Measurable Diff:=by convert! (hmξ θ).sub (hmξ η) using 1
  have hbound:∀p:Ω×HeatCircle,|Diff p|≤2*P.upper:=by
    intro p
    have h0:=profile_bounds P Λ (u p.1) (d p.1) (θ,(s,p.2))
    have h1:=profile_bounds P Λ (u p.1) (d p.1) (η,(s,p.2))
    have h0a:|profile P Λ (u p.1) (d p.1) (θ,(s,p.2))|≤P.upper:=by
      rw [abs_of_nonneg (P.lower_pos.le.trans h0.1)];exact h0.2
    have h1a:|profile P Λ (u p.1) (d p.1) (η,(s,p.2))|≤P.upper:=by
      rw [abs_of_nonneg (P.lower_pos.le.trans h1.1)];exact h1.2
    exact (abs_sub _ _).trans (by linarith)
  have hI:Integrable (fun p=>Diff p^2) (μ.prod haarAddCircle):=
    (bounded_memLp hm hbound).integrable_sq
  let K:=(2*meanConstant P.lower P.holder P.exponent)^2*|θ-η|^2*s^((P.exponent-1)/2)
  have hp:∀ω,(∫x,Diff (ω,x)^2 ∂haarAddCircle)≤K*‖d ω‖^2:=by
    intro ω
    have ht:=profile_l2_stability P hΛ (u ω) (d ω) θ η hsmall hs
    have hh:=pow_le_pow_left₀ (normTwo_nonneg _ _) ht 2
    rw [normTwo_sq] at hh
    have ha:(s^((P.exponent-1)/4))^2=s^((P.exponent-1)/2):=by
      rw [←Real.rpow_mul_natCast hs.1.le]
      congr 1
      ring
    simp only [mul_pow,ha] at hh
    convert hh using 1 <;> dsimp only [Diff,K] <;> ring
  refine ⟨hI,?_⟩
  rw [integral_prod _ hI]
  calc
    _≤∫ω,K*‖d ω‖^2 ∂μ:=integral_mono hI.integral_prod_left (hi.const_mul K) hp
    _=K*(∫ω,‖d ω‖^2 ∂μ):=integral_const_mul _ _

end SHE.ControlledProfilePastEnergy
