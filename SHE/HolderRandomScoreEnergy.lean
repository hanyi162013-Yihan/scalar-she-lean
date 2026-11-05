module

public import SHE.HolderGeneralScoreInput
public import SHE.FractionalNormEnergy
public import SHE.RandomFutureInputFields
public import SHE.SectionEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HolderRandomScoreEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfileStability ControlledProfile MeasurableGaussianScores ControlledResidualScoreInput
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- Actual sample/output energy of finite profile-difference score
mass under ANY correlated elliptic residual covariance. The past L2
energy is retained to its Holder power; neither independence nor a
Gaussian model moment is supplied as an input. -/
theorem future_energy (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [IsProbabilityMeasure μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i)
    (ell : ℝ) (hell : 0<ell) (c : W×ControlledProfile.Domain→ℝ) (hc : Measurable c)
    (U : ℝ) (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p) :
    let e:=fun z : W×ControlledProfile.Domain=>
      profile P Λ (u z.1) (d z.1) (θ,z.2)-profile P Λ (u z.1) (d z.1) (η,z.2)
    let F:=fun z : W×HeatCircle=>futureInput σ target center
      (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
    let C:=2*P.holder*|θ-η|^P.exponent*(3*((n:ℝ)/ell))
    Integrable (fun z=>|F z|^2) (μ.prod haarAddCircle) ∧
      (∫ z,|F z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ ω,‖d ω‖^2 ∂μ)^P.exponent := by
  intro e F C
  have he : Measurable e:=by
    have hm (a : ℝ) : Measurable (fun z : W×ControlledProfile.Domain=>((z.1,a),z.2)):=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    convert! ((random_profile_measurable P hu hd Λ).comp (hm θ)).sub
      ((random_profile_measurable P hu hd Λ).comp (hm η)) using 1
  have hF : Measurable F:=futureInput_random_measurable σ target center c e hc he q
  have hfrac:=FractionalNormEnergy.fractional_square (fun ω=>‖d ω‖) hd.norm.aestronglyMeasurable
    (by simpa only [norm_norm] using hdi)
    P.exponent_pos.le P.exponent_le_one
  simp only [norm_norm] at hfrac
  have hBi : Integrable (fun ω=>C^2*‖d ω‖^((2:ℝ)*P.exponent)) μ:=hfrac.1.const_mul _
  have hsec : ∀ᵐ ω ∂μ,Integrable (fun x : HeatCircle=>‖F (ω,x)‖^2) haarAddCircle ∧
      (∫ x : HeatCircle,‖F (ω,x)‖^2 ∂haarAddCircle)≤C^2*‖d ω‖^((2:ℝ)*P.exponent):=by
    apply ae_of_all
    intro ω
    have hh:=HolderGeneralScoreInput.future_input P hΛ (u ω) (d ω) hsmallL2 q hq θ η n
      σ target center hσ1 hages hi hhi hstop ell hell (fun p=>c (ω,p))
      (hc.comp (measurable_const.prodMk measurable_id)) U
      (fun p=>hcb (ω,p)) (fun p=>hcl (ω,p))
    have hsq:=pow_le_pow_left₀ (normTwo_nonneg haarAddCircle _) hh.2.2 2
    rw [normTwo_sq] at hsq
    have hfactor : 2*(P.holder*(|θ - η| * ‖d ω‖)^P.exponent)*(3*((n:ℝ)/ell))=
        C*‖d ω‖^P.exponent := by
      rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
      dsimp only [C]
      ring
    rw [hfactor,mul_pow] at hsq
    have hp : (‖d ω‖^P.exponent)^2=‖d ω‖^((2:ℝ)*P.exponent):=by
      rw [←Real.rpow_mul_natCast (norm_nonneg _)]
      congr 1
      ring
    rw [hp] at hsq
    refine ⟨hh.2.1.norm.integrable_sq,?_⟩
    simpa only [Real.norm_eq_abs,sq_abs,F,e] using hsq
  have hp:=SectionEnergy.product_energy haarAddCircle μ F hF
    (fun ω=>C^2*‖d ω‖^((2:ℝ)*P.exponent)) hBi
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨by simpa only [Real.norm_eq_abs] using hp.1,?_⟩
  have hmul:=mul_le_mul_of_nonneg_left hfrac.2 (sq_nonneg C)
  have ht : (∫ z,|F z|^2 ∂μ.prod haarAddCircle)≤
      C^2*(∫ ω,‖d ω‖^((2:ℝ)*P.exponent) ∂μ):=by
    simpa only [Real.norm_eq_abs,integral_const_mul] using hp.2
  exact ht.trans hmul

end SHE.HolderRandomScoreEnergy
