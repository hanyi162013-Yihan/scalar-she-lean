module

public import SHE.HolderFutureScoreInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HolderGeneralScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfileStability ControlledProfile MeasurableGaussianScores ControlledResidualScoreInput
local instance : Fact (0<2*π):=⟨by positivity⟩

/-- The finite actual profile difference acts against ANY elliptic
residual covariance law. In particular the law may be a convex
interpolation of endpoint profiles rather than another fixed point. -/
theorem shifted_input (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (s : ℝ) (hs : 0<s) (hstop : ∀ i,s≤σ i)
    (ell : ℝ) (hell : 0<ell) (c : ControlledProfile.Domain→ℝ) (hc : Measurable c)
    (U : ℝ) (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p) :
    let e:=ProfileHolderScoreRates.difference P Λ u d q θ η
    let F:=StoppedScoreLeverage.scoreInput σ target center c e
    (∀ x : HeatCircle,Integrable (fun p=>|e p| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x) c 0)
      (stoppedRow σ target (fun i=>center i+x) p)) (historyMeasure 0)) ∧
    MemLp F 2 haarAddCircle ∧
    normTwo haarAddCircle F≤(2*(P.holder*(|θ - η| * ‖d‖)^P.exponent))*(3*((n:ℝ)/ell)) := by
  intro e F
  let K:=2*(P.holder*(|θ - η| * ‖d‖)^P.exponent)
  have hK : 0≤K:=mul_nonneg (by norm_num)
    (mul_nonneg P.holder_nonneg (rpow_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) _))
  have he : Measurable e:=ProfileHolderScoreRates.difference_measurable P Λ u d q θ η
  have hcoarse (p : ControlledProfile.Domain) (hp : 0≤p.1) :
      |e p|≤(2*P.upper)*p.1^(-(1/4:ℝ)):=
    ProfileHolderScoreRates.difference_coarse P Λ u d hq θ η p hp
  have hmoment (x : HeatCircle) :=StoppedCovarianceInput.score_input_weighted_bound
    σ target (fun i=>center i+x) hσ hσ1 hages hs
    (by norm_num : -1 < -(1/4:ℝ)) (by norm_num : -(1/4:ℝ)<0)
    (mul_nonneg (by norm_num) P.upper_nonneg) hstop c hc U ell hcb hell hcl e he hcoarse
  have hFm : Measurable F:=by
    convert! StoppedCovarianceWordFields.scoreInput_measurable σ target center c e hc he using 1
  have hF0 (x : HeatCircle) : 0≤F x:=StoppedScoreLeverage.scoreInput_nonneg
    σ target center hσ hσ1 hages c hc U ell hcb hell hcl e x
  have hmem : MemLp F 2 haarAddCircle:=bounded_memLp hFm (fun x=>by
    rw [abs_of_nonneg (hF0 x)]
    exact (hmoment x).2)
  refine ⟨fun x=>(hmoment x).1,hmem,?_⟩
  have hh:=StoppedScoreLeverage.scoreInput_normTwo_bound
    σ target center hσ hσ1 hages hs (by norm_num : -1<(0:ℝ)) le_rfl
    (by norm_num : -1 < -(1/4:ℝ)) (by norm_num : -(1/4:ℝ)<0)
    hell hK (mul_nonneg (by norm_num) P.upper_nonneg) hstop c hc U hcb hcl e he hcoarse
    (ae_of_all _ (fun r=>by
      simpa only [rpow_zero,mul_one] using
        ProfileHolderScoreRates.difference_sharp P hΛ u d hsmallL2 q θ η r)) hFm
  convert! hh using 1 <;> norm_num <;> ring

/-- Original future time, arbitrary uniformly elliptic residual law,
and a literal finite controlled-profile difference. Absolute future
history integrability is a conclusion, before spatial cancellation. -/
theorem future_input (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i)
    (ell : ℝ) (hell : 0<ell) (c : ControlledProfile.Domain→ℝ) (hc : Measurable c)
    (U : ℝ) (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p) :
    let e:=fun p=>profile P Λ u d (θ,p)-profile P Λ u d (η,p)
    let F:=futureInput σ target center c e q
    (∀ x : HeatCircle,Integrable (fun p=>|e p| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x) c q)
      (stoppedRow σ target (fun i=>center i+x) p)) (historyMeasure q)) ∧
    MemLp F 2 haarAddCircle ∧
    normTwo haarAddCircle F≤(2*(P.holder*(|θ - η| * ‖d‖)^P.exponent))*(3*((n:ℝ)/ell)) := by
  intro e F
  have hs : 0<hi-q:=sub_pos.mpr hhi
  let c':=fun p : ControlledProfile.Domain=>c (q+p.1,p.2)
  have hc' : Measurable c':=hc.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hh:=shifted_input P hΛ u d hsmallL2 q hq θ η n
    (fun i=>σ i-q) (fun i=>target i-q) center
    (fun i=>hs.trans_le (sub_le_sub_right (hstop i) q)) hσ1
    (fun i=>sub_le_sub_right (hages i) q) (hi-q) hs
    (fun i=>sub_le_sub_right (hstop i) q) ell hell c' hc' U
    (fun p=>hcb (q+p.1,p.2)) (fun p=>hcl (q+p.1,p.2))
  have hpos : ∀ᵐ p : ControlledProfile.Domain ∂historyMeasure 0,0<p.1 := by
    have ht : ∀ᵐ r : ℝ ∂volume.restrict (Ici (0:ℝ)),0<r:=by
      rw [←Measure.restrict_congr_set (Ioi_ae_eq_Ici : Ioi (0:ℝ)=ᵐ[volume] Ici 0)]
      exact ae_restrict_mem measurableSet_Ioi
    exact Measure.quasiMeasurePreserving_fst.ae ht
  have heq : F=StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      c' (ProfileHolderScoreRates.difference P Λ u d q θ η) := by
    change (fun x : HeatCircle=>∫ p,|e p| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x) c q)
      (stoppedRow σ target (fun i=>center i+x) p) ∂historyMeasure q)=_
    rw [StoppedTimeTranslation.score_input_shift]
    funext x
    apply integral_congr_ae
    filter_upwards [hpos] with p hp
    simp only [ProfileHolderScoreRates.difference,hp,ite_true,StoppedTimeTranslation.shift_apply,e,c']
  refine ⟨?_,by simpa only [heq] using hh.2⟩
  intro x
  apply ((StoppedTimeTranslation.shift_preserving q).integrable_comp_emb
    (StoppedTimeTranslation.shift q).measurableEmbedding).mp
  apply (hh.1 x).congr
  filter_upwards [hpos] with p hp
  dsimp only [Function.comp_def]
  conv_rhs=>rw [StoppedTimeTranslation.covariance_shift]
  rw [StoppedTimeTranslation.row_shift]
  simp only [ProfileHolderScoreRates.difference,hp,ite_true,StoppedTimeTranslation.shift_apply,e,c']

end SHE.HolderGeneralScoreInput
