module

public import SHE.StoppedScoreScalar
public import SHE.StoppedScoreTranslation
public import SHE.StoppedCovarianceInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.StoppedScoreLeverage
open Set MeasureTheory AddCircle Finset StoppedFourier StoppedGaussianFeatures GaussianAudit
  GaussianGramScore GaussianIncrement MeasurableGaussianScores ProfileL2
  GaussianWordCovarianceBound StoppedCovarianceInput
open scoped InnerProductSpace
local instance stoppedScoreTransfer_periodPos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

theorem reference_input_integrable (hages : ∀ i,σ i ≤ target i)
    {s τ ell L : ℝ} (hs : 0 < s) (hτ : -1 < τ) (hτ0 : τ ≤ 0)
    (hell : 0 < ell) (hstop : ∀ i,s ≤ σ i)
    (e : Domain → ℝ) (he : Measurable e)
    (hcoarse : ∀ p,0 ≤ p.1 → |e p| ≤ L*p.1^τ) (x : HeatCircle) :
    Integrable (fun p : Domain => (referenceKernel σ target center hages 0 p/ell)*
      |e (p.1,x+p.2)|) (historyMeasure 0) := by
  have hh := referenceKernel_power_mass σ target center hages hs hτ hτ0 hstop
  obtain ⟨hkm,hk0,hki,hkmarg⟩ := physicalLeverage_properties
    (referenceCoefficients σ target center hages 0) σ target center hages
  have hdom : Integrable (fun p : Domain => (L/ell)*(p.1^τ*referenceKernel σ target center hages 0 p))
      (historyMeasure 0) := hh.1.const_mul (L/ell)
  apply hdom.mono'
    ((hkm.div_const ell).mul ((continuous_abs.measurable.comp he).comp
      (measurable_fst.prodMk (measurable_const.add measurable_snd)))).aestronglyMeasurable
  have ht : ∀ᵐ p : Domain ∂historyMeasure 0,0 ≤ p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  filter_upwards [ht] with p hp
  change ‖(referenceKernel σ target center hages 0 p/ell)*|e (p.1,x+p.2)|‖ ≤ _
  have hkpos : 0 ≤ referenceKernel σ target center hages 0 p := hk0 p
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hkpos hell.le),abs_abs]
  convert! mul_le_mul_of_nonneg_left (hcoarse (p.1,x+p.2) hp)
    (div_nonneg hkpos hell.le) using 1 <;> ring

/-- The actual shifted full-covariance score integral is bounded by
the deterministic positive reference convolution. The variable profile
and its signed input retain their full physical spatial dependence. -/
theorem score_integral_le_reference (hσ : ∀ i,0 < σ i) (hσ1 : ∀ i,σ i ≤ 1)
    (hages : ∀ i,σ i ≤ target i) {s τ ell L : ℝ} (hs : 0 < s)
    (hτ : -1 < τ) (hτ0 : τ ≤ 0) (hell : 0 < ell) (hstop : ∀ i,s ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (M : ℝ) (hcb : ∀ p,0 ≤ c p ∧ c p ≤ M)
    (hcl : ∀ p,ell ≤ c p) (e : Domain → ℝ) (he : Measurable e)
    (hcoarse : ∀ p,0 ≤ p.1 → |e p| ≤ L*p.1^τ) (x : HeatCircle) :
    (∫ p,|e p| * scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target (fun i => center i+x) c 0)
      (stoppedRow σ target (fun i => center i+x) p) ∂historyMeasure 0) ≤
    ∫ p : Domain,(referenceKernel σ target center hages 0 p/ell)*|e (p.1,x+p.2)| ∂historyMeasure 0 := by
  let cx : Domain → ℝ := fun p => c (domainTranslate x p)
  let ex : Domain → ℝ := fun p => e (domainTranslate x p)
  have hcx : Measurable cx := hc.comp (domainTranslate x).measurable
  have hex : Measurable ex := he.comp (domainTranslate x).measurable
  have henergy := weighted_input_energy_integrable σ target center hσ hσ1 hages ex hex hτ
    (fun p hp => hcoarse (domainTranslate x p) hp)
  have hi := scoreEnergy_outer_integrable (historyMeasure 0)
    (StoppedGaussianFeatures.stoppedCovariance σ target center cx 0)
    (stoppedRow σ target center) (stoppedRow_measurable σ target center) ex hex henergy
  have href := reference_input_integrable σ target center hages hs hτ hτ0 hell hstop e he hcoarse x
  rw [score_integral_translate]
  apply integral_mono_ae hi href
  filter_upwards [score_le_reference_ae σ target center hages cx hcx M
    (fun p => hcb _) hell (fun p => hcl _) 0] with p hp
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg (ex p))
  simpa only [ex,domainTranslate_apply,add_comm,mul_comm] using hh

end SHE.StoppedScoreLeverage
