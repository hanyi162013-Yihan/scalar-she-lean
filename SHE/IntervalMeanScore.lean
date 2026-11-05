module

public import SHE.IntervalScoreMass
public import SHE.PhysicalMeanRange
public import SHE.HeatProjectionAges
public import SHE.NegativeL2Heat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.IntervalMeanScore
open Set Filter MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  OldIntervalCovariance GaussianIncrement GaussianGramScore MeasurableGaussianScores
  HeatTorusKernel HeatProjection StoppedMeanRange StoppedGaussianScore
  RealHeatCovarianceMean PhysicalMeanRange
open scoped BigOperators InnerProductSpace
local instance intervalMeanScore_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- The terminal mean direction is the literal signed integral against
the original physical endpoint heat row. -/
theorem currentDirection_integral (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (lo : ℝ) (hactive : ∀ i, lo < σ i) (hages : ∀ i, σ i ≤ target i)
    (v : StoppedFourier.CircleL2) (i : Fin n) :
    currentDirection target a lo v i =
      ∫ x : HeatCircle, stoppedRow σ target (nativeCenter a) (lo,x) i * (v x).re ∂haarAddCircle := by
  have ht : 0 < target i-lo := by linarith [hactive i,hages i]
  change PhysicalProfile.physicalHeatMean v (target i-lo,nativeCenter a i)=_
  rw [PhysicalProfile.physicalHeatMean_eq ht,L2.inner_def]
  change RCLike.re (∫ x : HeatCircle, inner ℂ (circleHeat (target i-lo) (nativeCenter a i) x) (v x) ∂haarAddCircle)=_
  rw [← integral_re (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [ProfileVariance.heatPhysical_ae ht (nativeCenter a i)] with x hx
  have hr := WordRecursion.heatPhysical_real ht (nativeCenter a i) x
  have him : (ProfileVariance.heatPhysical (target i-lo) (nativeCenter a i) x).im=0 := by
    have hh := congrArg Complex.im hr
    simpa only [Complex.ofReal_im] using hh.symm
  rw [← hx,RCLike.inner_apply]
  change ((v x)*starRingEnd ℂ (ProfileVariance.heatPhysical (target i-lo) (nativeCenter a i) x)).re=
    (if lo < σ i then (ProfileVariance.heatPhysical (target i-lo) (nativeCenter a i) x).re else 0)*(v x).re
  rw [ite_eq_left (hactive i)]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,him,neg_zero,mul_zero,sub_zero]
  ring

/-- The actual old-interval covariance controls the terminal signed-input
score by the genuine orthogonal projection onto its physical heat span.
The covariance may be singular; no inverse condition number is used. -/
theorem direction_projection_bound
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hstop : ∀ i, hi ≤ σ i) (hages : ∀ i, σ i ≤ target i)
    (t : Fin n → ℝ) (hage : ∀ i, target i-lo=4*π^2*t i)
    (c : Domain → ℝ) (hc : Measurable c) (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) (d : HeatTorus.CircleL2) :
    let act : ∀ i, lo < σ i := fun i => hgap.trans_le (hstop i)
    let S := currentSynthesis σ target a lo t hage act
    meanDirection S d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) (intervalProfile c lo hi) 0)).range ∧
    scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) (intervalProfile c lo hi) 0)
      (meanDirection S d) ≤
        (ell*(hi-lo))⁻¹ * ‖(heatSpan t a).starProjection d‖^2 := by
  let act : ∀ i, lo < σ i := fun i => hgap.trans_le (hstop i)
  let S := currentSynthesis σ target a lo t hage act
  let v := IntervalScoreMass.feature σ target (nativeCenter a) hages c hc M
    (fun p => ⟨hell.le.trans (hb p).1,(hb p).2⟩) lo hi
  have hden : 0 < ell*(hi-lo) := mul_pos hell (sub_pos.mpr hgap)
  have hbound (z : State n) : ‖S z‖ ≤ sqrt ((ell*(hi-lo))⁻¹)*‖featureSynthesis v z‖ := by
    have he := IntervalScoreMass.endpoint_domination σ target (nativeCenter a) hages c hc hlo hgap
      (fun i => Or.inr (hstop i)) hell hb z
    rw [realHistory_square_mass σ target (nativeCenter a) hages] at he
    have hnorm : ‖S z‖^2=‖historyF Finset.univ (fun i => (z i:ℂ)) σ target (nativeCenter a) lo‖^2 := by
      exact HeatHistoryScore.currentHeatRow_norm_sq σ target a lo t hage act (fun i => (z i:ℂ))
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,sq_sqrt (inv_nonneg.mpr hden.le),hnorm]
    exact (le_inv_mul_iff₀ hden).mpr he
  have hp := scoreVariance_projection_bound t a S v
    (fun z => (realCurrent σ target a lo t hage act z).property)
    (sqrt_nonneg _) hbound d
  rw [sq_sqrt (inv_nonneg.mpr hden.le)] at hp
  have hg : Matrix.gram ℝ v=
      StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) (intervalProfile c lo hi) 0 :=
    IntervalScoreMass.feature_gram σ target (nativeCenter a) hages c hc M
      (fun p => ⟨hell.le.trans (hb p).1,(hb p).2⟩) lo hi
  rwa [hg] at hp

def covarianceField (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (c : UnitAddCircle × Domain → ℝ) (lo hi : ℝ) (x : UnitAddCircle) : Matrix (Fin n) (Fin n) ℝ :=
  StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter (fun i => a i+x))
    (intervalProfile (fun p => c (x,p)) lo hi) 0

theorem covarianceField_measurable (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    {c : UnitAddCircle × Domain → ℝ} (hc : Measurable c) (lo hi : ℝ) :
    Measurable (covarianceField σ target a c lo hi) := by
  have hm : Measurable (fun p : UnitAddCircle × Domain => intervalProfile (fun r => c (p.1,r)) lo hi p.2) := by
    exact hc.ite ((measurableSet_Ioc.prod MeasurableSet.univ).preimage measurable_snd) measurable_const
  exact StoppedGaussianFields.covariance_measurable (StoppedMeanEnergy.translatedFamily σ target a) hm measurable_const

theorem current_basis_measurable (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (lo : ℝ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hage : ∀ i, target i-lo=4*π^2*t i) (hactive : ∀ i, lo < σ i) (i : Fin n) :
    StronglyMeasurable (fun x => currentSynthesis σ target (fun j => a j+x) lo t hage hactive
      (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  have hm := (HeatChristoffelTransfer.continuous_translate_action.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : UnitAddCircle => unitHeatKernel (t i) (a i))))).stronglyMeasurable
  convert! hm using 1
  funext x
  rw [currentSynthesis_basis]
  change unitHeatKernel (t i) (a i+x)=translate x (unitHeatKernel (t i) (a i))
  exact (translate_unitHeatKernel (ht i) (a i) x).symm

/-- Sharp signed-input energy for the actual last old interval. Every
original target age keeps its own positive heat operator, even when ages
are not comparable and the coefficient depends on the output point. -/
theorem terminal_energy_age_sum (n : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
      {lo hi ell M : ℝ}, ∀ (hlo : 0 ≤ lo) (hgap : lo < hi)
      (hstop : ∀ i, hi ≤ σ i) (hages : ∀ i, σ i ≤ target i),
      ∀ (t : Fin n → ℝ), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i-lo=4*π^2*t i)
      (c : UnitAddCircle × Domain → ℝ), Measurable c → 0 < ell →
      (∀ x p, ell ≤ c (x,p) ∧ c (x,p) ≤ M) → ∀ d : HeatTorus.CircleL2,
      let act : ∀ i, lo < σ i := fun i => hgap.trans_le (hstop i)
      let S := fun x => currentSynthesis σ target (fun i => a i+x) lo t hage act
      Integrable (fun x => scoreVariance (covarianceField σ target a c lo hi x) (meanDirection (S x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (covarianceField σ target a c lo hi x) (meanDirection (S x) d) ∂haarAddCircle) ≤
        (C/(ell*(hi-lo))) * ∑ i, sqrt (t i)*‖CircleHeat.heat (θ*t i) d‖^2 := by
  obtain ⟨h,C,θ,hh,hh1,hC,hθ,hproj⟩ := heat_span_projection_age_sum n
  refine ⟨h,C,θ,hh,hh1,hC,hθ,?_⟩
  intro σ target a lo hi ell M hlo hgap hstop hages t ht hth hage c hc hell hb d
  let act : ∀ i, lo < σ i := fun i => hgap.trans_le (hstop i)
  let S := fun x => currentSynthesis σ target (fun i => a i+x) lo t hage act
  let A := covarianceField σ target a c lo hi
  have hden : 0 < ell*(hi-lo) := mul_pos hell (sub_pos.mpr hgap)
  have hpoint (x : UnitAddCircle) := direction_projection_bound σ target (fun i => a i+x) hlo hgap hstop hages
    t hage (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) hell (hb x) d
  have hAm : Measurable A := covarianceField_measurable σ target a hc lo hi
  have hDm : Measurable (fun x => meanDirection (S x) d) := meanDirection_measurable S
    (current_basis_measurable σ target a lo t ht hage act) d
  have hnonneg (x : UnitAddCircle) : 0 ≤ scoreVariance (A x) (meanDirection (S x) d) := by
    have hp : (A x).PosSemidef := by
      have hg : Matrix.gram ℝ (IntervalScoreMass.feature σ target (nativeCenter (fun i => a i+x)) hages
          (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) M
          (fun p => ⟨hell.le.trans (hb x p).1,(hb x p).2⟩) lo hi)=A x :=
        IntervalScoreMass.feature_gram σ target (nativeCenter (fun i => a i+x)) hages
          (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) M
          (fun p => ⟨hell.le.trans (hb x p).1,(hb x p).2⟩) lo hi
      rw [← hg]
      exact Matrix.posSemidef_gram ℝ _
    exact scoreVariance_nonneg hp (hpoint x).1
  obtain ⟨hpi,hpb⟩ := hproj t a ht hth d
  have hInt : Integrable (fun x => scoreVariance (A x) (meanDirection (S x) d)) haarAddCircle := by
    apply (hpi.const_mul ((ell*(hi-lo))⁻¹)).mono'
      (scoreVariance_measurable.comp (hAm.prodMk hDm)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      change ‖scoreVariance (A x) (meanDirection (S x) d)‖ ≤ _
      rw [Real.norm_of_nonneg (hnonneg x)]
      exact (hpoint x).2)
  refine ⟨hInt,?_⟩
  calc
    _ ≤ ∫ x, (ell*(hi-lo))⁻¹*‖(heatSpan t (fun i => a i+x)).starProjection d‖^2 ∂haarAddCircle :=
      integral_mono hInt (hpi.const_mul _) (fun x => (hpoint x).2)
    _ = (ell*(hi-lo))⁻¹*(∫ x, ‖(heatSpan t (fun i => a i+x)).starProjection d‖^2 ∂haarAddCircle) := integral_const_mul _ _
    _ ≤ (ell*(hi-lo))⁻¹*(C*∑ i, sqrt (t i)*‖CircleHeat.heat (θ*t i) d‖^2) :=
      mul_le_mul_of_nonneg_left hpb (inv_nonneg.mpr hden.le)
    _ = _ := by ring

end SHE.IntervalMeanScore
