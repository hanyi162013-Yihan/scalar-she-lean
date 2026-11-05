module

public import SHE.StoppedScoreLeverage
public import SHE.StoppedCovarianceOrder
public import SHE.GaussianPositiveFloor
public import SHE.CoveredOldResidualCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.FullResidualFrameRange
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores StoppedScoreLeverage GaussianRangeSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
local instance fullResidualFrameRange_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- One genuine common history event works for ALL coefficient parameters,
including an uncountable parameter set. It is obtained from the fixed
unweighted Gram range before introducing any parameter. -/
theorem row_mem_all_ranges_ae {ι : Type*} (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (c : ι→Domain→ℝ)
    (hc : ∀ θ,Measurable (c θ)) {ell M : ℝ} (hell : 0<ell)
    (hb : ∀ θ p,ell≤c θ p ∧ c θ p≤M) :
    ∀ᵐ p ∂historyMeasure q,∀ θ,stoppedRow σ target center p∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center (c θ) q)).range := by
  have he : Matrix.gram ℝ (referenceFeature σ target center hages q)=
      stoppedCovariance σ target center (fun _=>1) q := by
    exact weightedFeature_gram σ target center (fun _=>1) measurable_const 1 (fun _=>by norm_num) hages q
  have hmul : stoppedCovariance σ target center (fun _=>ell) q=
      ell • stoppedCovariance σ target center (fun _=>1) q := by
    simpa only [mul_one] using StoppedCovarianceSplit.covariance_const_mul σ target center q (fun _=>1) ell
  have hrange : (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center (fun _=>ell) q)).range=
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center (fun _=>1) q)).range := by
    rw [hmul,covariance_range_smul _ hell.ne']
  filter_upwards [row_mem_reference_range_ae σ target center hages q] with p hp
  rw [he,←hrange] at hp
  intro θ
  exact StoppedCovarianceOrder.range_mono σ target center hages q (fun _=>ell) (c θ)
    measurable_const (hc θ) (fun _=>⟨hell.le,le_rfl⟩)
    (fun p=>⟨hell.le.trans (hb θ p).1,(hb θ p).2⟩) (fun p=>(hb θ p).1) hp

theorem residual_row_all_parameters_ae (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (old : ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (hb : ∀ p,0≤old p ∧ old p≤P.lower/2)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ i,σ i≤target i) (q : ℝ) :
    ∀ᵐ p ∂historyMeasure q,∀ θ : ℝ,stoppedRow σ target center p∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ)
        (ControlledFixedReserve.covariance P Λ u d old σ target center q θ)).range := by
  apply row_mem_all_ranges_ae σ target center hages q (ControlledFixedReserve.coefficient P Λ u d old)
    (fun θ=>((ControlledProfile.profile_measurable P Λ u d).comp
      (measurable_const.prodMk measurable_id)).sub hold) (half_pos P.lower_pos)
  intro θ p
  have hh := ControlledFixedReserve.coefficient_bounds P Λ u d old hb θ p
  constructor <;> linarith

variable {X : Type} [MeasurableSpace X]

/-- Actual full-residual covariance marks use the covered stopped row.
Its fresh Gaussian range is concluded on genuine history×input events;
there is no common-front range premise and no change of original targets. -/
theorem actual_full_residual_row_range_ae (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u d : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u d θ) X n)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u d θ) ρ k,
      ∀ q : ℝ,0≤q → q≤(carrier L k).terminal p →
      ∀ᵐ r ∂historyMeasure q,stoppedRow (stops L k p) (targets L k p) (centers L k p) r∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ)
          (fullResidualCovariance L (referenceProfile P Λ u d) k p q)).range := by
  filter_upwards [full_residual_eq_fixedReserve_ae P ha Λ u d θ L hages ρ k] with p hp
  intro q hq hqt
  rw [hp q hq hqt]
  have hgeom (i : Fin (n+k)) : stops L k p i≤targets L k p i :=
    (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages L hages k p i)
  exact (residual_row_all_parameters_ae P Λ u d (fixedProfile P Λ u d (lower L k p) (upper L k p))
    (fixedProfile_measurable P Λ u d _ _) (fixedProfile_bounds P Λ u d _ _ (disjoint L k p))
    (stops L k p) (targets L k p) (centers L k p) hgeom q).mono (fun _ hh=>hh θ)

end SHE.FullResidualFrameRange
