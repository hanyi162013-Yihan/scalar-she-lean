module

public import SHE.ControlledFullFutureScore
public import SHE.CoveredOldResidualCovariance
public import SHE.GlobalPointDensity
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.CoveredHistoryGeometry
open CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- Initial stops below the initial terminal remain so after every
literal insertion. This is the precise condition under which covered
stop clipping leaves the exponential noise weights unchanged. -/
theorem carrier_stops_le_initial (L : CutoffWordLevel.Level R X n)
    (hstop : ∀ p i,(L.observations.observations p i).stop≤L.terminal p)
    (k : ℕ) (p : History X k) (i : Fin (n+k)) :
    ((carrier L k).observations.observations p i).stop ≤ initialTerminal L k p := by
  induction k with
  | zero => exact hstop p i
  | succ k ih =>
    refine Fin.cases ?_ (fun i=>ih p.1 i) i
    exact ((carrier L k).nodeTime_mem p).2.trans (terminal_le_initial L k p.1)

end SHE.CoveredHistoryGeometry

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry ControlledOldIntervals
  MeasurableGaussianScores StopWeightedRows
open scoped BigOperators
local instance fullResidualScoreDensity_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X]
variable (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X 1)

/-- The actual full-residual weighted first-score scale has exactly the
old-score parent density already used by spatial forest integration.
The hypothesis on INITIAL stops is retained explicitly: clipping a stop
without also changing its damping weight is not valid. -/
theorem weighted_full_score_density_ae (hΛ : 0≤Λ)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (hstop : ∀ p i,(L.observations.observations p i).stop≤L.terminal p)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) ρ k,
      ∀ {q r : ℝ},0≤q → q≤r → r<(carrier L k).terminal p →
      (∀ i,((carrier L k).observations.observations p i).target-r≤H) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        let Z := (carrier L k).observations.observations p
        let B := fullResidualCovariance L (referenceProfile P Λ u dir) k p q
        weightedHeatRow Λ Z q r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) B).range ∧
          sqrt (scoreVariance B (weightedHeatRow Λ Z q r y))*
            scoreProduct L Z (referenceProfile P Λ u dir) k p≤
            sqrt (2*C/(P.lower*((carrier L k).terminal p-r)))*
              globalDensity L (referenceProfile P Λ u dir) k p r y := by
  let c := referenceProfile P Λ u dir
  have hc : Measurable c := referenceProfile_measurable P Λ u dir
  have hb (z : Domain) : fraction P*P.lower≤c z ∧
      c z≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference z :=
    ⟨(referenceProfile_bounds P Λ u dir z).1,
      (referenceProfile_bounds P Λ u dir z).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,z)).1)⟩
  obtain ⟨H,C,hH,hC,hV⟩ := ControlledFixedReserve.weighted_residual_sqrt_heat_envelope (1+k)
  refine ⟨H,C,hH,hC,?_⟩
  filter_upwards [full_residual_eq_fixedReserve_ae P ha Λ u dir θ L hages ρ k,
    actual_scoreProduct_nonneg_ae L c hc (mul_pos (fraction_pos P) P.lower_pos) hb hages ρ k] with p hp hn
  intro q r hq hqr hr hsmall
  let Z := (carrier L k).observations.observations p
  have hσ : stops L k p=(fun i=>(Z i).stop) := by
    funext i
    exact min_eq_left (carrier_stops_le_initial L hstop k p i)
  have hqhi : q≤(carrier L k).terminal p := hqr.trans hr.le
  have hres := hp q hq hqhi
  rw [hσ] at hres
  have hh := hV P hΛ u dir (fixedProfile P Λ u dir (lower L k p) (upper L k p))
    (fixedProfile_measurable P Λ u dir _ _)
    (fixedProfile_bounds P Λ u dir _ _ (disjoint L k p)) Z
    (RecursiveScoreSupport.carrier_ages L hages k p) hq hqr hr
    ((carrier L k).stops_after p) hsmall θ
  filter_upwards [hh] with y hy
  dsimp only
  have hrow := hy.1
  change weightedHeatRow Λ Z q r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
    (ControlledFixedReserve.covariance P Λ u dir
      (fixedProfile P Λ u dir (lower L k p) (upper L k p))
      (fun i=>(Z i).stop) (targets L k p) (centers L k p) q θ)).range at hrow
  rw [←hres] at hrow
  refine ⟨hrow,?_⟩
  rw [hres]
  have hs := mul_le_mul_of_nonneg_right hy.2 hn
  change 0≤scoreProduct L ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) k p at hn
  simp only [globalDensity,max_eq_left hn]
  convert! hs using 1 <;> ac_rfl

end SHE.ScalarMeanEnvelope
