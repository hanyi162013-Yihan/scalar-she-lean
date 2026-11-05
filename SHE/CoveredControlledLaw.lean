module

public import SHE.CoveredHistoryGeometry
public import SHE.ControlledWordLevel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.CoveredControlledLaw
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry ControlledOldIntervals
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

def stops (L : CutoffWordLevel.Level R X n) (k : ℕ) (p : History X k) : Fin (n+k)→ℝ :=
  fun i => min ((carrier L k).observations.observations p i).stop (initialTerminal L k p)

def targets (L : CutoffWordLevel.Level R X n) (k : ℕ) (p : History X k) : Fin (n+k)→ℝ :=
  fun i => ((carrier L k).observations.observations p i).target

def centers (L : CutoffWordLevel.Level R X n) (k : ℕ) (p : History X k) : Fin (n+k)→HeatCircle :=
  fun i => ((carrier L k).observations.observations p i).center

theorem old_eq (L : CutoffWordLevel.Level R X n) (c : Domain→ℝ)
    (k : ℕ) (p : History X k) {q : ℝ} (hq : 0≤q) (hqt : q≤(carrier L k).terminal p) :
    familyCovariance (stops L k p) (targets L k p) (centers L k p) c
      (lowerWith L k p q) (upperWith L k p)=
    GaussianFreshFraction.covariances
      (intervalCovariance ((carrier L k).observations.observations p) c q ((carrier L k).terminal p))
      (covariances L ((carrier L k).observations.observations p) c k p) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact CoveredControlledCovariance.interval_clip_upper _ c hq (terminal_le_initial L k p)
  · exact CoveredControlledCovariance.interval_clip_upper _ c
      (hq.trans (hqt.trans (terminal_le_lower L k p j))) (upper_le_initial L k p j)

/-- The actual terminal residual of the recursive controlled word is
the canonical positive residual on the clipped covered window. This is
an equality of the literal covariance matrices, not a replacement by a
larger Gaussian law or an assumed compatibility relation. -/
theorem residual_eq_ae (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) μ k,
      ∀ q : ℝ,0≤q → q≤(carrier L k).terminal p →
      let Z := (carrier L k).observations.observations p
      (intervalCovariance Z (fun r => ControlledProfile.profile P Λ u dir (θ,r)-referenceProfile P Λ u dir r)
          q ((carrier L k).terminal p)+
        ∑ j,covariances L Z
          (fun r => ControlledProfile.profile P Λ u dir (θ,r)-referenceProfile P Λ u dir r) k p j)=
      ControlledFixedReserve.covariance P Λ u dir
        (fixedProfile P Λ u dir (lowerWith L k p q) (upperWith L k p))
        (stops L k p) (targets L k p) (centers L k p) q θ := by
  have hb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [CoveredControlledCovariance.terminal_decomposition_ae L _
    (referenceProfile_measurable P Λ u dir) (mul_pos (fraction_pos P) P.lower_pos) hb hages μ k] with p hp
  intro q hq hqt
  have hZ (i : Fin (n+k)) : stops L k p i≤targets L k p i :=
    (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages L hages k p i)
  have hc := ControlledWindowDecomposition.covariance_sum_residual P Λ u dir θ
    (lowerWith L k p q) (upperWith L k p) (disjointWith L k p q)
    (stops L k p) (targets L k p) (centers L k p) hZ hq (lowerWith_bound L k p hqt)
  rw [old_eq L _ k p hq hqt] at hc
  have ht := hp q hq hqt
  dsimp only at ht
  apply add_left_cancel
  exact ht.trans hc.symm

theorem measure_eq_ae (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) μ k,
      ∀ q : ℝ,0≤q → q≤(carrier L k).terminal p →
      terminalAssignedMeasure L (referenceProfile P Λ u dir) k p q=
      (Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k))
        (familyCovariance (stops L k p) (targets L k p) (centers L k p)
          (referenceProfile P Λ u dir) (lowerWith L k p q) (upperWith L k p) j))).prod
        (multivariateGaussian 0 (ControlledFixedReserve.covariance P Λ u dir
          (fixedProfile P Λ u dir (lowerWith L k p q) (upperWith L k p))
          (stops L k p) (targets L k p) (centers L k p) q θ)) := by
  filter_upwards [residual_eq_ae P ha Λ u dir θ L hages μ k] with p hp
  intro q hq hqt
  unfold terminalAssignedMeasure
  dsimp only
  rw [←old_eq L _ k p hq hqt]
  rw [show (ControlledWordLevel.referenceData P ha Λ u dir θ).reference=
    (fun r => ControlledProfile.profile P Λ u dir (θ,r)) by rfl]
  rw [hp q hq hqt]

end SHE.CoveredControlledLaw
