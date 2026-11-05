module

public import SHE.FullPredictablePhysicalWord
public import SHE.ControlledOldIntervals
public import SHE.CanonicalCutoffWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledWordLevel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  SmoothCylinders ControlledProfile ControlledOldIntervals

/-- The literal controlled profile, with its damped original-target mean,
initializes the same physical recursive words. -/
def referenceData (P : CanonicalCovariance.ProfileParameters) (ha : BoundedSmooth P.coefficient)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) : ReferenceData where
  totalVariance := P.coefficient
  totalVariance_smooth := ha
  reference := fun p => profile P Λ u d (θ,p)
  reference_measurable := (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  upper := P.upper
  upper_nonneg := P.upper_nonneg
  reference_bound := fun p => by
    rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ u d (θ,p)).1)]
    exact (profile_bounds P Λ u d (θ,p)).2
  reference_nonneg := fun p => P.lower_pos.le.trans (profile_bounds P Λ u d (θ,p)).1
  base := 0
  horizon := P.horizon
  base_nonneg := le_rfl
  ordered := P.horizon_pos.le

def initialLevel (P : CanonicalCovariance.ProfileParameters) (ha : BoundedSmooth P.coefficient)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) {n : ℕ} (Z : Fin n → Observation)
    (h : ℝ) (hh : h ∈ Icc 0 P.horizon) (ht : ∀ i,h ≤ (Z i).target)
    (hs : ∀ i,h ≤ (Z i).stop) {F : WordRecursion.State n → ℝ} (hF : BoundedSmooth F) :
    Level (referenceData P ha Λ u d θ) Unit n where
  observations := VariableObservations.Family.fixed Z
  terminal := fun _ => h
  terminal_measurable := measurable_const
  terminal_base := fun _ => hh.1
  terminal_horizon := fun _ => hh.2
  targets_after := fun _ => ht
  stops_after := fun _ => hs
  test := fun _ => F
  test_uniform := UniformSmooth.UniformBoundedSmooth.fixed hF
  test_measurable := hF.smooth.continuous.measurable.comp measurable_snd

/-- Interpolation changes profiles and tests, but the genuine history
measure stays fixed, so all parameter averages use the same history space. -/
theorem historyMeasure_eq (P : CanonicalCovariance.ProfileParameters) (ha : BoundedSmooth P.coefficient)
    (Λ : ℝ) (u d : CircleL2) (θ η : ℝ) {X : Type*} [MeasurableSpace X] (μ : Measure X) (k : ℕ) :
    historyMeasure (referenceData P ha Λ u d θ) μ k =
      historyMeasure (referenceData P ha Λ u d η) μ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (historyMeasure (referenceData P ha Λ u d θ) μ k).prod (nodeMeasure _) =
      (historyMeasure (referenceData P ha Λ u d η) μ k).prod (nodeMeasure _)
    rw [ih]
    rfl

/-- The fixed-old physical word representation applies to the genuine
controlled-profile recursive level, with its range, triangular support
and reserved covariance applicability all discharged. -/
theorem predictable_representation (P : CanonicalCovariance.ProfileParameters)
    (ha : BoundedSmooth P.coefficient) (Λ : ℝ) (u d : CircleL2) (θ : ℝ)
    {n : ℕ} (Z : Fin n → Observation) (h : ℝ) (hh : h ∈ Icc 0 P.horizon)
    (ht : ∀ i,h ≤ (Z i).target) (hs : ∀ i,h ≤ (Z i).stop)
    (hages : ∀ i,(Z i).stop ≤ (Z i).target)
    {F : WordRecursion.State n → ℝ} (hF : BoundedSmooth F) (k : ℕ) :
    let L := initialLevel P ha Λ u d θ Z h hh ht hs hF
    ∀ᵐ p ∂historyMeasure (referenceData P ha Λ u d θ) (Measure.dirac ()) k,
      (PhysicalChainArrays.reserve L (referenceProfile P Λ u d) k p).PosSemidef ∧
        ∀ z : WordRecursion.State (n+k),
          GaussianConvolution.gaussianAverage (PhysicalScoreChain.initialCovariance L k p)
            (UncutSmoothWords.test L k p) z =
          GaussianConvolution.gaussianAverage (PhysicalChainArrays.reserve L (referenceProfile P Λ u d) k p)
            (PhysicalChainArrays.oldAverage L (referenceProfile P Λ u d) k p) z := by
  intro L
  exact PhysicalChainArrays.predictable_eq_old_average_ae L (referenceProfile P Λ u d)
    (referenceProfile_measurable P Λ u d) (mul_pos (fraction_pos P) P.lower_pos)
    (fun p => ⟨(referenceProfile_bounds P Λ u d p).1,
      (referenceProfile_bounds P Λ u d p).2.trans ((half_le_self P.lower_pos.le).trans
        (profile_bounds P Λ u d (θ,p)).1)⟩)
    (fun _ i => hages i) (Measure.dirac ()) k

end SHE.ControlledWordLevel
