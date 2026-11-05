module

public import SHE.ObservationOldTimeShift
public import SHE.ControlledReferenceWindows
public import SHE.ControlledOldIntervals

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

/-! The canonical controlled reference based at a past v is exactly a
time translate of its relative-age profile. This identifies its actual
old/fresh Gaussian product law, retaining all individual original stops. -/
namespace SHE.ControlledProfileTimeShift
open Set MeasureTheory ProbabilityTheory AddCircle WordRecursion StoppedFourier
  StoppedGaussianFeatures OldIntervalCovariance ControlledOldIntervals ObservationTimeShift
open scoped Topology BigOperators
local instance controlledProfileTimeShift_period : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}
variable (P : CanonicalCovariance.ProfileParameters) (Λ θ v : ℝ)
  (u d : CircleL2)

/-- The reference used by the actual random-past family has the correct
relative age, rather than the age from the original initial time. -/
theorem coefficient_eq : ControlledReferenceWindows.coefficient P Λ θ v (u,d)=
    ObservationTimeShift.profile v (fun p=>ControlledProfile.profile P Λ u d (θ,p)) := rfl

theorem coefficient_translation (p : Domain) :
    ControlledReferenceWindows.coefficient P Λ θ v (u,d) (translation v p)=
      ControlledProfile.profile P Λ u d (θ,p) := by
  rw [coefficient_eq,profile_translation]

theorem covariance_translation (q s : ℝ) (Z : Fin n → Observation) :
    WordRecursion.covariance (ControlledReferenceWindows.coefficient P Λ θ v (u,d))
      (observations v Z) (q+v) (s+v)=
    WordRecursion.covariance (fun p=>ControlledProfile.profile P Λ u d (θ,p)) Z q s := by
  rw [coefficient_eq,ObservationTimeShift.covariance_translation]

theorem stoppedCovariance_translation (q : ℝ) (σ target : Fin n→ℝ)
    (center : Fin n→HeatCircle) :
    StoppedGaussianFeatures.stoppedCovariance (fun i=>σ i+v) (fun i=>target i+v) center
      (ControlledReferenceWindows.coefficient P Λ θ v (u,d)) (q+v)=
    StoppedGaussianFeatures.stoppedCovariance σ target center
      (fun p=>ControlledProfile.profile P Λ u d (θ,p)) q := by
  rw [coefficient_eq,ObservationTimeShift.stoppedCovariance_translation]

/-- The old profile uses theta zero, including after an arbitrary actual
random past-input substitution. -/
def oldProfile : Domain→ℝ :=
  ObservationTimeShift.profile v (referenceProfile P Λ u d)

def fixedOldProfile (lo hi : Fin r→ℝ) : Domain→ℝ :=
  sumProfile (oldProfile P Λ v u d) (fun j=>lo j+v) (fun j=>hi j+v)

theorem fixedOldProfile_eq (lo hi : Fin r→ℝ) :
    fixedOldProfile P Λ v u d lo hi=
      ObservationTimeShift.profile v (fixedProfile P Λ u d lo hi) := by
  exact sumProfile_translation v lo hi (referenceProfile P Λ u d)

/-- Full fresh residual covariance after removing the same old fractions.
No common-window covariance is substituted for the stopped history. -/
theorem residualCovariance_translation (q : ℝ) (σ target : Fin n→ℝ)
    (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) :
    StoppedGaussianFeatures.stoppedCovariance (fun i=>σ i+v) (fun i=>target i+v) center
      (fun p=>ControlledReferenceWindows.coefficient P Λ θ v (u,d) p-
        fixedOldProfile P Λ v u d lo hi p) (q+v)=
    ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center q θ := by
  rw [fixedOldProfile_eq,coefficient_eq]
  change StoppedGaussianFeatures.stoppedCovariance (fun i=>σ i+v) (fun i=>target i+v) center
    (ObservationTimeShift.profile v (ControlledFixedReserve.coefficient P Λ u d
      (fixedProfile P Λ u d lo hi) θ)) (q+v)=_
  exact ObservationTimeShift.stoppedCovariance_translation v q σ target center _

theorem oldCovariance_translation (hv : 0≤v) (σ target : Fin n→ℝ)
    (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) (hlo : ∀ j,0≤lo j) (j : Fin r) :
    familyCovariance (fun i=>σ i+v) (fun i=>target i+v) center (oldProfile P Λ v u d)
      (fun j=>lo j+v) (fun j=>hi j+v) j=
      familyCovariance σ target center (referenceProfile P Λ u d) lo hi j :=
  ObservationOldTimeShift.familyCovariance_translation v hv σ target center
    (referenceProfile P Λ u d) lo hi hlo j

/-- Equality of the literal old-increment/fresh-residual product law
used by the assigned word, with the original stopping times preserved.
This is pointwise in BOTH reference inputs, hence also valid after
measurable past-dependent substitution. -/
theorem gaussianProduct_translation (hv : 0≤v) (q : ℝ) (σ target : Fin n→ℝ)
    (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) (hlo : ∀ j,0≤lo j) :
    (Measure.pi (fun j=>multivariateGaussian (0 : State n)
      (familyCovariance (fun i=>σ i+v) (fun i=>target i+v) center (oldProfile P Λ v u d)
        (fun j=>lo j+v) (fun j=>hi j+v) j))).prod
      (multivariateGaussian (0 : State n)
        (StoppedGaussianFeatures.stoppedCovariance (fun i=>σ i+v) (fun i=>target i+v) center
          (fun p=>ControlledReferenceWindows.coefficient P Λ θ v (u,d) p-
            fixedOldProfile P Λ v u d lo hi p) (q+v)))=
    (Measure.pi (fun j=>multivariateGaussian (0 : State n)
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j))).prod
      (multivariateGaussian (0 : State n)
        (ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
          σ target center q θ)) := by
  rw [residualCovariance_translation]
  congr 1
  exact ObservationOldTimeShift.oldGaussianProduct_translation v hv σ target center
    (referenceProfile P Λ u d) lo hi hlo

/-- Original full-profile leaf baselines are unchanged by the shift. -/
theorem leafBaseline_translation (target : ℝ) (center : HeatCircle) :
    ControlledReferenceWindows.coefficient P Λ θ v (u,d) (target+v,center)=
      ControlledProfile.profile P Λ u d (θ,(target,center)) :=
  coefficient_translation P Λ θ v u d (target,center)

end SHE.ControlledProfileTimeShift
