module

public import SHE.NativeFirstScoreAverage
public import SHE.CoveredTerminalMoments
public import SHE.RangeTerminalNorm
public import SHE.ActualMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2700000
noncomputable section

namespace SHE.NativePhysicalWord
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  PhysicalParentGeometry CoveredTerminalFactors CoveredTerminalMoments StoppedGaussianScore
  PhysicalProfile PhysicalMeanSemigroup
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω] {R : ReferenceData} {n : ℕ}

def unitCenters (L : CutoffWordLevel.Level R X n) (k : ℕ) (p : History X k) : Fin (n+k)→UnitAddCircle :=
  fun i => NativeHeatSpan.unitCenter (((carrier L k).observations.observations p i).center)

theorem native_centers (L : CutoffWordLevel.Level R X n) (k : ℕ) (p : History X k) :
    nativeCenter (unitCenters L k p)=centers L k p := by
  funext i
  exact NativeHeatSpan.scale_inverse _

variable (P : CanonicalCovariance.ProfileParameters)
variable (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

/-- The word used by the actual native moment estimate is literally
the original recursive assigned word, with all original factors. The
identity is independent of any law for the current mean. -/
theorem word_eq (k : ℕ) (p : History X k) {q : ℝ} (hq0 : 0≤q) (hq : q≤(carrier L k).terminal p)
    (direction : WordRecursion.State (n+k)) (mean : Ω→WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) (z : Ω×((Fin (k+1)→WordRecursion.State (n+k))×WordRecursion.State (n+k))) :
    NativeFirstScoreWordMoments.word P.coefficient flags
      (familyCovariance (stops L k p) (targets L k p) (nativeCenter (unitCenters L k p))
        (referenceProfile P Λ u dir) (lowerWith L k p q) (upperWith L k p))
      (Fin.cons direction (directions L ((carrier L k).observations.observations p) k p))
      (liftChoices choices) (L.test (rootParameter k p)) mean
      (rootSelector k (fun i => i)) (leafIndex k (fun i => i))
      (fun j => ControlledProfile.profile P Λ u dir
        (θ,(targets L k p (leafIndex k (fun i => i) j),nativeCenter (unitCenters L k p) (leafIndex k (fun i => i) j)))) z=
    rangeAssignedWord L (referenceProfile P Λ u dir) k p q direction (mean z.1) choices z.2 := by
  rw [native_centers L k p,old_eq L _ k p hq0 hq]
  have hb : (fun j => ControlledProfile.profile P Λ u dir
      (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j))))=
      baseline L k p := funext (fun j => (baseline_eq P ha Λ u dir θ L k p j).symm)
  rw [hb]
  rfl

end SHE.NativePhysicalWord
