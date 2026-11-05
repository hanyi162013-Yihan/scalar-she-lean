module

public import SHE.NativeFirstWholeOffsets
public import SHE.NativeFirstWholeAverage
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.NativeFirstWholeMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance nativeFirstWholeFibre_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n d r m : ℕ}

/-- Literal omitted-leaf fibre integral, under the SAME physical old
fractions and full residual as the original word. -/
def fibreAverage (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ q : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : State n) (D : Fin r→State n) (E:State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ) : ℝ :=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let R:=NativeFirstScoreReserve.covariance P σ target center q
  let C:=ControlledFixedReserve.covariance P Λ u d0
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
  ∫ x,word A D R E choices P.coefficient F (fun _ : Unit=>mean) g leaf
      (fun j=>ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) ((),x)
    ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod ((multivariateGaussian (0 : State n) R).prod (multivariateGaussian (0 : State n) C))


end SHE.NativeFirstWholeMoments
