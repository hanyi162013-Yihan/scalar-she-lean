module

public import SHE.OmittedPhysicalIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.PhysicalChainArrays
open MeasureTheory WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates PhysicalScoreChain StoppedGaussianFeatures GaussianAssignmentBlocks
open scoped BigOperators
local instance omittedWordPhysicalBridge_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- Erasing a leaf means erasing it BEFORE assigning old fractions.
Every assignment hitting that constant factor vanishes, while an empty
block leaves the literal original omitted word and full baselines. -/
theorem omitted_assigned_eq_word (L : CutoffWordLevel.Level R X n) (c : Domain→ℝ)
    (k : ℕ) (h : History X k) (mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) (j0 : Fin k)
    (x : (Fin k→WordRecursion.State (n+k))×WordRecursion.State (n+k)) :
    omittedAssignedWord L c k h mean choices j0 x=
      if block choices j0.succ=[] then
        OmittedAssignedMoments.word
          (covariances L ((carrier L k).observations.observations h) c k h)
          (directions L ((carrier L k).observations.observations h) k h)
          choices j0 R.totalVariance (L.test (rootParameter k h)) (fun _ : Unit=>mean)
          (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k h) ((),x) else 0 := by
  by_cases hb : block choices j0.succ=[]
  · simp only [omittedAssignedWord,OmittedAssignmentIdentity.value,OmittedAssignmentIdentity.testValue,
      ite_eq_left hb,OmittedAssignedMoments.word,OmittedAssignedMoments.oldScores]
    ring
  · simp only [omittedAssignedWord,OmittedAssignmentIdentity.value,OmittedAssignmentIdentity.testValue,
      ite_eq_right hb,mul_zero]

end SHE.PhysicalChainArrays
