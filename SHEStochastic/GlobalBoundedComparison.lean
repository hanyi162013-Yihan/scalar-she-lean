module

public import SHEStochastic.GlobalBoundedNativeSingleEquation
public import SHEStochastic.ProjectedContinuationRecovery
public import SHEStochastic.JointPathState

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.GlobalBoundedComparison
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  SHE.FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0) (hH : 0<H)
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)))) (u : RealL2)

/-- The precise bounded native uniqueness statement needed for
localization. It compares actual mild solutions and their state laws;
it contains no exit time, continuation kernel or unbounded equation.
The remaining bounded-proof interface wiring is kept explicit here. -/
def Holds : Prop :=
  ∀ (μ ν : Measure (JointPathFiltration.Space (E := RealL2) (ι := ι) H))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : FiniteScalarIto.Family (JointPathFiltration.filtration (E := RealL2) (ι := ι) H) μ H ι)
    (Q : FiniteScalarIto.Family (JointPathFiltration.filtration (E := RealL2) (ι := ι) H) ν H ι),
    JointPathState.state H 0 =ᵐ[μ] (fun _ ↦ u) →
    JointPathState.state H 0 =ᵐ[ν] (fun _ ↦ u) →
    GlobalBoundedFourierRecognition.HasClosedVersion (JointPathFiltration.filtration H) μ H
      (JointPathState.state H) (JointPathState.predictable H) hg hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) (JointPathState.state H 0) →
    GlobalBoundedFourierRecognition.HasClosedVersion (JointPathFiltration.filtration H) ν H
      (JointPathState.state H) (JointPathState.predictable H) hg hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto Q.toCoordinates e) (JointPathState.state H 0) →
    μ.map (ProjectedContinuationRecovery.project H) = ν.map (ProjectedContinuationRecovery.project H)

end SHEStochastic.GlobalBoundedComparison
