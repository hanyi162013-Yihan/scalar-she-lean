module

public import SHEStochastic.GlobalBoundedComparison
public import SHEStochastic.NativeGlobalUniqueness
public import SHEStochastic.BoundedScalarData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.GlobalBoundedComparisonProof
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace PhysicalOriginalHeatRows.Noise := borel _
local instance : BorelSpace PhysicalOriginalHeatRows.Noise := ⟨rfl⟩

/-- The bounded comparison premise in the unbounded cutoff reduction
is discharged by the original local uniqueness proof, with all seven
stochastic inputs proved for the same native integrals. -/
theorem holds {ι : Type} [Countable ι] [DecidableEq ι]
    (H : ℝ≥0) (hH : 0<H)
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ1 : β<1)
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖≤B)
    (e : HilbertBasis ι ℝ PhysicalOriginalHeatRows.Noise) (u : RealL2)
    (ell : ℝ) (hell : 0<ell) (hel : ∀ z, ell≤(g z)^2) :
    GlobalBoundedComparison.Holds H hH hg hβ hβ1 B hb e u := by
  intro μ ν hμ hν P Q hInitP hInitQ hMildP hMildQ
  letI : SecondCountableTopology PhysicalOriginalHeatRows.Noise := e.repr.toHomeomorph.secondCountableTopology
  let Space := JointPathFiltration.Space (E := RealL2) (ι := ι) H
  let F := JointPathFiltration.filtration (E := RealL2) (ι := ι) H
  let W := JointPathState.state (E := RealL2) (ι := ι) H
  let D := BoundedScalarData.data hg hβ B hb ell hell hel
  let masses : Bool → Measure Space := fun b ↦ Bool.rec ν μ b
  let probs : ∀ b : Bool, IsProbabilityMeasure (masses b) := Bool.rec hν hμ
  letI : ∀ b : Bool, IsProbabilityMeasure (masses b) := probs
  let J : ∀ b : Bool, StandardTerminalIto (C := RealL2) (E := ℝ) F (masses b) H := Bool.rec
    (restrictNoise (FiniteCylindricalIto.terminalIto Q.toCoordinates e) NativePhysicalState.push)
    (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) NativePhysicalState.push)
  have hJfalse : J false = restrictNoise (FiniteCylindricalIto.terminalIto Q.toCoordinates e) NativePhysicalState.push := rfl
  have hJtrue : J true = restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) NativePhysicalState.push := rfl
  let S : ∀ b : Bool, @SingleNativeHeatEquation.Data Space _ F (masses b) (probs b) H D (J b) u := Bool.rec
    (GlobalBoundedNativeSingleEquation.data F ν H D W (JointPathState.predictable H) hg hβ hβ1 B hb
      hH (FiniteCylindricalIto.terminalIto Q.toCoordinates e) u (W 0) hInitQ
      (JointPathState.continuous H) hMildQ)
    (GlobalBoundedNativeSingleEquation.data F μ H D W (JointPathState.predictable H) hg hβ hβ1 B hb
      hH (FiniteCylindricalIto.terminalIto P.toCoordinates e) u (W 0) hInitP
      (JointPathState.continuous H) hMildP)
  let M : ∀ b : Bool, @NativeScalarModel.Model Space RealL2 _ _ _ _ F (masses b) (probs b) H (J b) := Bool.rec
    (NativeScalarModel.unitary (NativeScalarModel.ofFamily Q e) NativePhysicalState.equivalence)
    (NativeScalarModel.unitary (NativeScalarModel.ofFamily P e) NativePhysicalState.equivalence)
  have he := @NativeGlobalUniqueness.laws_eq Bool inferInstance inferInstance (fun _ : Bool ↦ Space)
    (fun _ ↦ inferInstance) (fun _ ↦ F) masses probs H hH
    D J u S M true false
  have hEq := congrArg (fun p ↦ p.toMeasure) he
  change μ.map (NativeContinuousPath.path H W (JointPathState.continuous H)) =
    ν.map (NativeContinuousPath.path H W (JointPathState.continuous H)) at hEq
  have hPath : NativeContinuousPath.path H W (JointPathState.continuous H) =
      ProjectedContinuationRecovery.project H := by
    funext x
    exact JointPathState.path H x
  rwa [hPath] at hEq

end SHEStochastic.GlobalBoundedComparisonProof
