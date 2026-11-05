module

public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledReferenceFamilyLevel
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledReferenceFamilyLevel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))

/-- The actual canonical controlled reference family with an arbitrary
measurable root-observation parameter. This includes spatial scalar
roots, whose original stop and target may coincide. -/
def level (p : Inputs) : Level (referenceData P A hA Λ θ v b hvb p) X n where
  observations := Z
  terminal := fun _ => b
  terminal_measurable := measurable_const
  terminal_base := fun _ => by exact_mod_cast hvb
  terminal_horizon := fun _ => le_rfl
  targets_after := htarget
  stops_after := hstop
  test := F
  test_uniform := hF
  test_measurable := hFm

end SHE.ControlledReferenceFamilyLevel
