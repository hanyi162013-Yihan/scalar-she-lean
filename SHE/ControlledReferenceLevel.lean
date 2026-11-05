module

public import SHE.ControlledReferenceCovariance
public import SHE.MixedJointPastExpectedLevel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledReferenceLevel
open Set MeasureTheory StoppedFourier ControlledProfile ControlledReferenceWindows
open WordRecursion CutoffWordLevel SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledReferenceLevel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceLevel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceLevel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)

/-- A deterministic member of the ACTUAL controlled reference family.
The parameter will later be the F_v-random pair (U_v,V_v-U_v). -/
def referenceData (p : Inputs) : ReferenceData where
  totalVariance := A
  totalVariance_smooth := hA
  reference := coefficient P Λ θ v p
  reference_measurable := coefficient_section_measurable P Λ θ v p
  upper := P.upper
  upper_nonneg := P.upper_nonneg
  reference_bound := coefficient_abs_bound P Λ θ v p
  reference_nonneg := fun z => P.lower_pos.le.trans (coefficient_bounds P Λ θ v p z).1
  base := v
  horizon := b
  base_nonneg := v.2
  ordered := by exact_mod_cast hvb

variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)

def level (p : Inputs) : Level (referenceData P A hA Λ θ v b hvb p) Unit n where
  observations := {
    observations := fun _ => Z
    stop_measurable := fun _ => measurable_const
    target_measurable := fun _ => measurable_const
    center_measurable := fun _ => measurable_const }
  terminal := fun _ => b
  terminal_measurable := measurable_const
  terminal_base := fun _ => by exact_mod_cast hvb
  terminal_horizon := fun _ => le_rfl
  targets_after := fun _ => htarget
  stops_after := fun _ => hstop
  test := fun _ => F
  test_uniform := UniformBoundedSmooth.fixed hF
  test_measurable := hF.smooth.continuous.measurable.comp measurable_snd

theorem window_eq (p : Inputs) :
    (level P A hA Λ θ v b hvb Z htarget hstop F hF p).window ()=
      ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p := rfl

end SHE.ControlledReferenceLevel
