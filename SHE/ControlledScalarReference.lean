module

public import SHE.ControlledReferenceFamilyLevel
public import SHE.ScalarRootLevel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledScalarReference
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledScalarReference_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

def observations (b : ℝ≥0) : VariableObservations.Family HeatCircle 1 where
  observations := fun x _ => ⟨b,b,x⟩
  stop_measurable := fun _ => measurable_const
  target_measurable := fun _ => measurable_const
  center_measurable := fun _ => measurable_id

def test (g : ℝ→ℝ) (ψ : HeatCircle→ℝ) : HeatCircle→WordRecursion.State 1→ℝ := fun x z => ψ x*g (z 0)

variable (g : ℝ→ℝ) (hg : BoundedSmooth g) (ψ : HeatCircle→ℝ) (hψ : Measurable ψ)
variable {W : ℝ} (hW : 0≤W) (hbψ : ∀ x,|ψ x|≤W)
include hg hW hbψ in
theorem test_uniform : UniformBoundedSmooth (test g ψ) := by
  have hp : UniformBoundedSmooth (fun x (_ : WordRecursion.State 1) => ψ x) :=
    UniformBoundedSmooth.parameter_const ψ hW (fun x => by simpa only [Real.norm_eq_abs] using hbψ x)
  have hg' : UniformBoundedSmooth (fun _ : HeatCircle => g) := UniformBoundedSmooth.fixed hg
  exact hp.mul (hg'.comp_right (EuclideanSpace.proj (0:Fin 1)))

include hg hψ in
theorem test_measurable : Measurable (fun q : HeatCircle×WordRecursion.State 1 => test g ψ q.1 q.2) :=
  (hψ.comp measurable_fst).mul
    (hg.smooth.continuous.measurable.comp ((EuclideanSpace.proj (0:Fin 1)).continuous.measurable.comp measurable_snd))

variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
local notation "R" => ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb

/-- The actual scalar root has original stop=target=b, while the
canonical controlled reference depends on both original past inputs. -/
def level (p : Inputs) : Level (R p) HeatCircle 1 :=
  ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb
    (observations b) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (test g ψ)
    (test_uniform g hg ψ hW hbψ) (test_measurable g hg ψ hψ) p

theorem level_eq_scalar (p : Inputs) : level g hg ψ hψ hW hbψ P A hA Λ θ v b hvb p=
    ScalarRootLevel.level (R p) b (by exact_mod_cast hvb) le_rfl g hg ψ hψ hW hbψ := rfl

end SHE.ControlledScalarReference
