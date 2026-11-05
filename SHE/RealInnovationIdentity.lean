module

public import SHE.HaarRealSpace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory CircleHeat DyadicApproximation
open scoped ENNReal
local instance realInnovationIdentity_local1 : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

/-- Literal real innovations embed as the previously constructed full
complex innovation, with no change of coordinates or normalization. -/
theorem realInnovation_embed {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M) (v : RealL2) :
    realInputEmbed (fieldRealInnovation ell M hell f v)=
      innovationRotation f.1 ell M hell f.2.1 f.2.2 (realEmbed v) := by
  have he := congrArg (fun x : realInputSpace => (x:HaarInput))
    (realInputIdentification.apply_symm_apply
      (realInnovationRotation f.1 ell M hell f.2.1 f.2.2 (realCircleIdentification v)))
  exact he

/-- The actual common-Haar factor times the literal real innovation
is the physical square-root coefficient multiplier. -/
theorem factor_realInnovation {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M) (v : RealL2) :
    fieldFactor ell M hell f (realInputEmbed (fieldRealInnovation ell M hell f v))=
      CircleMultiplier.rootEquivalence f.1 ell M hell
        (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) (realEmbed v) := by
  rw [realInnovation_embed hell f v]
  exact factor_innovationRotation f.1 ell M hell f.2.1 f.2.2 (realEmbed v)

theorem real_factor_realInnovation {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M) (v : RealL2) :
    realPart (fieldFactor ell M hell f (realInputEmbed (fieldRealInnovation ell M hell f v)))=
      realPart (CircleMultiplier.rootEquivalence f.1 ell M hell
        (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) (realEmbed v)) :=
  congrArg realPart (factor_realInnovation hell f v)

end SHE.FiniteHaar
