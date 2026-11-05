module

public import SHE.ControlledReferenceWindows
public import SHE.CanonicalCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledProfileZero
open StoppedFourier PhysicalProfile
local instance controlledProfileZero_period : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The zero-theta controlled profile is exactly the ordinary canonical
profile. This is equality of the actual Picard realizations and holds
also outside the profile horizon. -/
theorem profile_zero (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (p : ControlledProfile.Domain) :
    ControlledProfile.profile P Λ u d (0,p) =
      CanonicalProfile.profile P.coefficient P.lower P.horizon (u,p) := by
  unfold ControlledProfile.profile CanonicalProfile.profile
  calc
    _ = ParametricProfile.canonicalProfile P.coefficient
        (fun q : Unit × ControlledProfile.Domain => physicalHeatMean u q.2)
        P.lower P.horizon ((),p) := by
      have h := ParametricProfile.canonicalProfile_comap P.coefficient
        (ControlledProfile.mean Λ u d) P.lower P.horizon (fun _ : Unit => (0:ℝ)) ((),p)
      simpa only [ControlledProfile.mean,zero_mul,add_zero] using h.symm
    _ = _ := ParametricProfile.canonicalProfile_comap P.coefficient
      (fun q : CircleL2 × ControlledProfile.Domain => physicalHeatMean q.1 q.2)
      P.lower P.horizon (fun _ : Unit => u) ((),p)

/-- The absolute-clock zero-theta reference coefficient is the ordinary
canonical field based at the same original past time. Neither damping
nor the second initial state enters this field. -/
theorem coefficient_zero (P : CanonicalCovariance.ProfileParameters) (Λ v : ℝ)
    (p : ControlledProfile.Inputs) (z : ControlledProfile.Domain) :
    ControlledReferenceWindows.coefficient P Λ 0 v p z=P.field v (p.1,z) :=
  profile_zero P Λ p.1 p.2 (z.1-v,z.2)

end SHE.ControlledProfileZero
