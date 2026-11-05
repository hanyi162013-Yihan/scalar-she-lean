module

public import SHE.ControlledProfileZero

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.ZeroDirectionProfile
open StoppedFourier PhysicalProfile
local instance zeroDirectionProfile_period:Fact (0<2*Real.pi):=⟨by positivity⟩

theorem heat_mean_zero (p:ControlledProfile.Domain):physicalHeatMean (0:CircleL2) p=0:=by
  simp [physicalHeatMean,heatMeanSeries,fourierCoeff]

/-- With zero initial difference the ACTUAL fixed-point profile is
independent of its interpolation parameter, also outside the horizon. -/
theorem profile (P:CanonicalCovariance.ProfileParameters) (Λ θ:ℝ) (u:CircleL2)
    (p:ControlledProfile.Domain):
    ControlledProfile.profile P Λ u 0 (θ,p)=
      CanonicalProfile.profile P.coefficient P.lower P.horizon (u,p):=by
  unfold ControlledProfile.profile CanonicalProfile.profile
  calc
    _=ParametricProfile.canonicalProfile P.coefficient
      (fun q:Unit×ControlledProfile.Domain=>physicalHeatMean u q.2) P.lower P.horizon ((),p):=by
      have he:=ParametricProfile.canonicalProfile_comap P.coefficient
        (ControlledProfile.mean Λ u 0) P.lower P.horizon (fun _:Unit=>θ) ((),p)
      simpa only [ControlledProfile.mean,heat_mean_zero,mul_zero,add_zero] using he.symm
    _=_:=ParametricProfile.canonicalProfile_comap P.coefficient
      (fun q:CircleL2×ControlledProfile.Domain=>physicalHeatMean q.1 q.2)
      P.lower P.horizon (fun _:Unit=>u) ((),p)

theorem coefficient (P:CanonicalCovariance.ProfileParameters) (Λ θ v:ℝ) (u:CircleL2):
    ControlledReferenceWindows.coefficient P Λ θ v (u,0)=P.field v ∘ (fun z=>(u,z)):=by
  funext z
  exact profile P Λ θ u (z.1-v,z.2)

end SHE.ZeroDirectionProfile
