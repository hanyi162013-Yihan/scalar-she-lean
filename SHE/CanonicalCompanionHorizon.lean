module

public import SHE.SmoothComparisonHorizon

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SHE.CanonicalCompanionHorizon
open SmoothApproximation ScalarData GaussianProfile

/-- One actual horizon simultaneously supplies the pointwise contraction
used by the exact scalar expansion and the distinct L2 contraction used
by the comparison estimates, for every canonical companion index. -/
theorem common (D : ScalarData) :
    ∃ (T : ℝ) (hT : 0<T) (hT1 : T≤1)
      (hprofile : contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2),
      ∀ j : ℕ,
        let P:=ControlledSmoothLimit.smoothTotalParameters D hT hT1 hprofile j
        (ProfileStability.memoryConstant P.lower P.holder P.exponent*
          ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) ∧
        (ProfileStability.memoryConstant P.lower P.holder P.exponent*
          ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2) := by
  obtain ⟨T,hT,hT1,hprofile,hpoint,hL2⟩:=SmoothComparisonHorizon.common_horizon D
  refine ⟨T,hT,hT1,hprofile,?_⟩
  intro j
  exact ⟨hpoint,hL2⟩

end SHE.CanonicalCompanionHorizon
