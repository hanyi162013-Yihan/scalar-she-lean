module

public import SHE.FirstGammaAffine

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SHE.JointGammaAffine
open GaussianIncrement
variable (n : ℕ)

/-- The true joint observation is a CONSTANT linear map of the actual
extended martingale: the difference coordinate already carries exp(Λq).
This map has no old compensator and no time derivative. -/
def current (Λ θ : ℝ) (target : Fin n→ℝ) : FirstGammaAffine.Space n→L[ℝ]State n :=
  FirstGammaAffine.currentU n+θ •
    (FirstGammaAffine.terminalDamping n Λ target).comp (FirstGammaAffine.currentD n)

theorem current_apply (Λ θ : ℝ) (target : Fin n→ℝ) (z : FirstGammaAffine.Space n) (i : Fin n) :
    current n Λ θ target z i=FirstGammaAffine.currentU n z i+
      θ*Real.exp (-Λ*target i)*FirstGammaAffine.currentD n z i := by
  simp only [current,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    FirstGammaAffine.terminalDamping_apply]
  ring

end SHE.JointGammaAffine
