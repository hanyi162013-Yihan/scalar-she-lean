module

public import SHE.JointWordAnalytic
public import SHE.JointDefectAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointWordHessian
open Set MeasureTheory StoppedFourier WordRecursion GaussianItoTest CutoffWordLevel
open JointWordAnalytic CutoffWordAnalytic
abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

def field (p : (P×Ω)×ℝ) : State n→L[ℝ]State n→L[ℝ]ℝ :=
  GaussianTaylor.hessian (backward (L.window p.1.1) (L.test p.1.1) p.2)
    (state L Λ U V XU XV p.1.1 p.1.2 p.2)

set_option backward.isDefEq.respectTransparency true in
theorem measurable (hU : Measurable U) (hV : Measurable V)
    (hXU : Measurable XU) (hXV : Measurable XV) : Measurable (field L Λ U V XU XV) := by
  have hs := state_measurable L Λ hU hV hXU hXV
  have hg : Measurable (fun p : (P×ℝ)×State n =>
      GaussianTaylor.hessian (backward (L.window p.1.1) (L.test p.1.1) p.1.2) p.2) :=
    MeasurableDerivatives.hessian_measurable (backward_measurable L)
      (fun p => ((backward_uniform L).smooth p).of_le (by simp))
  have hp : Measurable (fun p : (P×Ω)×ℝ => ((p.1.1,p.2),state L Λ U V XU XV p.1.1 p.1.2 p.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk hs
  have hh := hg.comp hp
  convert hh using 1
  funext p
  rfl

/-- Uniform in every actual old joint state; the finite smooth word's
derivative constant remains explicit and may depend on its depth. -/
theorem uniform_bound : ∃ B : ℝ,0≤B ∧ ∀ p,‖field L Λ U V XU XV p‖≤B := by
  obtain ⟨B,hBn,hB⟩ := (backward_uniform L).fderiv.fderiv.norm_bound
  exact ⟨B,hBn,fun p => hB (p.1.1,p.2) (state L Λ U V XU XV p.1.1 p.1.2 p.2)⟩

end SHE.JointWordHessian
