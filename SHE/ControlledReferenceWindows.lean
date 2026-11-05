module

public import SHE.ControlledProfileInputContinuity
public import SHE.CovarianceEndpointPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledReferenceWindows
open Set MeasureTheory StoppedFourier ControlledProfile
open CovarianceEndpoint
local instance controlledReferenceWindows_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceWindows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceWindows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

variable (P : CanonicalCovariance.ProfileParameters) (Λ θ v : ℝ)

/-- Actual controlled canonical TOTAL covariance profile in the physical
window based at v. The input parameter is the pair of original L² states. -/
def coefficient (p : Inputs) (z : Domain) : ℝ :=
  profile P Λ p.1 p.2 (θ,(z.1-v,z.2))

theorem coefficient_measurable : Measurable (fun p : Inputs×Domain => coefficient P Λ θ v p.1 p.2) := by
  have hm := ControlledProfile.profile_joint_measurable P Λ
  have hmap : Measurable (fun p : Inputs×Domain => ((p.1,θ),(p.2.1-v,p.2.2))) :=
    (measurable_fst.prodMk measurable_const).prodMk
      ((measurable_snd.fst.sub_const v).prodMk measurable_snd.snd)
  have hh := hm.comp hmap
  convert hh using 1
  rfl

theorem coefficient_section_measurable (p : Inputs) : Measurable (coefficient P Λ θ v p) := by
  have hm := coefficient_measurable P Λ θ v
  have hmap : Measurable (fun z : Domain => (p,z)) := measurable_const.prodMk measurable_id
  have hh := hm.comp hmap
  convert hh using 1
  rfl

theorem coefficient_bounds (p : Inputs) (z : Domain) :
    P.lower≤coefficient P Λ θ v p z ∧ coefficient P Λ θ v p z≤P.upper :=
  ControlledProfile.profile_bounds P Λ p.1 p.2 _

theorem coefficient_abs_bound (p : Inputs) (z : Domain) : |coefficient P Λ θ v p z|≤P.upper := by
  rw [abs_of_nonneg (P.lower_pos.le.trans (coefficient_bounds P Λ θ v p z).1)]
  exact (coefficient_bounds P Λ θ v p z).2

theorem coefficient_inputs_continuous (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (z : Domain) : Continuous (fun p => coefficient P Λ θ v p z) :=
  ControlledProfileInputContinuity.profile_inputs_continuous P hΛ θ hsmall (z.1-v,z.2)

variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b : ℝ) (hvb : v≤b)
variable (htarget : ∀ i,b≤(Z i).target)

def window (p : Inputs) : EndpointWindow n where
  coefficient := coefficient P Λ θ v p
  measurable := coefficient_section_measurable P Λ θ v p
  observations := Z
  left := v
  right := b
  upper := P.upper
  ordered := hvb
  upper_nonneg := P.upper_nonneg
  target_after := htarget
  bounded := fun t _ x => coefficient_abs_bound P Λ θ v p (t,x)
  nonneg := fun t _ x => P.lower_pos.le.trans (coefficient_bounds P Λ θ v p (t,x)).1

end SHE.ControlledReferenceWindows
