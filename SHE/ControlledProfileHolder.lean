module

public import SHE.ControlledProfile
public import SHE.ProfileHolderL2

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance PhysicalProfile
  GaussianProfile ProfileStability ProfileL2
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters)

/-- The ACTUAL controlled fixed-point profile has a Holder L2 modulus
with temporal weight zero, uniformly in damping. This is the coarse
profile source required when pairing the terminal finite-N remainder. -/
theorem profile_l2_holder {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2) (θ η : ℝ)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 1) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {r : ℝ} (hr : r ∈ Ioc 0 P.horizon) :
    normTwo haarAddCircle (fun x => profile P Λ u d (θ, (r, x)) - profile P Λ u d (η, (r, x))) ≤
      2*(P.holder*(|θ - η| * ‖d‖)^P.exponent) := by
  have hc : Measurable (fun p => profile P Λ u d (θ, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hd : Measurable (fun p => profile P Λ u d (η, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have haB (z : ℝ) : |P.coefficient z| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have hp : 6≤ProfileVolterra.powerConstant ((P.exponent-1)/4) := by
    unfold ProfileVolterra.powerConstant
    have hd : 0<(P.exponent-1)/4+1:=by linarith [P.exponent_pos]
    have hh : 1≤1/((P.exponent-1)/4+1):=(le_div_iff₀ hd).mpr (by linarith [P.exponent_le_one])
    linarith
  have hsmall : 6*memoryConstant P.lower P.holder P.exponent*
      P.horizon^(P.exponent/4)≤1/2 := by
    have hm:=mul_le_mul_of_nonneg_right hp
      (mul_nonneg (memoryConstant_nonneg (β:=P.exponent) P.lower_pos.le P.holder_nonneg)
        (Real.rpow_nonneg P.horizon_pos.le (P.exponent/4)))
    calc
      _≤memoryConstant P.lower P.holder P.exponent*
          ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4) := by nlinarith only [hm]
      _≤1/2:=hsmallL2
  convert! (ProfileHolderL2.stability
    (φ := fun p => mean Λ u d (θ, p)) (ψ := fun p => mean Λ u d (η, p))
    (c := fun p => profile P Λ u d (θ, p)) (d := fun p => profile P Λ u d (η, p))
    P.measurable hc hd P.lower_pos P.upper_nonneg
    P.holder_nonneg P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one
    (show 0 ≤ |θ - η| * ‖d‖ by positivity) haB P.holder_bound
    (fun p => profile_bounds P Λ u d (θ, p)) (fun p => profile_bounds P Λ u d (η, p))
    (fun r hr => mean_l2_difference hΛ u d θ η hr.1) hsmall
    (fun r hr x => profile_fixed P Λ u d θ hr x)
    (fun r hr x => profile_fixed P Λ u d η hr x) r hr) using 1


end SHE.ControlledProfile
