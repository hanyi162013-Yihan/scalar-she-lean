module

public import SHE.MovingMeanKernelMass

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.MovingMeanCost
open Real

theorem square_rpow {x : ℝ} (hx : 0≤x) (a : ℝ) : (x^a)^2=x^(2*a) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  congr 1
  ring

/-- The actual section RMS square has exactly the damping and energy
powers needed by moving-past convolution, with no moment-cap loss. -/
theorem identity (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν s K ε Λ En χ : ℝ) (hΛ : 0≤Λ) (hEn : 0≤En) :
    (K*(h-s)^(ρ/2)*En^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h s fresh A0 ν)^2=
      (K*(4:ℝ)^ε)^2*Λ^(-2*ε)*MovingMeanKernelMass.kernel P ell Cs k ρ h fresh A0 ν s*En^χ := by
  have he : (En^(χ/2))^2=En^χ := by
    rw [square_rpow hEn]
    congr 1
    ring
  have hl : (Λ^(-ε))^2=Λ^(-2*ε) := by
    rw [square_rpow hΛ]
    congr 1
    ring
  calc
    _=(K*(4:ℝ)^ε)^2*(Λ^(-ε))^2*
      MovingMeanKernelMass.kernel P ell Cs k ρ h fresh A0 ν s*(En^(χ/2))^2 := by
        unfold MovingMeanKernelMass.kernel
        ring
    _=_ := by rw [hl,he]

end SHE.MovingMeanCost
