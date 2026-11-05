module

public import SHE.NativeCanonicalMovingEnergy
public import SHE.NativeCanonicalInitialEnergy
public import SHE.SignedNativeCanonicalMoving

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeCanonicalFrequency
open Set MeasureTheory Real SmoothApproximation
open scoped ENNReal

variable (D:ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (ell:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
variable (ρ χ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)(η:ℝ)(hη:0<η)

/-- These fixed coefficients are chosen from the structural time ledgers,
before the stochastic model, smoothing index, band and horizon. -/
def currentCoefficient:ℝ:=Classical.choose
  (moving_band_energy D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη)
def pastCoefficient:ℝ:=Classical.choose (Classical.choose_spec
  (moving_band_energy D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη))
def initialCoefficient:ℝ:=Classical.choose
  (initial_band_energy D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη)

local notation "Cc"=>currentCoefficient D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
local notation "Cp"=>pastCoefficient D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
local notation "Ci"=>initialCoefficient D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall

theorem moving_coefficients:
    0<Cc ∧ 0<Cp ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→∀H:ℝ,
      ∀F:ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window D.beta ν
      ENNReal.ofReal (ν^(-2*D.beta))*
        (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ χ ν (h-s)^2)*F (v+s)^χ) ≤
        ENNReal.ofReal (Cc*ν^(-NativeBandFrequencyRates.currentDegree D.beta ρ χ η))*
          ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)) ∧
      ENNReal.ofReal (ν^(-2*D.beta))*
        (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,
          ENNReal.ofReal (s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ 0 ν (h-s)^2)*F v) ≤
        ENNReal.ofReal (Cp*ν^(-NativeBandFrequencyRates.pastDegree D.beta η))*
          (∫⁻r in Ioc (0:ℝ) H,F r):=
  Classical.choose_spec (Classical.choose_spec
    (moving_band_energy D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη))

theorem initial_coefficient:
    0<Ci ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→∀H:ℝ,∀F:ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window D.beta ν
      ENNReal.ofReal (ν^(-2*D.beta))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ χ ν (t-q)^2)*F q^χ) ≤
        ENNReal.ofReal (Ci*ν^(-NativeBandFrequencyRates.currentDegree D.beta ρ χ η))*
          ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)):=
  Classical.choose_spec
    (initial_band_energy D hT hT1 hsmall ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη)

end SHE.NativeCanonicalFrequency
