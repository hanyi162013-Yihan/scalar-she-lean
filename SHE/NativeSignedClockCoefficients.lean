module

public import SHE.SignedNativeCanonicalMoving

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeCanonicalFrequency
open Set MeasureTheory Real SmoothApproximation SignedNativeBandFrequency
open scoped ENNReal
variable (D:ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (ell:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
variable (ρ η ε tail ζ:ℝ)(hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
local notation "Bound"=>signed_moving_energy D hT hT1 hsmall ell Cs k hk ρ η ε tail ζ hα hαhalf hζ

/-- Fixed before the stochastic model and smoothing index. -/
def goodCoefficient:ℝ:=Classical.choose Bound
def badCoefficient:ℝ:=Classical.choose (Classical.choose_spec Bound)
local notation "Cg"=>goodCoefficient D hT hT1 hsmall ell Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Cb"=>badCoefficient D hT hT1 hsmall ell Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall

theorem signed_coefficients:
    0<Cg ∧ 0<Cb ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→∀H:ℝ,∀F:ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window D.beta ν
      let Kg:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k (ρ+η) (2*(ρ+η)) ν (h-s)^2)
      let Kb:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k 0 0 ν (h-s)^2)
      ENNReal.ofReal (ν^(-2*D.beta+2*ε))*
        (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,Kg s*F (v+s))≤
          ENNReal.ofReal (Cg*ν^(-goodDegree D.beta ε ζ))*(∫⁻r in Ioc (0:ℝ) H,F r) ∧
      ENNReal.ofReal (ν^(-2*D.beta+2*ε))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k (ρ+η) (2*(ρ+η)) ν (t-q)^2)*F q)≤
          ENNReal.ofReal (Cg*ν^(-goodDegree D.beta ε ζ))*(∫⁻r in Ioc (0:ℝ) H,F r) ∧
      ENNReal.ofReal (ν^(-2*D.beta-tail))*(∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,Kb s)≤
          ENNReal.ofReal (Cb*ν^(-badDegree D.beta tail ζ))*ENNReal.ofReal H ∧
      ENNReal.ofReal (ν^(-2*D.beta-tail))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k 0 0 ν (t-q)^2))≤
          ENNReal.ofReal (Cb*ν^(-badDegree D.beta tail ζ))*ENNReal.ofReal H:=
  Classical.choose_spec (Classical.choose_spec Bound)

end SHE.NativeCanonicalFrequency
