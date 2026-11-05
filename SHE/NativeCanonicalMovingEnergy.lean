module

public import SHE.NativeMovingBandEnergy
public import SHE.NativeCanonicalFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.NativeCanonicalFrequency
open Set MeasureTheory Real SmoothApproximation
open scoped ENNReal

variable (D:ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

/-- The actual moving-window current and past energy bounds have one
constant before every smooth companion, band, and physical horizon. -/
theorem moving_band_energy (ell:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
    (ρ χ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)(η:ℝ)(hη:0<η):
    ∃Cc Cp:ℝ,0<Cc ∧ 0<Cp ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→∀H:ℝ,
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
          (∫⁻r in Ioc (0:ℝ) H,F r):=by
  obtain ⟨Cc,Cp,hCc,hCp,hb⟩:=NativeMovingBandEnergy.band_energy Rough ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
  refine ⟨Cc,Cp,hCc,hCp,fun n ν hν H F hF=>?_⟩
  have he:(Rough).exponent=D.beta:=rfl
  have hh:=hb ν hν H F hF
  rw [he] at hh
  simpa only [majorant_smooth D hT hT1 hsmall] using hh

end SHE.NativeCanonicalFrequency
