module

public import SHE.NativeInitialBandEnergy
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

/-- The initial triangle bound is uniform before all actual smooth
companions and all dyadic windows, with the physical current retained. -/
theorem initial_band_energy (ell:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
    (ρ χ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)(η:ℝ)(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→∀H:ℝ,∀F:ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window D.beta ν
      ENNReal.ofReal (ν^(-2*D.beta))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ χ ν (t-q)^2)*F q^χ) ≤
        ENNReal.ofReal (C*ν^(-NativeBandFrequencyRates.currentDegree D.beta ρ χ η))*
          ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)) := by
  obtain ⟨C,hC,hb⟩:=NativeInitialBandEnergy.band_energy Rough ell Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
  refine ⟨C,hC,fun n ν hν H F hF=>?_⟩
  have he:(Rough).exponent=D.beta:=rfl
  have hh:=hb ν hν H F hF
  rw [he] at hh
  simpa only [majorant_smooth D hT hT1 hsmall] using hh

end SHE.NativeCanonicalFrequency
