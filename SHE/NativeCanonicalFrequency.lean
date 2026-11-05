module

public import SHE.NativeBandFrequencyRates
public import SHE.NativeFrequencyProfileCongruence
public import SHE.ControlledSmoothLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeCanonicalFrequency
open Set MeasureTheory Real SmoothApproximation

variable (D:ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

theorem majorant_smooth (ell:ℝ)(Cs:ℕ→ℝ)(k n:ℕ)(ρ χ ν w:ℝ):
    NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ χ ν w=
      NativeCurrentBudgetFrequency.majorant Rough ell Cs k ρ χ ν w:=by
  apply NativeCurrentBudgetFrequency.majorant_congr <;> rfl

/-- The actual two native frequency bounds have ONE constant before
all smoothing indices and all dyadic windows. No high coefficient
derivative, companion index or band window enters the constant. -/
theorem band_integrals (ell:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
    (ρ χ:ℝ)(hρ:0<ρ)(hχ:χ<1)(hm:χ<D.beta+2*ρ)(η:ℝ)(hη:0<η):
    ∃Cc Cp:ℝ,0<Cc ∧ 0<Cp ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→
      Integrable (fun w=>NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ χ ν w^2)
        (volume.restrict (Ioc 0 (NativeBandFrequencyRates.window D.beta ν))) ∧
      Integrable (fun s=>s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ 0 ν
        (NativeBandFrequencyRates.window D.beta ν-s)^2)
        (volume.restrict (Ioc 0 (NativeBandFrequencyRates.window D.beta ν))) ∧
      ν^(-2*D.beta)*(∫w,NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ χ ν w^2
        ∂volume.restrict (Ioc 0 (NativeBandFrequencyRates.window D.beta ν)))≤
        Cc*ν^(-NativeBandFrequencyRates.currentDegree D.beta ρ χ η) ∧
      ν^(-2*D.beta)*(∫s,s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant (Smooth n) ell Cs k ρ 0 ν
        (NativeBandFrequencyRates.window D.beta ν-s)^2
        ∂volume.restrict (Ioc 0 (NativeBandFrequencyRates.window D.beta ν)))≤
        Cp*ν^(-NativeBandFrequencyRates.pastDegree D.beta η):=by
  obtain ⟨Cc,Cp,hCc,hCp,hb⟩:=NativeBandFrequencyRates.band_integrals Rough ell Cs k hk ρ χ hρ hχ hm η hη
  refine ⟨Cc,Cp,hCc,hCp,fun n ν hν=>?_⟩
  have he:(Rough).exponent=D.beta:=rfl
  have hh:=hb ν hν
  rw [he] at hh
  simpa only [majorant_smooth D hT hT1 hsmall] using hh

end SHE.NativeCanonicalFrequency
