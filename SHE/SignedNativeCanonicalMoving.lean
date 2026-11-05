module

public import SHE.SignedNativeMovingEnergy
public import SHE.NativeCanonicalFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.NativeCanonicalFrequency
open Set MeasureTheory Real SmoothApproximation SignedNativeBandFrequency
open scoped ENNReal
variable (D:ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

/-- The actual signed-kernel time ledger has fixed constants before
all smooth companions, all bands, and all actual energy functions. -/
theorem signed_moving_energy (ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(ρ η ε tail ζ:ℝ)(hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ):
    ∃Cg Cb:ℝ,0<Cg ∧ 0<Cb ∧ ∀n:ℕ,∀ν:ℝ,1≤ν→∀H:ℝ,∀F:ℝ→ℝ≥0∞,Measurable F→
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
          ENNReal.ofReal (Cb*ν^(-badDegree D.beta tail ζ))*ENNReal.ofReal H :=by
  obtain ⟨Cg,Cb,hCg,hCb,hb⟩:=SignedNativeBandFrequency.moving_energy Rough ell Cs k hk ρ η ε tail ζ hα hαhalf hζ
  refine ⟨Cg,Cb,hCg,hCb,fun n ν hν H F hF=>?_⟩
  have he:(Rough).exponent=D.beta:=rfl
  have hh:=hb ν hν H F hF
  rw [he] at hh
  simpa only [majorant_smooth D hT hT1 hsmall] using hh

end SHE.NativeCanonicalFrequency
