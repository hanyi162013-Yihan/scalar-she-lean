module

public import SHE.NativeZeroBudgetFrequency
public import SHE.NativeBandFrequencyRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.SignedNativeBandFrequency
open Set MeasureTheory Real

def goodDegree (β ε ζ:ℝ):ℝ:=2*β-2*ε-ζ
def badDegree (β tail ζ:ℝ):ℝ:=2*β+tail-ζ

private theorem weight {a ζ ν:ℝ}(hζ:0≤ζ)(hν:1≤ν):
    ν^(-a)*(1+ν)^ζ≤(2:ℝ)^ζ*ν^(-(a-ζ)):=by
  have hv:0<ν:=zero_lt_one.trans_le hν
  have hp:(1+ν)^ζ≤(2:ℝ)^ζ*ν^ζ:=by
    have hh:=Real.rpow_le_rpow (by positivity:0≤1+ν) (show 1+ν≤2*ν by linarith) hζ
    rwa [Real.mul_rpow (by norm_num:0≤(2:ℝ)) hv.le] at hh
  calc
    _≤ν^(-a)*((2:ℝ)^ζ*ν^ζ):=mul_le_mul_of_nonneg_left hp (rpow_nonneg hv.le _)
    _=(2:ℝ)^ζ*(ν^(-a)*ν^ζ):=by ring
    _=_:=by rw [←Real.rpow_add hv];congr 2;ring

/-- Both literal signed-endpoint kernels have actual uniform band
masses. The zero-degree bad corner uses its clipped roots, while the
good log loss leaves no additional frequency power beyond truncation. -/
theorem band_integrals (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(ρ η ε tail ζ:ℝ)(hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ):
    ∃Cg Cb:ℝ,0<Cg ∧ 0<Cb ∧ ∀ν:ℝ,1≤ν→
      let h:=NativeBandFrequencyRates.window P.exponent ν
      Integrable (fun w=>NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν w^2)
        (volume.restrict (Ioc 0 h)) ∧
      Integrable (fun w=>NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν w^2)
        (volume.restrict (Ioc 0 h)) ∧
      ν^(-2*P.exponent+2*ε)*(∫w,NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν w^2
        ∂volume.restrict (Ioc 0 h))≤Cg*ν^(-goodDegree P.exponent ε ζ) ∧
      ν^(-2*P.exponent-tail)*(∫w,NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν w^2
        ∂volume.restrict (Ioc 0 h))≤Cb*ν^(-badDegree P.exponent tail ζ):=by
  obtain ⟨Cg,hCg,hgb⟩:=NativeCurrentBudgetFrequency.majorant_energy P ell Cs k hk (ρ+η) (2*(ρ+η))
    hα (by linarith) (by linarith [P.exponent_pos]) ζ hζ
  obtain ⟨Cb,hCb,hbb⟩:=NativeCurrentBudgetFrequency.zero_majorant_energy P ell Cs k hk ζ hζ
  refine ⟨Cg*(2:ℝ)^ζ,Cb*(2:ℝ)^ζ,by positivity,by positivity,?_⟩
  intro ν hν h
  have hv:0<ν:=zero_lt_one.trans_le hν
  have hh:0<h:=NativeBandFrequencyRates.window_pos hv
  have hh1:h≤1:=NativeBandFrequencyRates.window_le_one P.exponent_pos.le hν
  have hg:=hgb ν h hv hh hh1
  have hb:=hbb ν h hv hh hh1
  have he:max 0 (2*(2*(ρ+η))-4*(ρ+η))+ζ=ζ:=by ring_nf;norm_num
  rw [he] at hg
  refine ⟨hg.1,hb.1,?_,?_⟩
  · calc
      _≤ν^(-2*P.exponent+2*ε)*(Cg*(1+ν)^ζ):=
        mul_le_mul_of_nonneg_left hg.2 (rpow_nonneg hv.le _)
      _=Cg*(ν^(-(2*P.exponent-2*ε))*(1+ν)^ζ):=by rw [show -2*P.exponent+2*ε= -(2*P.exponent-2*ε) by ring];ring
      _≤Cg*((2:ℝ)^ζ*ν^(-((2*P.exponent-2*ε)-ζ))):=
        mul_le_mul_of_nonneg_left (weight hζ.le hν) hCg.le
      _=_:=by unfold goodDegree;ring
  · calc
      _≤ν^(-2*P.exponent-tail)*(Cb*(1+ν)^ζ):=
        mul_le_mul_of_nonneg_left hb.2 (rpow_nonneg hv.le _)
      _=Cb*(ν^(-(2*P.exponent+tail))*(1+ν)^ζ):=by rw [show -2*P.exponent-tail= -(2*P.exponent+tail) by ring];ring
      _≤Cb*((2:ℝ)^ζ*ν^(-((2*P.exponent+tail)-ζ))):=
        mul_le_mul_of_nonneg_left (weight hζ.le hν) hCb.le
      _=_:=by unfold badDegree;ring

end SHE.SignedNativeBandFrequency
