module

public import SHE.NativePastBudgetConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.NativeBandFrequencyRates
open Set MeasureTheory Real
open scoped BigOperators

def currentDegree (β ρ χ η:ℝ):ℝ:=2*β-max 0 (2*χ-4*ρ)-η
def pastDegree (β η:ℝ):ℝ:=β/2-η
def window (β ν:ℝ):ℝ:=ν^(-3*β)

/-- The complete current range chi<beta+2rho leaves a positive band
summation margin, simultaneously with the actual past-age loss. -/
theorem positive_degrees {β ρ χ:ℝ}(hβ:0<β)(hm:χ<β+2*ρ):
    ∃η:ℝ,0<η ∧ 0<currentDegree β ρ χ η ∧ 0<pastDegree β η:=by
  have hd:0<2*β-max 0 (2*χ-4*ρ):=by
    by_cases h:0≤2*χ-4*ρ
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left (le_of_not_ge h)]
      linarith
  let η:=min (β/4) ((2*β-max 0 (2*χ-4*ρ))/2)
  have hη:0<η:=lt_min (by positivity) (by positivity)
  refine ⟨η,hη,?_,?_⟩
  · dsimp only [currentDegree]
    have hh:=min_le_right (β/4) ((2*β-max 0 (2*χ-4*ρ))/2)
    change η≤_ at hh
    linarith
  · dsimp only [pastDegree]
    have hh:=min_le_left (β/4) ((2*β-max 0 (2*χ-4*ρ))/2)
    change η≤_ at hh
    linarith

theorem window_pos {β ν:ℝ}(hν:0<ν):0<window β ν:=Real.rpow_pos_of_pos hν _
theorem window_le_one {β ν:ℝ}(hβ:0≤β)(hν:1≤ν):window β ν≤1:=
  Real.rpow_le_one_of_one_le_of_nonpos hν (by linarith)

/-- Root amplitude absorbs the actual current reflected-envelope
frequency loss. No artificial damping gain is inserted. -/
theorem current_weight {β ρ χ η ν:ℝ}(hη:0≤η)(hν:1≤ν):
    ν^(-2*β)*(1+ν)^(max 0 (2*χ-4*ρ)+η)≤
      (2:ℝ)^(max 0 (2*χ-4*ρ)+η)*ν^(-currentDegree β ρ χ η):=by
  have hνp:0<ν:=lt_of_lt_of_le zero_lt_one hν
  let D:=max 0 (2*χ-4*ρ)+η
  have hD:0≤D:=add_nonneg (le_max_left _ _) hη
  have hp:(1+ν)^D≤(2:ℝ)^D*ν^D:=by
    have hh:=Real.rpow_le_rpow (by positivity : 0≤1+ν)
      (show 1+ν≤2*ν by linarith) hD
    rwa [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hνp.le] at hh
  calc
    _≤ν^(-2*β)*((2:ℝ)^D*ν^D):=mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hνp.le _)
    _=(2:ℝ)^D*(ν^(-2*β)*ν^D):=by ring
    _=_:=by rw [←Real.rpow_add hνp];congr 2;dsimp only [D,currentDegree];ring

/-- The manuscript's actual h_nu=nu^(-3 beta) converts the retained
half-power past-age convolution into the summable beta/2 band rate. -/
theorem past_weight {β η ν:ℝ}(hη:0≤η)(hν:1≤ν):
    ν^(-2*β)*window β ν^(-(1/2:ℝ))*(1+ν)^η≤
      (2:ℝ)^η*ν^(-pastDegree β η):=by
  have hνp:0<ν:=lt_of_lt_of_le zero_lt_one hν
  have hp:(1+ν)^η≤(2:ℝ)^η*ν^η:=by
    have hh:=Real.rpow_le_rpow (by positivity : 0≤1+ν)
      (show 1+ν≤2*ν by linarith) hη
    rwa [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hνp.le] at hh
  calc
    _≤ν^(-2*β)*window β ν^(-(1/2:ℝ))*((2:ℝ)^η*ν^η):=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.rpow_nonneg hνp.le _)
        (Real.rpow_nonneg (window_pos hνp).le _))
    _=(2:ℝ)^η*(ν^(-2*β)*(ν^(-3*β))^(-(1/2:ℝ))*ν^η):=by dsimp only [window];ring
    _=_:=by
      rw [←Real.rpow_mul hνp.le,←Real.rpow_add hνp,←Real.rpow_add hνp]
      congr 2
      dsimp only [pastDegree]
      ring

/-- Both actual reflected envelopes are integrated before choosing
the dyadic band. Constants are uniform in every actual band window. -/
theorem band_integrals (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(ρ χ:ℝ)(hρ:0<ρ)(hχ:χ<1)(hm:χ<P.exponent+2*ρ)
    (η:ℝ)(hη:0<η):
    ∃Cc Cp:ℝ,0<Cc ∧ 0<Cp ∧ ∀ν:ℝ,1≤ν→
      Integrable (fun w=>NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν w^2)
        (volume.restrict (Ioc 0 (window P.exponent ν))) ∧
      Integrable (fun s=>s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν
        (window P.exponent ν-s)^2) (volume.restrict (Ioc 0 (window P.exponent ν))) ∧
      ν^(-2*P.exponent)*(∫w,NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν w^2
        ∂volume.restrict (Ioc 0 (window P.exponent ν)))≤
        Cc*ν^(-currentDegree P.exponent ρ χ η) ∧
      ν^(-2*P.exponent)*(∫s,s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν
        (window P.exponent ν-s)^2 ∂volume.restrict (Ioc 0 (window P.exponent ν)))≤
        Cp*ν^(-pastDegree P.exponent η):=by
  obtain ⟨Cc,hCc,hcb⟩:=NativeCurrentBudgetFrequency.majorant_energy P ell Cs k hk ρ χ hρ hχ hm η hη
  obtain ⟨Cp,hCp,hpb⟩:=NativePastBudgetConvolution.majorant_energy P ell Cs k ρ hρ η hη
  let D:=max 0 (2*χ-4*ρ)+η
  refine ⟨Cc*(2:ℝ)^D,Cp*(2:ℝ)^η,mul_pos hCc (Real.rpow_pos_of_pos (by norm_num) _),
    mul_pos hCp (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro ν hν
  have hνp:0<ν:=lt_of_lt_of_le zero_lt_one hν
  have hw:=window_pos (β:=P.exponent) hνp
  have hw1:=window_le_one P.exponent_pos.le hν
  have hc:=hcb ν (window P.exponent ν) hνp hw hw1
  have hp:=hpb ν (window P.exponent ν) hνp hw hw1
  refine ⟨hc.1,hp.1,?_,?_⟩
  · calc
      _≤ν^(-2*P.exponent)*(Cc*(1+ν)^D):=mul_le_mul_of_nonneg_left hc.2 (Real.rpow_nonneg hνp.le _)
      _=Cc*(ν^(-2*P.exponent)*(1+ν)^D):=by ring
      _≤Cc*((2:ℝ)^D*ν^(-currentDegree P.exponent ρ χ η)):=
        mul_le_mul_of_nonneg_left (current_weight hη.le hν) hCc.le
      _=_:=by ring
  · calc
      _≤ν^(-2*P.exponent)*(Cp*window P.exponent ν^(-(1/2:ℝ))*(1+ν)^η):=
        mul_le_mul_of_nonneg_left hp.2 (Real.rpow_nonneg hνp.le _)
      _=Cp*(ν^(-2*P.exponent)*window P.exponent ν^(-(1/2:ℝ))*(1+ν)^η):=by ring
      _≤Cp*((2:ℝ)^η*ν^(-pastDegree P.exponent η)):=
        mul_le_mul_of_nonneg_left (past_weight hη.le hν) hCp.le
      _=_:=by ring

end SHE.NativeBandFrequencyRates
