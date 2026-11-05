module
public import SHE.PastReferenceBudgetFrequency
public import SHE.NativeBandFrequencyRates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.PastReferenceBandFrequency
open Real

def degree(β:ℝ)(k:ℕ)(f w η:ℝ):ℝ:=2*β+3*β*(w+2*f-2+(k:ℝ)*β/2)-2*η

def covarianceDegree(β:ℝ)(k:ℕ)(η:ℝ):ℝ:=β/2+(3/2:ℝ)*β^2*((k:ℝ)+1)-2*η
def baselineDegree(β:ℝ)(k:ℕ)(η:ℝ):ℝ:=β/2+(3/2:ℝ)*β^2*(k:ℝ)-2*η
def meanDegree(β ρ ε:ℝ)(k:ℕ)(η:ℝ):ℝ:=β*(3*ρ-1-6*ε)+(3/2:ℝ)*β^2*(k:ℝ)-2*η

theorem covariance_degree(β:ℝ)(k:ℕ)(η:ℝ):
    degree β k ((β+3)/4) 0 η=covarianceDegree β k η:=by unfold degree covarianceDegree;ring

theorem baseline_degree(β:ℝ)(k:ℕ)(η:ℝ):
    degree β k (3/4:ℝ) 0 η=baselineDegree β k η:=by unfold degree baselineDegree;ring

theorem mean_degree(β ρ ε:ℝ)(k:ℕ)(η:ℝ):
    degree β k (1/2-ε) ρ η=meanDegree β ρ ε k η:=by unfold degree meanDegree;ring

theorem weight{β a η ν:ℝ}(hη:0≤η)(hν:1≤ν):
    ν^(-2*β)*(1+ν)^(2*η)*NativeBandFrequencyRates.window β ν^a≤
      (2:ℝ)^(2*η)*ν^(-(2*β+3*β*a-2*η)):=by
  have hp:0<ν:=zero_lt_one.trans_le hν
  have hb:(1+ν)^(2*η)≤(2:ℝ)^(2*η)*ν^(2*η):=by
    have hh:=rpow_le_rpow (by positivity:0≤1+ν) (show 1+ν≤2*ν by linarith) (by positivity:0≤2*η)
    rwa [mul_rpow (by norm_num:(0:ℝ)≤2) hp.le] at hh
  calc
    _≤ν^(-2*β)*((2:ℝ)^(2*η)*ν^(2*η))*NativeBandFrequencyRates.window β ν^a:=by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (rpow_nonneg hp.le _))
        (rpow_nonneg (NativeBandFrequencyRates.window_pos hp).le _)
    _=(2:ℝ)^(2*η)*(ν^(-2*β)*ν^(2*η)*(ν^(-3*β))^a):=by
      unfold NativeBandFrequencyRates.window
      ring
    _=_:=by
      rw [←rpow_mul hp.le,←rpow_add hp,←rpow_add hp]
      congr 2
      ring

/-- At the actual h_nu window, every positive fresh degree has an
explicit endpoint band rate, retaining all finite old-age gains. -/
theorem weighted_square_bound(P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ){f η A ν:ℝ}
    (hf:0<f)(hη:0<η)(hA:0≤A)(hν:1≤ν)(w:ℝ):
    NativeBandFrequencyRates.window P.exponent ν^w*
      (QuarterRMSTimeFactors.oldTimeBudget P ell C k
        (NativeBandFrequencyRates.window P.exponent ν) 0 f (A*ν^(-P.exponent)) ν)^2≤
      A^2*(TerminalCovarianceBudget.constant P ell C k η/f)^2*(2:ℝ)^(2*η)*
        ν^(-degree P.exponent k f w η):=by
  have hp:0<ν:=zero_lt_one.trans_le hν
  have hw:=NativeBandFrequencyRates.window_pos (β:=P.exponent) hp
  have hs:=PastReferenceBudgetFrequency.square_bound P hell C hC k hw
    (NativeBandFrequencyRates.window_le_one P.exponent_pos.le hν) hf hη
    (mul_nonneg hA (rpow_nonneg hp.le (-P.exponent))) (zero_le_one.trans hν)
  have hB:=mul_le_mul_of_nonneg_left hs (rpow_nonneg hw.le w)
  have hpow:(ν^(-P.exponent))^2=ν^(-2*P.exponent):=by
    rw [←rpow_mul_natCast hp.le]
    congr 1
    ring
  have hnorm:NativeBandFrequencyRates.window P.exponent ν^w*
      ((A*ν^(-P.exponent))^2*(TerminalCovarianceBudget.constant P ell C k η/f)^2*(1+ν)^(2*η)*
        NativeBandFrequencyRates.window P.exponent ν^(2*f-2+(k:ℝ)*P.exponent/2))=
      (A^2*(TerminalCovarianceBudget.constant P ell C k η/f)^2)*
        (ν^(-2*P.exponent)*(1+ν)^(2*η)*
          NativeBandFrequencyRates.window P.exponent ν^(w+2*f-2+(k:ℝ)*P.exponent/2)):=by
    rw [mul_pow,hpow]
    have hr:=rpow_add hw w (2*f-2+(k:ℝ)*P.exponent/2)
    rw [show w+2*f-2+(k:ℝ)*P.exponent/2=w+(2*f-2+(k:ℝ)*P.exponent/2) by ring,hr]
    ring
  apply hB.trans
  rw [hnorm]
  have hweight:=mul_le_mul_of_nonneg_left
    (weight (β:=P.exponent) (a:=w+2*f-2+(k:ℝ)*P.exponent/2) hη.le hν)
    (mul_nonneg (sq_nonneg A) (sq_nonneg (TerminalCovarianceBudget.constant P ell C k η/f)))
  convert! hweight using 1 <;> dsimp only [degree] <;> ring

/-- The printed rho and one small common epsilon/log loss give a
strictly positive endpoint rate at EVERY fixed finite depth, including
k=0. The mean needs no false zero-current substitution. -/
theorem printed_positive{β:ℝ}(hβ:0<β)(hβmax:β≤4/25)(k:ℕ):
    0<covarianceDegree β k (β/100) ∧ 0<baselineDegree β k (β/100) ∧
    0<meanDegree β (1/2-3*β/5) (β/100) k (β/100):=by
  have hb2:β^2≤(4/25)*β:=by nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hβmax)]
  have hk:0≤β^2*(k:ℝ):=mul_nonneg (sq_nonneg β) (Nat.cast_nonneg k)
  dsimp only [covarianceDegree,baselineDegree,meanDegree]
  constructor
  · nlinarith [sq_nonneg β]
  constructor
  · nlinarith
  · nlinarith
end SHE.PastReferenceBandFrequency
