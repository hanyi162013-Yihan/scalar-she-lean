module
public import SHE.Parameters
public import SHE.SignedNativeBandFrequency
public import SHE.NativeBandFrequencyRates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeHigherRateChoice
open Real

/-- All four ACTUAL higher-noise rates are simultaneously admissible
at the manuscript's rho/chi. Arbitrarily small losses and a finite
ordinary BDG order suffice; the bad RMS tail exceeds R^-8. -/
theorem exists_parameters{β δ:ℝ}(hβ:0<β)(hβsmall:β≤4/25)(hδ:0<δ):
    ∃ζ:ℝ,∃p:ℕ,0<ζ ∧ ζ≤δ ∧ 0<p ∧
      0<SHE.rho β+ζ ∧ SHE.rho β+ζ<1/2 ∧
      1≤(p:ℝ)*(1-SHE.chi β) ∧ (20:ℝ)≤ζ*(2*((p-1:ℕ):ℝ)) ∧
      0<NativeBandFrequencyRates.currentDegree β (SHE.rho β) (SHE.chi β) ζ ∧
      0<NativeBandFrequencyRates.pastDegree β ζ ∧
      0<SignedNativeBandFrequency.goodDegree β ζ ζ ∧
      (16:ℝ)<SignedNativeBandFrequency.badDegree β 20 ζ:=by
  let ζ:=min (β/100) δ
  have hz:0<ζ:=lt_min (by positivity) hδ
  have hzb:ζ≤β/100:=min_le_left _ _
  have hzd:ζ≤δ:=min_le_right _ _
  have hchi:0<1-SHE.chi β:=by dsimp [SHE.chi];linarith
  obtain ⟨p,hp⟩:=exists_nat_gt (max 1 (max (1/(1-SHE.chi β)) (20/(2*ζ)+1)))
  have hpR:1<(p:ℝ):=(le_max_left _ _).trans_lt hp
  have hpN:1≤p:=by exact_mod_cast hpR.le
  have hp0:0<p:=by omega
  have hpOrder:1/(1-SHE.chi β)<(p:ℝ):=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hp
  have hpTail:20/(2*ζ)+1<(p:ℝ):=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hp
  have horder:1≤(p:ℝ)*(1-SHE.chi β):=((div_lt_iff₀ hchi).mp hpOrder).le
  have htail:(20:ℝ)≤ζ*(2*((p-1:ℕ):ℝ)):=by
    rw [Nat.cast_sub hpN,Nat.cast_one]
    have hh:20<(p-1:ℝ)*(2*ζ):=(div_lt_iff₀ (by positivity:0<2*ζ)).mp (by linarith :20/(2*ζ)<(p:ℝ)-1)
    nlinarith
  have hmax:0≤2*SHE.chi β-4*SHE.rho β:=by dsimp [SHE.chi,SHE.rho];linarith
  refine ⟨ζ,p,hz,hzd,hp0,?_,?_,horder,htail,?_,?_,?_,?_⟩
  · dsimp [SHE.rho];linarith
  · dsimp [SHE.rho];linarith
  · rw [NativeBandFrequencyRates.currentDegree,max_eq_right hmax]
    dsimp [SHE.chi,SHE.rho]
    linarith
  · dsimp [NativeBandFrequencyRates.pastDegree];linarith
  · dsimp [SignedNativeBandFrequency.goodDegree];linarith
  · dsimp [SignedNativeBandFrequency.badDegree];linarith
end SHE.NativeHigherRateChoice
