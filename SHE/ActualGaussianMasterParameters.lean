module
public import SHE.NativeHigherRateChoice
public import SHE.ActualReferenceMasterClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.ActualGaussianMasterParameters
open Real
/-- One finite BDG order works for both actual higher-current and
reference interpolation estimates, before damping and approximation. -/
theorem exists_parameters{β:ℝ}(hβ:0<β)(hβsmall:β≤4/25):
    ∃ζ:ℝ,∃p:ℕ,0<ζ ∧ ζ≤β/100 ∧ 0<p ∧
      0<SHE.rho β+ζ ∧ SHE.rho β+ζ<1/2 ∧
      1≤(p:ℝ)*(1-SHE.chi β) ∧
      1≤(p:ℝ)*(1-ActualReferenceMasterClosure.referenceExponent β) ∧
      (20:ℝ)≤ζ*(2*((p-1:ℕ):ℝ)) ∧
      0<NativeBandFrequencyRates.currentDegree β (SHE.rho β) (SHE.chi β) ζ ∧
      0<NativeBandFrequencyRates.pastDegree β ζ ∧
      0<SignedNativeBandFrequency.goodDegree β ζ ζ ∧
      (16:ℝ)<SignedNativeBandFrequency.badDegree β 20 ζ:=by
  obtain ⟨ζ,p0,hζ,hζβ,hp0,hα,hαhalf,ho,ht,hcur,hpast,hgood,hbad⟩:=
    NativeHigherRateChoice.exists_parameters hβ hβsmall (show 0<β/100 by positivity)
  have hr:0<1-ActualReferenceMasterClosure.referenceExponent β:=by
    dsimp [ActualReferenceMasterClosure.referenceExponent]
    linarith
  obtain ⟨p1,hp1⟩:=exists_nat_gt (1/(1-ActualReferenceMasterClosure.referenceExponent β))
  let p:=max p0 p1
  have hp:0<p:=lt_of_lt_of_le hp0 (le_max_left _ _)
  have h0:(p0:ℝ)≤p:=by exact_mod_cast (le_max_left p0 p1)
  have h1:(p1:ℝ)≤p:=by exact_mod_cast (le_max_right p0 p1)
  have hn:((p0-1:ℕ):ℝ)≤((p-1:ℕ):ℝ):=by
    exact_mod_cast Nat.sub_le_sub_right (show p0≤p from le_max_left _ _) 1
  have hcomp:0≤1-SHE.chi β:=by dsimp [SHE.chi];linarith
  refine ⟨ζ,p,hζ,hζβ,hp,hα,hαhalf,?_,?_,?_,hcur,hpast,hgood,hbad⟩
  · exact ho.trans (mul_le_mul_of_nonneg_right h0 hcomp)
  · have hh:1<(p1:ℝ)*(1-ActualReferenceMasterClosure.referenceExponent β):=(div_lt_iff₀ hr).mp hp1
    exact hh.le.trans (mul_le_mul_of_nonneg_right h1 hr.le)
  · exact ht.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by norm_num:(0:ℝ)≤2)) hζ.le)
end SHE.ActualGaussianMasterParameters
