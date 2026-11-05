module

public import SHE.ControlledProfileHolder
public import SHE.ShiftedControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ProfileHolderScoreRates
open Set MeasureTheory Real AddCircle StoppedFourier ControlledProfile ProfileL2 ProfileStability
local instance : Fact (0<2*π):=⟨by positivity⟩

/-- Finite profile variation at future relative time, with the null
zero-time section removed before applying a singular coarse envelope. -/
def difference (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (q θ η : ℝ) (p : ControlledProfile.Domain) : ℝ:=
  if 0<p.1 then profile P Λ u d (θ,(q+p.1,p.2))-profile P Λ u d (η,(q+p.1,p.2)) else 0

theorem difference_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (q θ η : ℝ) : Measurable (difference P Λ u d q θ η) := by
  have hm (a : ℝ) : Measurable (fun p : ControlledProfile.Domain=>(a,(q+p.1,p.2))):=
    measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk measurable_snd)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (((profile_measurable P Λ u d).comp (hm θ)).sub ((profile_measurable P Λ u d).comp (hm η)))
    measurable_const

theorem difference_coarse (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) {q : ℝ} (hq : 0≤q) (θ η : ℝ)
    (p : ControlledProfile.Domain) (hp : 0≤p.1) :
    |difference P Λ u d q θ η p|≤(2*P.upper)*p.1^(-(1/4:ℝ)) := by
  unfold difference
  split_ifs with ht
  · by_cases hr1 : p.1≤1
    · have hb : |profile P Λ u d (θ,(q+p.1,p.2))-profile P Λ u d (η,(q+p.1,p.2))|≤2*P.upper := by
        have ha:=profile_bounds P Λ u d (θ,(q+p.1,p.2))
        have hb:=profile_bounds P Λ u d (η,(q+p.1,p.2))
        rw [abs_le]
        constructor <;> linarith [P.lower_pos]
      have hw : 1≤p.1^(-(1/4:ℝ)) := by
        simpa only [one_rpow] using Real.rpow_le_rpow_of_nonpos ht hr1 (by norm_num : -(1/4:ℝ)≤0)
      exact hb.trans (by nlinarith [P.upper_nonneg])
    · have hout : q+p.1∉Ioc 0 P.horizon:=by
        intro hx
        have hh:=hx.2
        linarith [P.horizon_le_one,not_le.mp hr1]
      rw [profile_outside P Λ u d θ (p:=(q+p.1,p.2)) hout,
        profile_outside P Λ u d η (p:=(q+p.1,p.2)) hout,sub_self,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) P.upper_nonneg) (rpow_nonneg hp _)
  · rw [abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) P.upper_nonneg) (rpow_nonneg hp _)

/-- Sharp finite profile variation has time exponent zero. Every
restart time and both parameters are quantified before any integration. -/
theorem difference_sharp (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0≤Λ)
    (u d : CircleL2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (q θ η : ℝ) (r : ℝ) :
    normTwo haarAddCircle (fun x=>difference P Λ u d q θ η (r,x))≤
      2*(P.holder*(|θ - η| * ‖d‖)^P.exponent) := by
  by_cases ht : 0<r
  · by_cases hr : q+r∈Ioc 0 P.horizon
    · simpa only [difference,ht,ite_true] using profile_l2_holder P hΛ u d θ η hsmallL2 hr
    · have he : (fun x=>difference P Λ u d q θ η (r,x))=fun _ : HeatCircle=>0:=by
        funext x
        simp only [difference,ht,ite_true,profile_outside P Λ u d θ (p:=(q+r,x)) hr,
          profile_outside P Λ u d η (p:=(q+r,x)) hr,sub_self]
      rw [he]
      simp only [normTwo,zero_pow (by decide : 2≠0),integral_zero,sqrt_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg P.holder_nonneg
        (rpow_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) _))
  · have he : (fun x=>difference P Λ u d q θ η (r,x))=fun _ : HeatCircle=>0:=by
      funext x
      simp only [difference,ht,ite_false]
    rw [he]
    simp only [normTwo,zero_pow (by decide : 2≠0),integral_zero,sqrt_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg P.holder_nonneg
      (rpow_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) _))

end SHE.ProfileHolderScoreRates
