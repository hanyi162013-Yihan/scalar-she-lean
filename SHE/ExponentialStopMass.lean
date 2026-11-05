module

public import SHE.PredictableTime
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ExponentialStopMass
open MeasureTheory Set PredictableL2
open scoped NNReal

theorem exponential_tail (Λ r t : ℝ) :
    Λ*(∫ s in r..t,Real.exp (-Λ*(t-s)))=1-Real.exp (-Λ*(t-r)) := by
  have hd (s : ℝ) : HasDerivAt (fun u => Real.exp (-Λ*(t-u)))
      (Λ*Real.exp (-Λ*(t-s))) s := by
    have hh := (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-Λ)).exp
    simpa only [Pi.sub_apply,id_eq,zero_sub,neg_mul_neg,mul_one,mul_comm] using hh
  have hint : IntervalIntegrable (fun s => Λ*Real.exp (-Λ*(t-s))) volume r t :=
    (show Continuous (fun s : ℝ => Λ*Real.exp (-Λ*(t-s))) by fun_prop).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hint
  rw [intervalIntegral.integral_const_mul] at he
  simpa only [sub_self,mul_zero,Real.exp_zero] using he

def mass (Λ : ℝ) (t r : ℝ≥0) : ℝ :=
  ∫ s,if r<s then Real.exp (-Λ*((t:ℝ)-(s:ℝ))) else 0 ∂timeMeasure t

theorem mass_eq_integral {t r : ℝ≥0} (hr : r≤t) (Λ : ℝ) :
    mass Λ t r=∫ s in (r:ℝ)..(t:ℝ),Real.exp (-Λ*((t:ℝ)-s)) := by
  rw [mass,timeMeasure_integral]
  have he : (∫ s in Ioc (0:ℝ) (t:ℝ),if r<s.toNNReal then Real.exp (-Λ*((t:ℝ)-(s.toNNReal:ℝ))) else 0)=
      ∫ s in Ioc (0:ℝ) (t:ℝ),(Ioi (r:ℝ)).indicator (fun u => Real.exp (-Λ*((t:ℝ)-u))) s := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hcoe : (s.toNNReal:ℝ)=s := Real.coe_toNNReal _ hs.1.le
    have hiff : r<s.toNNReal↔(r:ℝ)<s := by rw [← NNReal.coe_lt_coe,hcoe]
    simp only [hcoe,hiff,Set.indicator,mem_Ioi]
  rw [he,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (r:ℝ)∩Ioc (0:ℝ) (t:ℝ)=Ioc (r:ℝ) (t:ℝ) := by
    ext s
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · exact fun hs => ⟨hs.1,hs.2.2⟩
    · exact fun hs => ⟨hs.1,lt_of_le_of_lt r.2 hs.1,hs.2⟩
  rw [hset,intervalIntegral.integral_of_le (show (r:ℝ)≤t from hr)]

theorem mul_mass (Λ : ℝ) (t r : ℝ≥0) :
    Λ*mass Λ t r=if r<t then 1-Real.exp (-Λ*((t:ℝ)-(r:ℝ))) else 0 := by
  by_cases hr : r<t
  · rw [if_pos hr,mass_eq_integral hr.le]
    exact exponential_tail Λ (r:ℝ) (t:ℝ)
  · rw [if_neg hr]
    have hz : mass Λ t r=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [timeMeasure_ae_mem t] with s hs
      exact if_neg (not_lt.mpr (hs.2.trans (le_of_not_gt hr)))
    rw [hz,mul_zero]

end SHE.ExponentialStopMass
