module

public import SHE.FiniteMomentSum
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteSpatialBaseline
open MeasureTheory Real
open scoped BigOperators
variable {ι Ω W : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace W]
variable (μ : Measure Ω) [SFinite μ] (ν : Measure W) [SFinite ν]

/-- Absolute integrability justifies the literal finite baseline sum
inside old space. The final L2 estimate uses old-space averages BEFORE
squaring and retains the individual erased-leaf bounds. -/
theorem averaged_energy (F : ι→Ω×W→ℝ) (hF : ∀ i,Measurable (F i))
    (hJoint : ∀ i,Integrable (F i) (μ.prod ν))
    (hi : ∀ i,Integrable (fun z=>|∫ w,F i (z,w) ∂ν|^2) μ)
    (C : ι→ℝ) (hb : ∀ i,(∫ z,|∫ w,F i (z,w) ∂ν|^2 ∂μ)≤C i) :
    Integrable (fun z=>|∫ w,-(∑ i,F i (z,w)) ∂ν|^2) μ ∧
      (∫ z,|∫ w,-(∑ i,F i (z,w)) ∂ν|^2 ∂μ)≤
        (Fintype.card ι:ℝ)*∑ i,C i := by
  let A:=fun i z=>∫ w,F i (z,w) ∂ν
  let B:=fun z=>(Fintype.card ι:ℝ)*∑ i,|A i z|^2
  have hA (i):Measurable (A i):=(hF i).stronglyMeasurable.integral_prod_right'.measurable
  have hB : Integrable B μ:=(integrable_finsetSum Finset.univ (fun i _=>hi i)).const_mul _
  have hpoint (z) : |∑ i,A i z|^2≤B z:=by
    have ha:=Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun i=>A i z)
    have hh:=pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hp:=FiniteMomentSum.sum_pow_le 2 (by norm_num) (fun i=>|A i z|) (fun _=>abs_nonneg _)
    exact hh.trans (by simpa only [B,Nat.reduceSub,pow_one] using hp)
  have hsum : Integrable (fun z=>|∑ i,A i z|^2) μ:=by
    apply hB.mono' ((continuous_abs.measurable.comp
      (Finset.measurable_sum Finset.univ (fun i _=>hA i))).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hpoint z)
  have hval : (∫ z,|∑ i,A i z|^2 ∂μ)≤(Fintype.card ι:ℝ)*∑ i,C i:=by
    calc
      _≤∫ z,B z ∂μ:=integral_mono hsum hB hpoint
      _=(Fintype.card ι:ℝ)*∑ i,(∫ z,|A i z|^2 ∂μ):=by
        rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)]
      _≤_:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hb i)) (Nat.cast_nonneg _)
  have hsections : ∀ᵐ z ∂μ,∀ i,Integrable (fun w=>F i (z,w)) ν:=
    (ae_all_iff).mpr (fun i=>(hJoint i).prod_right_ae)
  have he : (fun z=>|∫ w,-(∑ i,F i (z,w)) ∂ν|^2)=ᵐ[μ] fun z=>|∑ i,A i z|^2:=by
    filter_upwards [hsections] with z hz
    rw [integral_neg,integral_finsetSum _ (fun i _=>hz i),abs_neg]
  exact ⟨hsum.congr he.symm,(integral_congr_ae he).trans_le hval⟩

end SHE.FiniteSpatialBaseline
