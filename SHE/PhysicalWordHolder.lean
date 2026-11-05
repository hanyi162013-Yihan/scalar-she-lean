module
public import SHE.FixedOldHessianBound

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

namespace SHE.FiniteProductHolder
open scoped BigOperators

theorem difference_bound {ι:Type*} [DecidableEq ι] (s:Finset ι)
    (f g d:ι→ℝ) {C:ℝ} (hC:1≤C)
    (hf:∀i∈s,|f i|≤C) (hg:∀i∈s,|g i|≤C)
    (hd:∀i∈s,0≤d i) (hfg:∀i∈s,|f i-g i|≤d i):
    |(∏i∈s,f i)-(∏i∈s,g i)|≤C^s.card*(∑i∈s,d i):=by
  have hC0:0≤C:=zero_le_one.trans hC
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert a s ha ih=>
    have hfs:∀i∈s,|f i|≤C:=fun i hi=>hf i (Finset.mem_insert_of_mem hi)
    have hgs:∀i∈s,|g i|≤C:=fun i hi=>hg i (Finset.mem_insert_of_mem hi)
    have hds:∀i∈s,0≤d i:=fun i hi=>hd i (Finset.mem_insert_of_mem hi)
    have hfgs:∀i∈s,|f i-g i|≤d i:=fun i hi=>hfg i (Finset.mem_insert_of_mem hi)
    have hi:=ih hfs hgs hds hfgs
    have hp:|∏i∈s,f i|≤C^s.card:=by
      rw [Finset.abs_prod]
      calc
        _≤∏_i∈s,C:=Finset.prod_le_prod₀ (fun _ _=>abs_nonneg _) hfs
        _=_:=by rw [Finset.prod_const]
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Finset.sum_insert ha,pow_succ]
    have he:f a*(∏i∈s,f i)-g a*(∏i∈s,g i)=
        (f a-g a)*(∏i∈s,f i)+g a*((∏i∈s,f i)-(∏i∈s,g i)):=by ring
    rw [he]
    have hb:=calc
      |(f a-g a)*(∏i∈s,f i)+g a*((∏i∈s,f i)-(∏i∈s,g i))|≤
          |f a-g a| * |∏i∈s,f i|+|g a| * |(∏i∈s,f i)-(∏i∈s,g i)|:=by
        simpa only [abs_mul] using abs_add_le ((f a-g a)*(∏i∈s,f i)) (g a*((∏i∈s,f i)-(∏i∈s,g i)))
      _≤d a*C^s.card+C*(C^s.card*(∑i∈s,d i)):=
        add_le_add (mul_le_mul (hfg a (Finset.mem_insert_self _ _)) hp (abs_nonneg _) (hd a (Finset.mem_insert_self _ _)))
          (mul_le_mul (hg a (Finset.mem_insert_self _ _)) hi (abs_nonneg _) hC0)
    have hm:=mul_nonneg (mul_nonneg (pow_nonneg hC0 s.card) (hd a (Finset.mem_insert_self _ _)))
      (sub_nonneg.mpr hC)
    nlinarith

end SHE.FiniteProductHolder

namespace SHE.WeightedBorelAverage
open MeasureTheory ProbabilityTheory GaussianIncrement
variable {X:Type*} [MeasurableSpace X] {n:ℕ}

/-- A signed fixed-old average preserves an actual directional Hölder
modulus, multiplied only by its true old-score absolute mass. -/
theorem directional_holder (μ:Measure X) (w:X→ℝ) (hw:Integrable w μ)
    (shift:X→State n) (hs:Measurable shift) (F:State n→ℝ) (hF:Measurable F)
    (B:ℝ) (hb:∀z,|F z|≤B) {K β:ℝ} (d:State n)
    (hh:∀x s t,|F (x+s • d)-F (x+t • d)|≤K*|s-t|^β)
    (z:State n) (s t:ℝ):
    |average μ w shift F (z+s • d)-average μ w shift F (z+t • d)|≤
      (K*∫x,|w x| ∂μ)*|s-t|^β:=by
  have hi (r:ℝ):Integrable (fun x=>w x*F (z+r • d+shift x)) μ:=
    integrable μ w hw shift hs F hF B hb (z+r • d)
  unfold average
  rw [←integral_sub (hi s) (hi t)]
  have hp (x:X):‖w x*F (z+s • d+shift x)-w x*F (z+t • d+shift x)‖≤
      (K*|s-t|^β)*|w x|:=by
    have hhx:=hh (z+shift x) s t
    have h1:z+s • d+shift x=z+shift x+s • d:=by abel
    have h2:z+t • d+shift x=z+shift x+t • d:=by abel
    rw [h1,h2,←mul_sub,Real.norm_eq_abs,abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hhx (abs_nonneg (w x))]
  have h:=norm_integral_le_of_norm_le (hw.norm.const_mul (K*|s-t|^β)) (ae_of_all _ hp)
  rw [Real.norm_eq_abs,integral_const_mul] at h
  simp only [Real.norm_eq_abs] at h
  convert h using 1 <;> ring

end SHE.WeightedBorelAverage
