module
public import SHE.HeatTorusKernel
public import SHE.HeatOverlap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.TwoPointHeatLine
open Real MeasureTheory HeatLine HeatOverlap

def gaussian(t a x:ℝ):ℝ:=exp (-(1/(4*t))*(x-a)^2)
def pair(t a b u v:ℝ)(z:ℂ):ℂ:=(u:ℂ)*heatEntire t a z+(v:ℂ)*heatEntire t b z

theorem heat_real(t a x:ℝ):heatEntire t a (x:ℂ)=(gaussian t a x:ℂ):=by
  unfold heatEntire gaussian
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem norm_pair_sq(t a b u v x:ℝ):‖pair t a b u v (x:ℂ)‖^2=
    u^2*(gaussian t a x*gaussian t a x)+v^2*(gaussian t b x*gaussian t b x)+
      (2*u*v)*(gaussian t a x*gaussian t b x):=by
  unfold pair
  rw [heat_real,heat_real,←Complex.ofReal_mul,←Complex.ofReal_mul,←Complex.ofReal_add,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

theorem energy{t:ℝ}(ht:0<t)(a b u v:ℝ):
    Integrable (fun x:ℝ=>‖pair t a b u v (x:ℂ)‖^2) ∧
      (∫x:ℝ,‖pair t a b u v (x:ℂ)‖^2)=
        sqrt (2*Real.pi*t)*(u^2+v^2+2*u*v*exp (-(a-b)^2/(8*t))):=by
  have ha:0<1/(4*t):=by positivity
  have haa:Integrable (fun x=>gaussian t a x*gaussian t a x):=integrable_gaussian_product ha ha a a
  have hbb:Integrable (fun x=>gaussian t b x*gaussian t b x):=integrable_gaussian_product ha ha b b
  have hab:Integrable (fun x=>gaussian t a x*gaussian t b x):=integrable_gaussian_product ha ha a b
  have hsum:1/(4*t)+1/(4*t)=1/(2*t):=by field_simp;ring
  have hmul:(1/(4*t))*(1/(4*t))/(1/(4*t)+1/(4*t))=1/(8*t):=by
    rw [hsum]
    field_simp
    <;> ring
  have hdiv:Real.pi/(1/(4*t)+1/(4*t))=2*Real.pi*t:=by rw [hsum];field_simp <;> ring
  have hprod(c d:ℝ):(∫x:ℝ,gaussian t c x*gaussian t d x)=
      sqrt (2*Real.pi*t)*exp (-(c-d)^2/(8*t)):=by
    have he:=integral_gaussian_product ha ha c d
    rw [hdiv,hmul] at he
    convert! he using 1
    ring
  simp_rw [norm_pair_sq]
  have hia:Integrable (fun x=>u^2*(gaussian t a x*gaussian t a x)):=haa.const_mul _
  have hib:Integrable (fun x=>v^2*(gaussian t b x*gaussian t b x)):=hbb.const_mul _
  have hic:Integrable (fun x=>(2*u*v)*(gaussian t a x*gaussian t b x)):=hab.const_mul _
  refine ⟨(hia.add hib).add hic,?_⟩
  have hs1:=integral_add (hia.add hib) hic
  have hs2:=integral_add hia hib
  simp only [Pi.add_apply] at hs1 hs2
  rw [hs1,hs2]
  simp only [integral_const_mul,hprod,sub_self,zero_pow (by norm_num:(2:ℕ)≠0),neg_zero,
    zero_div,exp_zero,mul_one]
  ring

/-- Actual line heat observations at separated points have a uniform
Gram lower bound. The coefficients may have arbitrary opposite signs. -/
theorem separated_lower{t:ℝ}(ht:0<t)(a b u v:ℝ)(hsep:4*sqrt t≤|a-b|):
    (sqrt t/2)*(u^2+v^2)≤∫x:ℝ,‖pair t a b u v (x:ℂ)‖^2:=by
  rw [(energy ht a b u v).2]
  have hsq:16*t≤(a-b)^2:=by
    have he:=pow_le_pow_left₀ (by positivity:0≤4*sqrt t) hsep 2
    rw [mul_pow,sq_sqrt ht.le,sq_abs] at he
    norm_num at he
    exact he
  have hex:-(a-b)^2/(8*t)≤-(2:ℝ):=(div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hE:exp (-(a-b)^2/(8*t))≤1/2:=
    (exp_le_exp.mpr hex).trans (by simpa only [one_div] using exp_neg_le_inverse (by norm_num:(0:ℝ)<2))
  have hEn:0≤exp (-(a-b)^2/(8*t)):=(exp_pos _).le
  have hsum:0≤u^2+v^2:=add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcross:-(u^2+v^2)≤2*u*v:=by nlinarith [sq_nonneg (u+v)]
  have hm:=mul_le_mul_of_nonneg_right hcross hEn
  have hm':=mul_le_mul_of_nonneg_left hE hsum
  have hpoly:(u^2+v^2)/2≤u^2+v^2+2*u*v*exp (-(a-b)^2/(8*t)):=by nlinarith
  have hroot:sqrt t≤sqrt (2*Real.pi*t):=sqrt_le_sqrt (by nlinarith [Real.one_le_pi_div_two])
  have h₁:=mul_le_mul_of_nonneg_left hpoly (sqrt_nonneg (2*Real.pi*t))
  have h₂:=mul_le_mul_of_nonneg_right hroot (div_nonneg hsum (by norm_num:(0:ℝ)≤2))
  nlinarith

end SHE.TwoPointHeatLine
