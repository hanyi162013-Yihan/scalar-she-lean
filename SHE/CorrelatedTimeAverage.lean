module

public import SHE.HilbertFiniteAverage
public import SHE.PairedSourcePower

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.CorrelatedTimeAverage
open Set MeasureTheory Real
variable {T Y:Type*} [MeasurableSpace T] [MeasurableSpace Y]

/-- Old time is averaged BEFORE squaring. The true current energy may
vary with every old time; only its harmless finite cap is used to prove
integrability. The quantitative bound retains that true energy INSIDE
the positive time integral. -/
theorem energy (ν:Measure T) [IsFiniteMeasure ν] (μ:Measure Y) [IsProbabilityMeasure μ]
    (F:T×Y→ℝ) (hF:Measurable F) (A E:T→ℝ)
    (hA:Measurable A) (hAi:Integrable A ν) (hA0:∀t,0≤A t)
    (hE:Measurable E) (hE0:∀t,0≤E t)
    {C M P χ:ℝ} (hC:0≤C) (hM:0≤M) (hP:0≤P) (hχ:0≤χ)
    (hcap:∀t,E t≤M)
    (hMom:∀ᵐ t ∂ν,Integrable (fun y=>|F (t,y)|^2) μ ∧
      (∫y,|F (t,y)|^2 ∂μ)≤C*(A t)^2*((E t)^χ+P^χ)):
    let G:=fun y=>∫t,F (t,y) ∂ν
    Integrable F (ν.prod μ) ∧ Integrable (fun y=>|G y|^2) μ ∧
      (∫y,|G y|^2 ∂μ)≤2*C*((∫t,A t*(E t)^(χ/2) ∂ν)^2+
        (∫t,A t ∂ν)^2*P^χ):=by
  intro G
  let D:=fun t=>sqrt C*A t*((E t)^(χ/2)+P^(χ/2))
  have hpow(t):((E t)^(χ/2))^2=(E t)^χ:=by
    rw [←Real.rpow_mul_natCast (hE0 t)]
    congr 1
    ring
  have hpp:(P^(χ/2))^2=P^χ:=by
    rw [←Real.rpow_mul_natCast hP]
    congr 1
    ring
  have hAEi:Integrable (fun t=>A t*(E t)^(χ/2)) ν:=by
    apply (hAi.const_mul (M^(χ/2))).mono' ((hA.mul (hE.pow_const _)).aestronglyMeasurable)
    apply ae_of_all
    intro t
    change ‖A t*(E t)^(χ/2)‖≤_
    rw [Real.norm_of_nonneg (mul_nonneg (hA0 t) (rpow_nonneg (hE0 t) _))]
    have hh:=mul_le_mul_of_nonneg_left (rpow_le_rpow (hE0 t) (hcap t) (by positivity : 0≤χ/2)) (hA0 t)
    simpa only [mul_comm] using hh
  have hDi:Integrable D ν:=by
    have hh:=(hAEi.add (hAi.mul_const (P^(χ/2)))).const_mul (sqrt C)
    convert! hh using 1
    funext t
    simp only [D,Pi.add_apply,Pi.mul_apply]
    ring
  have hDm:Measurable D:=((measurable_const.mul hA).mul ((hE.pow_const _).add_const _))
  have hD0(t):0≤D t:=mul_nonneg (mul_nonneg (sqrt_nonneg _) (hA0 t))
    (add_nonneg (rpow_nonneg (hE0 t) _) (rpow_nonneg hP _))
  have hsec:∀ᵐ t ∂ν,Integrable (fun y=>|F (t,y)|^2) μ ∧
      (∫y,|F (t,y)|^2 ∂μ)≤(D t)^2:=by
    filter_upwards [hMom] with t ht
    refine ⟨ht.1,ht.2.trans ?_⟩
    have he:=rpow_nonneg (hE0 t) (χ/2)
    have hp:=rpow_nonneg hP (χ/2)
    have hb:(E t)^χ+P^χ≤((E t)^(χ/2)+P^(χ/2))^2:=by
      nlinarith [hpow t,hpp,mul_nonneg he hp]
    have hz:=mul_le_mul_of_nonneg_left hb (mul_nonneg hC (sq_nonneg (A t)))
    convert! hz using 1
    simp only [D,mul_pow,Real.sq_sqrt hC]
    try ring
  have hh:=HilbertParameterAverage.finite_energy μ ν F hF D hDm hDi hD0
    (hsec.mono (fun _ ht=>by simpa only [Real.norm_eq_abs] using ht.1))
    (hsec.mono (fun _ ht=>by simpa only [Real.norm_eq_abs] using ht.2))
  have hh':Integrable F (ν.prod μ) ∧ Integrable (fun y=>|G y|^2) μ ∧
      (∫y,|G y|^2 ∂μ)≤(∫t,D t ∂ν)^2:=by
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨hh'.1,hh'.2.1,hh'.2.2.trans ?_⟩
  have he:(∫t,D t ∂ν)=sqrt C*((∫t,A t*(E t)^(χ/2) ∂ν)+(∫t,A t ∂ν)*P^(χ/2)):=by
    change (∫t,sqrt C*A t*((E t)^(χ/2)+P^(χ/2)) ∂ν)=_
    calc
      _=sqrt C*(∫t,A t*(E t)^(χ/2)+A t*P^(χ/2) ∂ν):=by
        rw [←integral_const_mul]
        congr 1
        funext t
        ring
      _=_:=by rw [integral_add hAEi (hAi.mul_const _),integral_mul_const]
  rw [he,mul_pow,Real.sq_sqrt hC]
  have hs:=sq_nonneg ((∫t,A t*(E t)^(χ/2) ∂ν)-(∫t,A t ∂ν)*P^(χ/2))
  have hb:((∫t,A t*(E t)^(χ/2) ∂ν)+(∫t,A t ∂ν)*P^(χ/2))^2≤
      2*((∫t,A t*(E t)^(χ/2) ∂ν)^2+(∫t,A t ∂ν)^2*P^χ):=by
    nlinarith [hpp]
  exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (by ring)

end SHE.CorrelatedTimeAverage
