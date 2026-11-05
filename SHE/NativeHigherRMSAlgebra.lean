module
public import SHE.NativeHigherEnergyFactors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeHigherRMSAlgebra
open Real

/-- Exact newest-gap square normalization for the two actual higher
noise legs, retaining the distinguished current displacement. -/
theorem split (K Ccur Cpast w δ s Eq Ev W sharp ρ χ:ℝ)
    (hK:0≤K)(hCc:0≤Ccur)(hCp:0≤Cpast)(hw:0<w)(hδ:0<δ)(hs:0<s)
    (hEq:0≤Eq)(hEv:0≤Ev)(hW:0≤W)(hsharp:0≤sharp):
    K*w^ρ*δ⁻¹*W^2*sharp^2*
        (8*Ccur*δ^(-χ/2)*Eq^χ+2*Cpast*s^(-(1/2:ℝ))*Ev)≤
      (w^(ρ/2)*(sqrt (8*K*Ccur)*Eq^(χ/2)*δ^((2-χ)/4-1)*(W*sharp)+
        sqrt (2*K*Cpast)*sqrt Ev*s^(-(1/4:ℝ))*δ^(-(1/2:ℝ))*(W*sharp)))^2 :=by
  let x:=sqrt (8*K*Ccur)*Eq^(χ/2)*δ^((2-χ)/4-1)*(W*sharp)
  let y:=sqrt (2*K*Cpast)*sqrt Ev*s^(-(1/4:ℝ))*δ^(-(1/2:ℝ))*(W*sharp)
  have hx:0≤x:=by dsimp only [x];positivity
  have hy:0≤y:=by dsimp only [y];positivity
  have heq:(Eq^(χ/2))^2=Eq^χ:=by
    rw [←Real.rpow_mul_natCast hEq]
    congr 1
    ring
  have hwp:(w^(ρ/2))^2=w^ρ:=by
    rw [←Real.rpow_mul_natCast hw.le]
    congr 1
    ring
  have hδp:(δ^((2-χ)/4-1))^2=δ⁻¹*δ^(-χ/2):=by
    rw [←Real.rpow_mul_natCast hδ.le,←Real.rpow_neg_one,
      ←Real.rpow_add hδ]
    congr 1
    ring
  have hδh:(δ^(-(1/2:ℝ)))^2=δ⁻¹:=by
    rw [←Real.rpow_mul_natCast hδ.le]
    norm_num [Real.rpow_neg_one]
  have hsh:=NativeHigherEnergyFactors.quarter_power hs.le
  have hnorm:K*w^ρ*δ⁻¹*W^2*sharp^2*
      (8*Ccur*δ^(-χ/2)*Eq^χ+2*Cpast*s^(-(1/2:ℝ))*Ev)=w^ρ*(x^2+y^2):=by
    dsimp only [x,y]
    simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤8*K*Ccur),
      Real.sq_sqrt (by positivity : 0≤2*K*Cpast),Real.sq_sqrt hEv,heq,hδp,hδh,hsh]
    ring
  rw [hnorm]
  change w^ρ*(x^2+y^2)≤(w^(ρ/2)*(x+y))^2
  calc
    w^ρ*(x^2+y^2)≤w^ρ*(x+y)^2:=mul_le_mul_of_nonneg_left
      (by nlinarith [mul_nonneg hx hy]) (rpow_nonneg hw.le ρ)
    _=(w^(ρ/2)*(x+y))^2:=by rw [mul_pow,hwp]


/-- Replacement of the two literal section budgets by their actual
current and past powers, before applying the RMS square. -/
theorem trace_split (K Ccur Cpast w δ s Eq Ev W sharp ρ χ cur past:ℝ)
    (hK:0≤K)(hCc:0≤Ccur)(hCp:0≤Cpast)(hw:0<w)(hδ:0<δ)(hs:0<s)
    (hEq:0≤Eq)(hEv:0≤Ev)(hW:0≤W)(hsharp:0≤sharp)
    (hc:cur=Ccur*δ^(-χ/2)*Eq^χ)
    (hp:past≤Cpast*sharp^2*s^(-(1/2:ℝ))*Ev):
    K*w^ρ*δ⁻¹*W^2*(8*sharp^2*cur+2*past)≤
      (w^(ρ/2)*(sqrt (8*K*Ccur)*Eq^(χ/2)*δ^((2-χ)/4-1)*(W*sharp)+
        sqrt (2*K*Cpast)*sqrt Ev*s^(-(1/4:ℝ))*δ^(-(1/2:ℝ))*(W*sharp)))^2 :=by
  have hh:=mul_le_mul_of_nonneg_left hp
    (by positivity : 0≤2*K*w^ρ*δ⁻¹*W^2)
  calc
    _=K*w^ρ*δ⁻¹*W^2*(8*sharp^2*cur)+2*K*w^ρ*δ⁻¹*W^2*past:=by ring
    _≤K*w^ρ*δ⁻¹*W^2*(8*sharp^2*cur)+
        2*K*w^ρ*δ⁻¹*W^2*(Cpast*sharp^2*s^(-(1/2:ℝ))*Ev):=add_le_add le_rfl hh
    _=K*w^ρ*δ⁻¹*W^2*sharp^2*(8*Ccur*δ^(-χ/2)*Eq^χ+2*Cpast*s^(-(1/2:ℝ))*Ev):=by rw [hc];ring
    _≤_:=split K Ccur Cpast w δ s Eq Ev W sharp ρ χ hK hCc hCp hw hδ hs hEq hEv hW hsharp

end SHE.NativeHigherRMSAlgebra
