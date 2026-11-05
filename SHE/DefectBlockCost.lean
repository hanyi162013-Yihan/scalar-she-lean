module
public import SHE.DefectHeatClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.DefectBlockCost
open Real

private theorem sqrt_inverse {d:ℝ}(hd:0<d):sqrt d⁻¹=d^(-(1/2:ℝ)):=by
  rw [sqrt_eq_rpow,←rpow_neg_one d,←rpow_mul hd.le]
  congr 1
  norm_num

/-- Literal native block trace cost, with a constant fixed before the
control strength and both original physical ages. -/
theorem cost (K θ ellR ellC W B Csigned ρ:ℝ)(hK:0≤K)(hθ:0<θ)
    (hellR:0<ellR)(hellC:0<ellC)(hW:0≤W)(hB:1≤B)(hSigned:0≤Csigned)(n:ℕ):
    ∃C:ℝ,0<C ∧ ∀Λ di dj:ℝ,1≤Λ→0<di→0<dj→
      let w:=di/(4*Real.pi^2)
      let Ec:=(max B 8*min 1 (Λ*di)^2/di)/(ellR/2)
      let Eb:=(max B 8/dj)/(ellC/2)*(4*W*(n:ℝ))
      Λ^(-ρ/2)*sqrt (Ec*Eb*K*sqrt B*sqrt w*Csigned*
        (Λ^ρ*(θ*w)^(-(1/2:ℝ))+(θ*w)^(-(1/2:ℝ)-ρ)))≤
      C*min 1 (Λ*di)*di^(-(1/2:ℝ))*dj^(-(1/2:ℝ))*
        (1+Λ^(-ρ/2)*di^(-ρ/2)):=by
  let clock:=4*Real.pi^2
  let AR:=max B 8/(ellR/2)
  let AC:=max B 8/(ellC/2)*(4*W*(n:ℝ))
  let D:=AR*AC*K*sqrt B*Csigned
  let T:=sqrt (max (θ^(-(1/2:ℝ))) (θ^(-(1/2:ℝ)-ρ)))
  let C:=1+sqrt D*T*max 1 (clock^(ρ/2))
  have hclock:0<clock:=by dsimp [clock];positivity
  have hAR:0≤AR:=div_nonneg ((zero_le_one.trans hB).trans (le_max_left _ _)) (by positivity)
  have hAC:0≤AC:=by dsimp [AC];positivity
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=sqrt_nonneg _
  have hC:0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro Λ di dj hΛ hdi hdj w Ec Eb
  have hΛp:0<Λ:=zero_lt_one.trans_le hΛ
  have hw:0<w:=div_pos hdi hclock
  let m:=min 1 (Λ*di)
  have hm:0≤m:=le_min zero_le_one (mul_nonneg hΛp.le hdi.le)
  have hfactor:Ec*Eb*K*sqrt B*sqrt w*Csigned*
      (Λ^ρ*(θ*w)^(-(1/2:ℝ))+(θ*w)^(-(1/2:ℝ)-ρ))=
        D*m^2*di⁻¹*dj⁻¹*DefectHeatClock.traceAge θ Λ ρ w:=by
    dsimp only [Ec,Eb,D,AR,AC,m,DefectHeatClock.traceAge]
    simp only [div_eq_mul_inv]
    ring
  have hs:sqrt (Ec*Eb*K*sqrt B*sqrt w*Csigned*
      (Λ^ρ*(θ*w)^(-(1/2:ℝ))+(θ*w)^(-(1/2:ℝ)-ρ)))=
        sqrt D*m*di^(-(1/2:ℝ))*dj^(-(1/2:ℝ))*sqrt (DefectHeatClock.traceAge θ Λ ρ w):=by
    rw [hfactor,sqrt_mul (by positivity:0≤D*m^2*di⁻¹*dj⁻¹),
      sqrt_mul (by positivity:0≤D*m^2*di⁻¹),sqrt_mul (by positivity:0≤D*m^2),
      sqrt_mul hD,sqrt_sq hm,sqrt_inverse hdi,sqrt_inverse hdj]
  have htrace:=DefectHeatClock.normalized_sqrt_trace (ρ:=ρ) hθ hΛp hw
  have hwp:w^(-ρ/2)=clock^(ρ/2)*di^(-ρ/2):=by
    dsimp only [w]
    rw [div_rpow hdi.le hclock.le,div_eq_mul_inv,←rpow_neg hclock.le]
    rw [show -(-ρ/2)=ρ/2 by ring]
    ring
  let x:=Λ^(-ρ/2)*di^(-ρ/2)
  have hx:0≤x:=mul_nonneg (rpow_nonneg hΛp.le _) (rpow_nonneg hdi.le _)
  have hclip:1+Λ^(-ρ/2)*w^(-ρ/2)≤max 1 (clock^(ρ/2))*(1+x):=by
    rw [hwp,mul_add,mul_one]
    have hc:=mul_le_mul_of_nonneg_right (le_max_right 1 (clock^(ρ/2))) hx
    have h1:=le_max_left (1:ℝ) (clock^(ρ/2))
    dsimp only [x] at hc ⊢
    nlinarith
  have htotal:=mul_le_mul_of_nonneg_left (htrace.trans
    (mul_le_mul_of_nonneg_left hclip hT))
      (show 0≤sqrt D*m*di^(-(1/2:ℝ))*dj^(-(1/2:ℝ)) by positivity)
  rw [hs]
  have he:Λ^(-ρ/2)*(sqrt D*m*di^(-(1/2:ℝ))*dj^(-(1/2:ℝ))*
      sqrt (DefectHeatClock.traceAge θ Λ ρ w))≤
      (sqrt D*T*max 1 (clock^(ρ/2)))*m*di^(-(1/2:ℝ))*dj^(-(1/2:ℝ))*(1+x):=by
    convert htotal using 1 <;> ring
  apply he.trans
  have hcoeff:sqrt D*T*max 1 (clock^(ρ/2))≤C:=by dsimp [C];linarith
  have hrow:0≤m*di^(-(1/2:ℝ))*dj^(-(1/2:ℝ))*(1+x):=by positivity
  convert mul_le_mul_of_nonneg_right hcoeff hrow using 1 <;> ring

end SHE.DefectBlockCost
