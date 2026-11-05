module

public import SHE.PolynomialInitialAgeTime
public import SHE.ScalarHeatBandTime
public import SHE.PolynomialGaussianDecay

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ScalarHeatBandInitialMass
open Set MeasureTheory Real ScalarHeatBandEnvelope

/-- The actual Gaussian heat-band gradient envelope, weighted by BOTH
future trace age and the singular original frozen-profile age, has the
full beta+2rho squared frequency gain. This directly supplies the
changed frozen-factor time integral; no annular exponential is assumed. -/
theorem mass {r c h β ρ p:ℝ} (hr:0<r) (hc:0<c) (hh:0<h)
    (hβ:β≤1) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (hp0:-1<p) (hp1:p≤0):
    let G:=fun t:ℝ=>t^(ρ-1/2)*(r^(β-1)*decay r (c*sqrt t) ((3-β)/2))^2*(h-t)^p
    IntegrableOn G (Ioc (0:ℝ) h) ∧
      (∫t in Ioc (0:ℝ) h,G t)≤
        (((1/2:ℝ)^p)*(1/(ρ+1/2)+1/(1-β/2-ρ))+2/(p+1))*
          c^(-1-2*ρ)*r^(2*β+4*ρ)*h^p:=by
  intro G
  let L:=c^2/r^4
  let K:=r^(2*β-2)
  have hL:0<L:=div_pos (sq_pos_of_pos hc) (pow_pos hr 4)
  have hK:0≤K:=rpow_nonneg hr.le _
  have hG:Measurable G:=by
    dsimp only [G,decay]
    fun_prop
  have hb(t:ℝ)(ht:t∈Ioo 0 h):
      |G t|≤K*((h-t)^p*PolynomialGaussianTime.kernel (ρ+1/2) ((3-β)/2) L t):=by
    have hd:=PolynomialGaussianDecay.decay_sq_bound hr hc ht.1
      (by linarith : 0≤(3-β)/2) (σ:=c*sqrt t) le_rfl
    have hs:(r^(β-1))^2=K:=by
      dsimp only [K]
      rw [←rpow_two,←rpow_mul hr.le]
      congr 1
      ring
    rw [abs_of_nonneg (by dsimp only [G];positivity [ht.1,sub_pos.mpr ht.2])]
    dsimp only [G]
    rw [mul_pow,hs]
    have he:=mul_le_mul_of_nonneg_left hd (mul_nonneg
      (mul_nonneg (rpow_nonneg ht.1.le (ρ-1/2)) hK)
      (rpow_nonneg (sub_pos.mpr ht.2).le p))
    convert he using 1 <;> (try simp only [PolynomialGaussianTime.kernel,L]) <;> ring
  have he:=PolynomialInitialAgeTime.dominated (by linarith : 0<ρ+1/2)
    (by linarith : ρ+1/2<(3-β)/2) hL hK hh hp0 hp1 G hG hb
  refine ⟨he.1,he.2.trans_eq ?_⟩
  have hscale:=ScalarHeatBandTime.scale_factor (β:=β) (ρ:=ρ) hr hc
  dsimp only [K,L]
  rw [show (3-β)/2-(ρ+1/2)=1-β/2-ρ by ring]
  calc
    _=(((1/2:ℝ)^p)*(1/(ρ+1/2)+1/(1-β/2-ρ))+2/(p+1))*
        (r^(2*β-2)*(c^2/r^4)^(-(ρ+1/2)))*h^p:=by ring
    _=_:=by rw [hscale];ring

end SHE.ScalarHeatBandInitialMass
