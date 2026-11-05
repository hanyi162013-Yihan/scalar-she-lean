module
public import SHE.NativeBesselSchurTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselSchurIntegral
open Set MeasureTheory Real

def weight (ρ Λ t:ℝ):ℝ:=Real.exp (-Λ*t)*t^(ρ-1)

theorem weight_integrable {ρ Λ:ℝ}(hρ:0<ρ)(hΛ:0<Λ):
    IntegrableOn (weight ρ Λ) (Ioi 0):=by
  convert! damped_power_integrable (Λ:=Λ/2) (by positivity) hρ using 1
  funext t
  dsimp only [weight]
  congr 2
  ring

theorem weight_integral {ρ Λ:ℝ}(hρ:0<ρ)(hΛ:0<Λ):
    (∫t in Ioi (0:ℝ),weight ρ Λ t)=Λ^(-ρ)*Real.Gamma ρ:=by
  rw [show weight ρ Λ=(fun t:ℝ=>t^(ρ-1)*Real.exp (-(Λ*t))) by
    funext t;dsimp [weight];ring]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hρ hΛ,one_div,←Real.rpow_neg_eq_inv_rpow]

/-- Actual positive heat Schur mass integrated against the genuine
massive Bessel Laplace density. The spatial gain is M^(2rho); the
constant spatial mode retains its Lambda^(-rho) factor. -/
theorem bound {ρ Λ B M:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(hΛ:0<Λ)(hB:0<B)(hM:0<M):
    (∫t in Ioi (0:ℝ),weight ρ Λ t*min 1 ((1+B*t^(-(1/2:ℝ)))*M))≤
      M*Λ^(-ρ)*Real.Gamma ρ+(1/ρ+1/(1/2-ρ))*(B*M)^(2*ρ):=by
  have hw:=weight_integrable hρ hΛ
  have hD:0<B*M:=mul_pos hB hM
  have hp:=NativeBesselSchurTime.integrable hρ hρhalf hD
  have hw0:∀t∈Ioi (0:ℝ),0≤weight ρ Λ t:=by
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  have hc0:∀t∈Ioi (0:ℝ),0≤min 1 ((1+B*t^(-(1/2:ℝ)))*M):=by
    intro t ht
    exact le_min (by norm_num) (mul_nonneg
      (add_nonneg (by norm_num) (mul_nonneg hB.le (Real.rpow_nonneg ht.le _))) hM.le)
  have hi:IntegrableOn (fun t=>weight ρ Λ t*min 1 ((1+B*t^(-(1/2:ℝ)))*M)) (Ioi 0):=by
    apply hw.mono' (by unfold weight;fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 t ht) (hc0 t ht))]
    exact mul_le_of_le_one_right (hw0 t ht) (min_le_left _ _)
  have hb:(∫t in Ioi (0:ℝ),weight ρ Λ t*min 1 ((1+B*t^(-(1/2:ℝ)))*M))≤
      ∫t in Ioi (0:ℝ),weight ρ Λ t*M+NativeBesselSchurTime.clipped ρ (B*M) t:=by
    apply integral_mono_ae hi ((hw.mul_const M).add hp)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs:=NativeBesselSchurTime.min_split hB.le hM.le ht.le
    have hex:Real.exp (-Λ*t)≤1:=Real.exp_le_one_iff.mpr (by simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hΛ.le ht.le))
    have hwt:weight ρ Λ t≤t^(ρ-1):=mul_le_of_le_one_left (Real.rpow_nonneg ht.le _) hex
    have hq:0≤min 1 (B*M*t^(-(1/2:ℝ))):=
      le_min (by norm_num) (mul_nonneg hD.le (Real.rpow_nonneg ht.le _))
    calc
      _≤weight ρ Λ t*(M+min 1 (B*M*t^(-(1/2:ℝ)))):=mul_le_mul_of_nonneg_left hs (hw0 t ht)
      _=weight ρ Λ t*M+weight ρ Λ t*min 1 (B*M*t^(-(1/2:ℝ))):=by ring
      _≤_:=by
        change weight ρ Λ t*M+weight ρ Λ t*min 1 (B*M*t^(-(1/2:ℝ)))≤
          weight ρ Λ t*M+t^(ρ-1)*min 1 (B*M*t^(-(1/2:ℝ)))
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hwt hq)
  rw [integral_add (hw.mul_const M) hp,integral_mul_const,weight_integral hρ hΛ,
    NativeBesselSchurTime.integral hρ hρhalf hD] at hb
  exact hb.trans_eq (by ring)

end SHE.NativeBesselSchurIntegral
