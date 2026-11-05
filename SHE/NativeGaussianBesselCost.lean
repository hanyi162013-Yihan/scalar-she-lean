module
public import SHE.NativeBesselSchurIntegral
public import SHE.NativeGaussianCovarianceKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeGaussianBesselCost
open Set MeasureTheory Real NativeGaussianCovarianceKernel

def heatFactor : ℝ := StoppedFourier.heatConstant*(1/2:ℝ)^(-(1/2:ℝ))
def bound (s L Λ ρ η:ℝ):ℝ :=
  (NativeGaussianCircleMass.mass s L+η)*Λ^(-ρ)+
    (1/ρ+1/(1/2-ρ))/Real.Gamma ρ*
      (heatFactor*NativeGaussianCircleMass.mass s L)^(2*ρ)

theorem heatFactor_pos : 0<heatFactor := by
  unfold heatFactor
  exact mul_pos StoppedFourier.heatConstant_pos (Real.rpow_pos_of_pos (by norm_num) _)

theorem cost_eq (s L t η:ℝ) (ht:0<t) :
    cost s L t η = min 1 ((1+heatFactor*t^(-(1/2:ℝ)))*NativeGaussianCircleMass.mass s L)+η := by
  unfold cost heatFactor
  rw [show t/2=t*(1/2:ℝ) by ring, Real.mul_rpow ht.le (by norm_num)]
  congr 3
  ring

theorem mass_pos {s L:ℝ}(hs:1<s)(hL:0<L):0<NativeGaussianCircleMass.mass s L := by
  unfold NativeGaussianCircleMass.mass
  have : 0<s-1 := by linarith
  positivity

theorem cost_nonneg {s L t η:ℝ}(hs:1<s)(hL:0≤L)(ht:0<t)(hη:0≤η):0≤cost s L t η := by
  unfold cost
  apply add_nonneg _ hη
  apply le_min (by norm_num)
  have hm:0≤NativeGaussianCircleMass.mass s L := by
    unfold NativeGaussianCircleMass.mass
    have : 0<s-1 := by linarith
    positivity
  exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg StoppedFourier.heatConstant_pos.le (Real.rpow_nonneg (by positivity) _))) hm

/-- The actual native heat constant and Gamma normalization are retained;
the spatial constant mode and the long-window floor remain explicit. -/
theorem integral_bound {s L Λ ρ η:ℝ}(hs:1<s)(hL:0<L)(hΛ:0<Λ)
    (hρ:0<ρ)(hρhalf:ρ<1/2)(hη:0≤η):
    IntegrableOn (fun t=>NativeBesselSchurIntegral.weight ρ Λ t / Real.Gamma ρ *cost s L t η) (Ioi 0) ∧
    (∫t in Ioi (0:ℝ),NativeBesselSchurIntegral.weight ρ Λ t / Real.Gamma ρ *cost s L t η)≤
      bound s L Λ ρ η := by
  let W:=NativeBesselSchurIntegral.weight ρ Λ
  let M:=NativeGaussianCircleMass.mass s L
  have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
  have hw:=NativeBesselSchurIntegral.weight_integrable hρ hΛ
  have hwm:IntegrableOn (fun t=>W t*cost s L t η) (Ioi 0):=by
    apply (hw.mul_const (1+η)).mono' (by unfold W NativeBesselSchurIntegral.weight cost;fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw0:0≤W t:=mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw0 (cost_nonneg hs hL.le ht hη))]
    exact mul_le_mul_of_nonneg_left (show cost s L t η≤1+η from by unfold cost; have hh:=min_le_left (1:ℝ) ((1+StoppedFourier.heatConstant*(t/2)^(-(1/2:ℝ)))*NativeGaussianCircleMass.mass s L); linarith) hw0
  have hn:IntegrableOn (fun t=>W t*min 1 ((1+heatFactor*t^(-(1/2:ℝ)))*M)) (Ioi 0):=by
    apply hw.mono' (by unfold W NativeBesselSchurIntegral.weight;fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw0:0≤W t:=mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
    have hc:0≤min 1 ((1+heatFactor*t^(-(1/2:ℝ)))*M):=
      le_min (by norm_num) (mul_nonneg (add_nonneg zero_le_one (mul_nonneg heatFactor_pos.le (Real.rpow_nonneg ht.le _))) (mass_pos hs hL).le)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw0 hc)]
    exact mul_le_of_le_one_right hw0 (min_le_left _ _)
  have he:(∫t in Ioi (0:ℝ),W t*cost s L t η)=
      (∫t in Ioi (0:ℝ),W t*min 1 ((1+heatFactor*t^(-(1/2:ℝ)))*M))+
        η*(Λ^(-ρ)*Real.Gamma ρ):=by
    calc
      _=∫t in Ioi (0:ℝ),W t*min 1 ((1+heatFactor*t^(-(1/2:ℝ)))*M)+W t*η:=by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [cost_eq s L t η ht]
        ring
      _=_:=by
        rw [integral_add hn (hw.mul_const η),integral_mul_const,
          NativeBesselSchurIntegral.weight_integral hρ hΛ]
        ring
  have hb:=NativeBesselSchurIntegral.bound hρ hρhalf hΛ heatFactor_pos (mass_pos hs hL)
  have hi:IntegrableOn (fun t=>W t/Real.Gamma ρ*cost s L t η) (Ioi 0):=by
    change Integrable (fun t=>W t/Real.Gamma ρ*cost s L t η) (volume.restrict (Ioi 0))
    have heq:(fun t=>W t/Real.Gamma ρ*cost s L t η)=(fun t=>(W t*cost s L t η)/Real.Gamma ρ):=by funext t;ring
    rw [heq]
    exact hwm.div_const _
  refine ⟨hi,?_⟩
  change (∫t in Ioi (0:ℝ),W t/Real.Gamma ρ*cost s L t η)≤_
  rw [show (fun t=>W t/Real.Gamma ρ*cost s L t η)=
      (fun t=>(W t*cost s L t η)/Real.Gamma ρ) by funext t;ring,integral_div,he]
  apply (div_le_iff₀ hg).mpr
  have hb':(∫t in Ioi (0:ℝ),W t*min 1 ((1+heatFactor*t^(-(1/2:ℝ)))*M))≤
      M*Λ^(-ρ)*Real.Gamma ρ+(1/ρ+1/(1/2-ρ))*(heatFactor*M)^(2*ρ):=hb
  calc
    _≤M*Λ^(-ρ)*Real.Gamma ρ+(1/ρ+1/(1/2-ρ))*(heatFactor*M)^(2*ρ)+η*(Λ^(-ρ)*Real.Gamma ρ):=by linarith
    _=bound s L Λ ρ η*Real.Gamma ρ:=by
      unfold bound
      dsimp only [M]
      simp only [div_mul_eq_mul_div]
      conv_rhs => rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hg)]
      ring
end SHE.NativeGaussianBesselCost
