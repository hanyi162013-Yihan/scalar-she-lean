module

public import SHE.JointWordHessian
public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointWordDefect
open Set MeasureTheory StoppedFourier WordRecursion GaussianItoTest CutoffWordLevel
open JointWordAnalytic PhysicalRemainderMass GaussianTaylorAverage
abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (E : (P×Ω)×ℝ→Matrix (Fin n) (Fin n) ℝ)

def integrand (p : (P×Ω)×ℝ) : ℝ :=
  (1/2:ℝ)*covarianceAction (E p) (JointWordHessian.field L Λ U V XU XV p)

def mark (p : P) (ω : Ω) : ℝ := ∫ t in R.base..L.terminal p,integrand L Λ U V XU XV E ((p,ω),t)

variable {U V XU XV E}
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
variable (hE : Measurable E)
include hU hV hXU hXV hE

theorem integrand_measurable : Measurable (integrand L Λ U V XU XV E) :=
  (JointDefectAction.action_measurable hE (JointWordHessian.measurable L Λ U V XU XV hU hV hXU hXV)).const_mul _

theorem mark_measurable : Measurable (fun p : P×Ω => mark L Λ U V XU XV E p.1 p.2) := by
  have hm : Measurable (fun p : (P×Ω)×ℝ => if R.base<p.2 ∧ p.2≤L.terminal p.1.1 then
      integrand L Λ U V XU XV E p else 0) :=
    (integrand_measurable L Λ hU hV hXU hXV hE).ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (L.terminal_measurable.comp measurable_fst.fst))) measurable_const
  have ht := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  convert ht.measurable using 1
  funext p
  rw [mark,intervalIntegral.integral_of_le (L.terminal_base p.1),← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Set.indicator,mem_Ioc]

omit hU hV hXU hXV hE in
theorem integrand_bound {M B : ℝ} (hM : 0≤M) (hB : 0≤B)
    (hH : ∀ p,‖JointWordHessian.field L Λ U V XU XV p‖≤B)
    (hbound : ∀ p ω t,t∈Ioo R.base (L.terminal p) → ∀ i j,
      |E ((p,ω),t) i j|≤2*M*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))))
    (p : P) (ω : Ω) {t : ℝ} (ht : t∈Ioo R.base (L.terminal p)) :
    ‖integrand L Λ U V XU XV E ((p,ω),t)‖≤
      ((n:ℝ)^2*M*B)*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) := by
  have hK : 0≤2*M*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (add_nonneg zero_le_one
      (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr ht.2).le _)))
  have hh := JointDefectAction.action_bound (E ((p,ω),t)) hK (hbound p ω t ht)
    (JointWordHessian.field L Λ U V XU XV ((p,ω),t))
  rw [integrand,norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ)*((n:ℝ)^2*(2*M*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))))*
        ‖JointWordHessian.field L Λ U V XU XV ((p,ω),t)‖) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ (1/2:ℝ)*((n:ℝ)^2*(2*M*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))))*B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hH _) (mul_nonneg (sq_nonneg _) hK)) (by norm_num)
    _ = _ := by ring

theorem uniform_bound {M : ℝ} (hM : 0≤M)
    (hbound : ∀ p ω t,t∈Ioo R.base (L.terminal p) → ∀ i j,
      |E ((p,ω),t) i j|≤2*M*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ)))) :
    ∃ K : ℝ,0≤K ∧ ∀ p ω,‖mark L Λ U V XU XV E p ω‖≤K ∧
      IntervalIntegrable (fun t => integrand L Λ U V XU XV E ((p,ω),t)) volume R.base (L.terminal p) := by
  obtain ⟨B,hBn,hB⟩ := JointWordHessian.uniform_bound L Λ U V XU XV
  let K : ℝ := (n:ℝ)^2*M*B
  have hKn : 0≤K := mul_nonneg (mul_nonneg (sq_nonneg _) hM) hBn
  refine ⟨K*heatMass R.horizon,mul_nonneg hKn (heatMass_nonneg (R.base_nonneg.trans R.ordered)),fun p ω => ?_⟩
  have hm := (integrand_measurable L Λ hU hV hXU hXV hE).comp
    ((measurable_const (a := (p,ω))).prodMk measurable_id)
  have hd : IntervalIntegrable (fun t => K*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ)))) volume R.base (L.terminal p) :=
    CovarianceEndpoint.endpoint_majorant_integrable K
  have hdom : ∀ᵐ t ∂volume.restrict (Ioc R.base (L.terminal p)),
      ‖integrand L Λ U V XU XV E ((p,ω),t)‖≤K*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (L.terminal p))] with t ht hne
    exact integrand_bound L Λ hM hBn hB hbound p ω ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hi : IntervalIntegrable (fun t => integrand L Λ U V XU XV E ((p,ω),t)) volume R.base (L.terminal p) := by
    apply hd.mono_fun' hm.aestronglyMeasurable
    rw [uIoc_of_le (L.terminal_base p)]
    filter_upwards [hdom] with t ht
    exact ht
  refine ⟨?_,hi⟩
  rw [ae_restrict_iff' measurableSet_Ioc] at hdom
  have hb := intervalIntegral.norm_integral_le_of_norm_le (L.terminal_base p) hdom hd
  rw [intervalIntegral.integral_const_mul,heat_majorant_mass (L.terminal_base p)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (heatMass_mono (sub_nonneg.mpr (L.terminal_base p))
    (by linarith [R.base_nonneg,L.terminal_horizon p])) hKn)

end SHE.JointWordDefect
