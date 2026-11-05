module
public import SHE.BieleckiKernel
public import SHE.CompanionEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.BieleckiColumnEnergy
open MeasureTheory Set PredictableL2 CompanionHeat LowBands
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

theorem causal_energy (h:ℝ≥0){γ:ℝ}(hγ:0<γ)(F:ℝ≥0→ℝ≥0∞)(hF:Measurable F):
    (∫⁻t,∫⁻s,BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))*F s
      ∂timeMeasure t ∂timeMeasure h)≤
      ENNReal.ofReal (BieleckiKernel.mass γ)*(∫⁻s,F s ∂timeMeasure h):=by
  have he:(∫⁻t,∫⁻s,BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))*F s
      ∂timeMeasure t ∂timeMeasure h)=
      ∫⁻t in Ioc (0:ℝ) h,∫⁻s in Ioc (0:ℝ) t,
        BieleckiKernel.kernel h γ (t-s)*F s.toNNReal:=by
    rw [timeMeasure_lintegral]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [timeMeasure_lintegral,Real.coe_toNNReal _ ht.1.le]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.coe_toNNReal _ hs.1.le]
  rw [he,timeMeasure_lintegral]
  exact BieleckiKernel.causal_energy h hγ _ (hF.comp measurable_real_toNNReal)

/-- The literal nonlinear common-Haar column energy contracts in a
Bielecki norm on any prescribed h≤1; no small horizon depending on the
coefficient Lipschitz constant is required. -/
theorem expected_energy {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[SFinite μ]
    {a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}(hell:0<ell)
    (hb:∀z,ell≤a z ∧ a z≤M)(hM:∀z,|a z|≤M){L:ℝ≥0}
    (hLip:LipschitzWith L (fun z=>(a z:ℂ)))(h:ℝ≥0)(hh:(h:ℝ)≤1)
    (u v:ℝ≥0×Ω→StateL2)(hu:Measurable u)(hv:Measurable v)
    {Λ γ:ℝ}(hΛ:0≤Λ)(hγ:0<γ):
    (∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
        columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ))))
      ∂μ ∂timeMeasure t ∂timeMeasure h)≤
      ENNReal.ofReal (picardConstant ell M L*BieleckiKernel.mass γ)*
        (∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2)
          ∂μ ∂timeMeasure h):=by
  let F:=fun s:ℝ≥0=>∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2) ∂μ
  let C:=ENNReal.ofReal (picardConstant ell M L)
  have hC:0≤picardConstant ell M L:=picardConstant_nonneg ((abs_nonneg (a 0)).trans (hM 0)) L
  have hFm:Measurable F:=by
    have hm:Measurable (fun p:ℝ≥0×Ω=>ENNReal.ofReal
        (Real.exp (-2*γ*(p.1:ℝ))*‖u p-v p‖^2)):=
      ENNReal.continuous_ofReal.measurable.comp
        ((((measurable_coe_nnreal_real.comp measurable_fst).const_mul (-2*γ)).exp).mul ((hu.sub hv).norm.pow_const 2))
    exact hm.lintegral_prod_right'
  have hbnd:(∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
        columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ))))
      ∂μ ∂timeMeasure t ∂timeMeasure h)≤
      ∫⁻t,∫⁻s,C*BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))*F s
        ∂timeMeasure t ∂timeMeasure h:=by
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem h] with t ht
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
    have hst':s<t:=lt_of_le_of_ne hs.2 hst
    have hτ:0<(t:ℝ)-(s:ℝ):=sub_pos.mpr (by exact_mod_cast hst')
    have hτh:(t:ℝ)-(s:ℝ)≤h:=by
      have htr:(t:ℝ)≤h:=by exact_mod_cast ht.2
      linarith [s.2]
    have hk:BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))=
        ENNReal.ofReal (Real.exp (-2*γ*((t:ℝ)-(s:ℝ)))*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ))):=
      Set.indicator_of_mem (show (t:ℝ)-(s:ℝ)∈Ioc (0:ℝ) (h:ℝ) from ⟨hτ,hτh⟩) _
    have hkfin:BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))≠∞:=by rw [hk];exact ENNReal.ofReal_ne_top
    rw [←lintegral_const_mul' (C*BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))) _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hkfin)]
    apply lintegral_mono
    intro ω
    dsimp only [C]
    rw [hk,←ENNReal.ofReal_mul hC]
    rw [←ENNReal.ofReal_mul (mul_nonneg hC (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    have hd:Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))≤1:=Real.exp_le_one_iff.mpr (by nlinarith)
    have hcol:=columnEnergy_bound ha hell hb hM hLip hτ (hτh.trans hh) (u (s,ω)) (v (s,ω))
    have h0:=columnEnergy_nonneg a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ))
    have he:Real.exp (-2*γ*(t:ℝ))=
        Real.exp (-2*γ*((t:ℝ)-(s:ℝ)))*Real.exp (-2*γ*(s:ℝ)):=by
      rw [←Real.exp_add]
      congr 1
      ring
    have hc':Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ))≤
        picardConstant ell M L*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ))*‖u (s,ω)-v (s,ω)‖^2:=
      (mul_le_of_le_one_left h0 hd).trans hcol
    have hmul:=mul_le_mul_of_nonneg_left hc' (Real.exp_pos (-2*γ*(t:ℝ))).le
    rw [he] at hmul
    rw [he]
    convert hmul using 1 <;> ring
  calc
    _≤_:=hbnd
    _=C*(∫⁻t,∫⁻s,BieleckiKernel.kernel h γ ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure h):=by
      simp_rw [mul_assoc,lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
    _≤C*(ENNReal.ofReal (BieleckiKernel.mass γ)*(∫⁻s,F s ∂timeMeasure h)):=
      mul_le_mul_right (causal_energy h hγ F hFm) C
    _=_:=by
      dsimp only [C,F]
      rw [←mul_assoc,←ENNReal.ofReal_mul hC]

end SHE.BieleckiColumnEnergy
