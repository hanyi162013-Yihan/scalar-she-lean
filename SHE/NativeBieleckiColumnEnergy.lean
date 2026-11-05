module
public import SHE.BieleckiColumnEnergy
public import SHE.NativeSignedClock
public import SHE.NonlinearHaarIntegrand
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBieleckiColumnEnergy
open MeasureTheory Set PredictableL2 CompanionHeat LowBands
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

def constant(ell M:ℝ)(L:ℝ≥0):ℝ:=CompanionHeat.picardConstant ell M L*
  NativeHeatObservation.timeScale^(1/2:ℝ)
theorem constant_nonneg{ell M:ℝ}(hM:0≤M)(L:ℝ≥0):0≤constant ell M L:=
  mul_nonneg (CompanionHeat.picardConstant_nonneg hM L)
    (Real.rpow_nonneg NativeHeatObservation.timeScale_pos.le _)

def kernel{a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)
    (τ:ℝ)(u:StateL2):RealHaarIntegrand.Columns:=
  NativeHeatObservation.kernel ell M hell (τ,NonlinearHaarIntegrand.coefficientField a ha ell M hell hb u)

theorem kernel_bound{a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)
    {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ))){τ:ℝ}(hτ:0<τ)
    (hτscale:τ≤NativeHeatObservation.timeScale)(u v:StateL2):
    ‖kernel ha hell hb τ u-kernel ha hell hb τ v‖^2≤constant ell M L*τ^(-(1/2:ℝ))*‖u-v‖^2:=by
  have hage:0<τ/NativeHeatObservation.timeScale:=div_pos hτ NativeHeatObservation.timeScale_pos
  have hage1:τ/NativeHeatObservation.timeScale≤1:=
    (div_le_one NativeHeatObservation.timeScale_pos).mpr hτscale
  change ‖NonlinearHaarIntegrand.kernel a ha ell M hell hb (τ/NativeHeatObservation.timeScale,u)-
    NonlinearHaarIntegrand.kernel a ha ell M hell hb (τ/NativeHeatObservation.timeScale,v)‖^2≤_
  rw [NonlinearHaarIntegrand.kernel_difference_norm_sq ha hell hb hage]
  have hh:=CompanionHeat.columnEnergy_bound ha hell hb (NonlinearHaarIntegrand.absBound hell hb)
    hLip hage hage1 u v
  rw [NativeSignedClock.div_neg_rpow hτ.le (1/2)] at hh
  convert hh using 1 <;> dsimp [constant] <;> ring

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
        ‖kernel ha hell hb ((t:ℝ)-(s:ℝ)) (u (s,ω))-kernel ha hell hb ((t:ℝ)-(s:ℝ)) (v (s,ω))‖^2))
      ∂μ ∂timeMeasure t ∂timeMeasure h)≤
      ENNReal.ofReal (constant ell M L*BieleckiKernel.mass γ)*
        (∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2)
          ∂μ ∂timeMeasure h):=by
  let F:=fun s:ℝ≥0=>∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2) ∂μ
  let C:=ENNReal.ofReal (constant ell M L)
  have hC:0≤constant ell M L:=constant_nonneg ((abs_nonneg (a 0)).trans (hM 0)) L
  have hFm:Measurable F:=by
    have hm:Measurable (fun p:ℝ≥0×Ω=>ENNReal.ofReal
        (Real.exp (-2*γ*(p.1:ℝ))*‖u p-v p‖^2)):=
      ENNReal.continuous_ofReal.measurable.comp
        ((((measurable_coe_nnreal_real.comp measurable_fst).const_mul (-2*γ)).exp).mul ((hu.sub hv).norm.pow_const 2))
    exact hm.lintegral_prod_right'
  have hbnd:(∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
        ‖kernel ha hell hb ((t:ℝ)-(s:ℝ)) (u (s,ω))-kernel ha hell hb ((t:ℝ)-(s:ℝ)) (v (s,ω))‖^2))
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
    have hScale:1≤NativeHeatObservation.timeScale:=by
      dsimp [NativeHeatObservation.timeScale]
      nlinarith only [Real.two_le_pi]
    have hcol:=kernel_bound ha hell hb hLip hτ ((hτh.trans hh).trans hScale) (u (s,ω)) (v (s,ω))
    have h0:=sq_nonneg ‖kernel ha hell hb ((t:ℝ)-(s:ℝ)) (u (s,ω))-kernel ha hell hb ((t:ℝ)-(s:ℝ)) (v (s,ω))‖
    have he:Real.exp (-2*γ*(t:ℝ))=
        Real.exp (-2*γ*((t:ℝ)-(s:ℝ)))*Real.exp (-2*γ*(s:ℝ)):=by
      rw [←Real.exp_add]
      congr 1
      ring
    have hc':Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*‖kernel ha hell hb ((t:ℝ)-(s:ℝ)) (u (s,ω))-kernel ha hell hb ((t:ℝ)-(s:ℝ)) (v (s,ω))‖^2≤
        constant ell M L*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ))*‖u (s,ω)-v (s,ω)‖^2:=
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
      mul_le_mul_right (BieleckiColumnEnergy.causal_energy h hγ F hFm) C
    _=_:=by
      dsimp only [C,F]
      rw [←mul_assoc,←ENNReal.ofReal_mul hC]

end SHE.NativeBieleckiColumnEnergy
