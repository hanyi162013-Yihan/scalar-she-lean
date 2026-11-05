module
public import SHE.LeftFrozenHaarKernel
public import SHE.KernelEnergyCauchy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.LeftFrozenHaarConsistency
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand LeftFrozenHaarKernel
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hH:(H:ℝ)≤1)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M Holder β:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
variable(U:ℝ≥0→Ω→StateL2)(hU:Measurable (Function.uncurry U))
variable(hc:∀ω,Continuous (fun s=>U s ω))
variable {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))

include hH hβ hHolder hholder hU hc hLip in
/-- Coefficient freezing is consistent in the actual full original input
L2 norm at every terminal time. The singular heat majorant and its finite
mass are proved; no Euler or stochastic convergence is assumed. -/
theorem input_energy_tendsto (t:ℝ≥0)(ht:t≤H):
    Tendsto (fun n=>∫⁻p:ℝ≥0×Ω,ENNReal.ofReal
      (‖value ha hell hb U n (t,p)-
        kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2)
      ∂energyMeasure μ H) atTop (𝓝 0):=by
  let C:ℝ:=4*HaarIntegrandEnergy.singleConstant M
  have hM:0≤M:=hell.le.trans ((hb 0).1.trans (hb 0).2)
  have hC:0≤C:=mul_nonneg (by norm_num) (HaarIntegrandEnergy.singleConstant_nonneg hM)
  let B:ℝ≥0×Ω→ℝ≥0∞:=fun p=>ENNReal.ofReal C*
    (Ioc 0 t).indicator (fun s:ℝ≥0=>ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)))) p.1
  have hBm:Measurable B:=by
    apply measurable_const.mul
    exact ((ENNReal.continuous_ofReal.measurable.comp
      ((measurable_const.sub measurable_coe_nnreal_real).pow_const _)).indicator measurableSet_Ioc).comp measurable_fst
  have hBmass:(∫⁻p,B p ∂energyMeasure μ H)<⊤:=by
    change (∫⁻p,B p ∂(timeMeasure H).prod μ)<⊤
    rw [lintegral_prod _ hBm.aemeasurable]
    simp only [B,lintegral_const,measure_univ,mul_one]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator measurableSet_Ioc,timeMeasure_restrict ht,
      causal_rpow_mass (by norm_num:(-1:ℝ) < -(1/2:ℝ))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hmRaw:Measurable (fun p:ℝ≥0×Ω=>
      kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)):=
    (kernel_measurable ha hell hb hβ hHolder hholder).comp
      ((measurable_const.sub (measurable_coe_nnreal_real.comp measurable_fst)).prodMk hU)
  have hmVal(n:ℕ):Measurable (fun p:ℝ≥0×Ω=>value ha hell hb U n (t,p)):=
    (value_measurable ha hell hb U hβ hHolder hholder hU n).comp
      (measurable_const.prodMk measurable_id)
  have hbound(n:ℕ):∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,
      ENNReal.ofReal (‖value ha hell hb U n (t,p)-
        kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2)≤B p:=by
    have hpos:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,0<p.1:=
      Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono (fun s hs=>hs.1))
    filter_upwards [hpos] with p hp
    by_cases hpt:p.1<t
    · have ht1:(t:ℝ)≤1:=(show (t:ℝ)≤(H:ℝ) from by exact_mod_cast ht).trans hH
      have hage:0<(t:ℝ)-(p.1:ℝ):=sub_pos.mpr (by exact_mod_cast hpt)
      have hval:=value_bound ha hell hb U n t p.1 ht1 hpt p.2
      have hraw:=HaarIntegrandEnergy.kernel_small_bound hell hage
        (by linarith [p.1.2]) (coefficientField a ha ell M hell hb (U p.1 p.2))
      have htriangle:=norm_sub_le (value ha hell hb U n (t,p))
        (kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2))
      have hsquare:‖value ha hell hb U n (t,p)-
          kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2≤
          C*((t:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)):=by
        change _≤4*HaarIntegrandEnergy.singleConstant M*_
        change ‖kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2≤_ at hraw
        nlinarith [sq_nonneg (‖value ha hell hb U n (t,p)‖-
          ‖kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖),
          norm_nonneg (value ha hell hb U n (t,p)),
          norm_nonneg (kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)),
          norm_nonneg (value ha hell hb U n (t,p)-
            kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2))]
      dsimp only [B]
      rw [Set.indicator_of_mem (show p.1∈Ioc 0 t from ⟨hp,hpt.le⟩),←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal hsquare
    · have hz:kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)=0:=
        HaarKernelApproximation.kernel_zero hell
          (sub_nonpos.mpr (by exact_mod_cast le_of_not_gt hpt)) _
      simp only [value,ite_eq_right hpt,hz,sub_zero,norm_zero,
        zero_pow (by decide:2≠0),ENNReal.ofReal_zero,zero_le]
  have hlim:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,
      Tendsto (fun n=>ENNReal.ofReal (‖value ha hell hb U n (t,p)-
        kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2)) atTop (𝓝 0):=by
    filter_upwards with p
    have he:=(value_tendsto ha hell hb U hLip hc t p.1
      ((show (t:ℝ)≤(H:ℝ) from by exact_mod_cast ht).trans hH) p.2).sub_const
        (kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2))
    simpa only [sub_self,norm_zero,zero_pow (by decide:2≠0),ENNReal.ofReal_zero,Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (he.norm.pow 2)
  simpa only [lintegral_zero,Function.comp_def,Pi.sub_apply,Pi.pow_apply] using tendsto_lintegral_of_dominated_convergence
    (μ:=energyMeasure μ H) B
    (fun n=>(ENNReal.continuous_ofReal.measurable.comp
      ((((hmVal n).stronglyMeasurable.sub hmRaw.stronglyMeasurable).norm.pow 2).measurable)))
    hbound hBmass.ne hlim
end SHE.LeftFrozenHaarConsistency
