module
public import SHE.PredictableEnergyCap
public import SHE.PredictablePathEnergy
public import SHE.NativeControlMass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.AdaptedRateLocalization
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(f:ℝ≥0→Ω→ℝ) (ha:StronglyAdapted 𝓕 f) (hc:∀ω,Continuous (fun t=>f t ω))
variable(hf:∀t ω,0≤f t ω)
def accumulated(t:ℝ≥0) (ω:Ω):ℝ:=∫s in (0:ℝ)..(t:ℝ),f s.toNNReal ω

include ha hc in
theorem adapted:StronglyAdapted 𝓕 (accumulated f):=by
  intro t
  letI:MeasurableSpace Ω:=𝓕 t
  let F:ℝ→Ω→ℝ:=fun r ω=>f (min r.toNNReal t) ω
  have hFc:∀ω,Continuous (fun r=>F r ω):=fun ω=>(hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hFm:∀r,StronglyMeasurable (F r):=fun r=>(ha _).mono (𝓕.mono (min_le_right _ _))
  have hj:=stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hFc hFm
  have hi:StronglyMeasurable (fun ω=>∫r,F r ω ∂volume.restrict (Ioc (0:ℝ) (t:ℝ))):=hj.integral_prod_left
  convert! hi using 1
  funext ω
  have he:=intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ))
    (f:=fun s:ℝ=>f s.toNNReal ω) t.2
  apply he.trans
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have ht:r.toNNReal≤t:=by exact_mod_cast (show (r.toNNReal:ℝ)≤(t:ℝ) by rw [Real.coe_toNNReal _ hr.1.le];exact hr.2)
  simp only [F,min_eq_left ht]

include hc in
theorem continuous(ω:Ω):Continuous (fun t=>accumulated f t ω):=
  (CumulativeEnergyCap.continuous_cumulative ((hc ω).comp continuous_real_toNNReal)).comp continuous_subtype_val

include hc hf in
theorem monotone(ω:Ω):Monotone (fun t=>accumulated f t ω):=by
  intro s t hst
  exact CumulativeEnergyCap.monotone_cumulative ((hc ω).comp continuous_real_toNNReal)
    (fun _=>hf _ _) s.2 t.2 (by exact_mod_cast hst)

def cut(U:ℝ≥0→Ω→E) (p:ℝ≥0×Ω):E:=if accumulated f p.1 p.2<1 then U p.1 p.2 else 0

include ha hc in
theorem predictable(U:ℝ≥0→Ω→E) (hU:StronglyMeasurable[𝓕.predictable] (Function.uncurry U)):
    StronglyMeasurable[𝓕.predictable] (cut f U):=by
  have hA:=ContinuousPredictable.stronglyMeasurable 𝓕 (accumulated f)
    (adapted 𝓕 f ha hc) (continuous f hc)
  exact hU.piecewise (measurableSet_lt hA.measurable measurable_const) stronglyMeasurable_const

include ha hc hf in
theorem exists_input(U:ℝ≥0→Ω→E) (hU:StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
    (hUc:∀ω,Continuous (fun t=>U t ω)) (C:ℝ) (hC:0≤C) (hbound:∀t ω,‖U t ω‖^2≤C*f t ω):
    ∃u:Process (E:=E) 𝓕 μ H,u=ᵐ[energyMeasure μ H] cut f U ∧ ‖u‖^2≤C:=by
  have hp:=predictable 𝓕 f ha hc U hU
  have hi(ω:Ω):Integrable (fun t=>‖cut f U (t,ω)‖^2) (timeMeasure H):=by
    have hm:Measurable (fun t:ℝ≥0=>‖cut f U (t,ω)‖^2):=
      (((hp.mono (predictable_le_product 𝓕)).measurable.comp
        (measurable_id.prodMk (measurable_const (a:=ω)))).norm.pow_const 2)
    apply (NativeControlMass.continuous_integrable H ((hUc ω).norm.pow 2)).mono'
      hm.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    unfold cut
    split_ifs <;> simp [sq_nonneg]
  have hb(ω:Ω):(∫t,‖cut f U (t,ω)‖^2 ∂timeMeasure H)≤C:=by
    let g:ℝ→ℝ:=fun r=>f r.toNNReal ω
    have hg:=CumulativeEnergyCap.energy_le_one ((hc ω).comp continuous_real_toNNReal)
      (fun _=>hf _ _) H.2
    have he:Integrable (fun t:ℝ≥0=>CumulativeEnergyCap.clipped g t) (timeMeasure H):=by
      simpa only [Function.comp_def,Real.toNNReal_coe] using
        ((timeMeasurePreserving H).integrable_comp_emb nonnegative_coe_measurableEmbedding).mpr hg.1
    have hh:(∫t:ℝ≥0,CumulativeEnergyCap.clipped g t ∂timeMeasure H)≤1:=by
      rw [timeMeasure_integral]
      have heq:(∫t:ℝ in Ioc 0 (H:ℝ),CumulativeEnergyCap.clipped g (t.toNNReal:ℝ))=
          ∫t:ℝ in Ioc 0 (H:ℝ),CumulativeEnergyCap.clipped g t:=by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change CumulativeEnergyCap.clipped g (t.toNNReal:ℝ)=CumulativeEnergyCap.clipped g t
        exact congrArg (CumulativeEnergyCap.clipped g) (Real.coe_toNNReal _ ht.1.le)
      exact heq.trans_le hg.2
    calc
      _≤∫t:ℝ≥0,C*CumulativeEnergyCap.clipped g t ∂timeMeasure H:=by
        apply integral_mono (hi ω) (he.const_mul C)
        intro t
        unfold cut CumulativeEnergyCap.clipped CumulativeEnergyCap.cumulative accumulated
        dsimp only [g,Real.toNNReal_coe]
        split_ifs
        · simpa only [Real.toNNReal_coe] using hbound t ω
        · simp only [norm_zero,zero_pow (by decide:2≠0),mul_zero,le_refl]
      _=C*(∫t:ℝ≥0,CumulativeEnergyCap.clipped g t ∂timeMeasure H):=integral_const_mul _ _
      _≤C:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hC
  exact PredictablePathEnergy.exists_input 𝓕 μ H (cut f U) hp C hi hb
end SHE.AdaptedRateLocalization
