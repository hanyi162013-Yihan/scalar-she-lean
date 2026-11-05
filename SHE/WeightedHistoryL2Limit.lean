module

public import SHE.HistoryAverageEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.WeightedHistoryL2Limit
open Set Filter MeasureTheory Real Topology
variable {P Ω I:Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable (σ:Measure P) [IsFiniteMeasure σ] (μ:Measure Ω) [IsProbabilityMeasure μ]

/-- Fixed smooth finite-depth history domination upgrades genuine
history/sample L1 cutoff convergence to sample L2 AFTER history averaging.
No square of the singular history weight is required. -/
theorem averaged_limit (F:I→P×Ω→ℝ) (G:P×Ω→ℝ)
    (hF:∀i,Measurable (F i)) (hG:Measurable G)
    (W:P→ℝ) (hW:Integrable W σ) (hW0:∀p,0≤W p) {C:ℝ} (hC:0≤C)
    (hbF:∀i p ω,‖F i (p,ω)‖≤C*W p) (hbG:∀p ω,‖G (p,ω)‖≤C*W p)
    (l:Filter I)
    (hlim:Tendsto (fun i=>∫q,‖F i q-G q‖ ∂σ.prod μ) l (𝓝 0)):
    let E:=fun i ω=>∫p,F i (p,ω)-G (p,ω) ∂σ
    (∀i,Integrable (fun ω=>‖E i ω‖^2) μ) ∧
      Tendsto (fun i=>∫ω,‖E i ω‖^2 ∂μ) l (𝓝 0):=by
  intro E
  let D:ℝ:=2*C*(∫p,W p ∂σ)
  have hD:0≤D:=mul_nonneg (by positivity) (integral_nonneg hW0)
  have hb(i:I)(p:P)(ω:Ω):‖F i (p,ω)-G (p,ω)‖≤2*C*W p:=by
    exact (norm_sub_le _ _).trans ((add_le_add (hbF i p ω) (hbG p ω)).trans_eq (by ring))
  have hdiff(i:I):Integrable (fun q:P×Ω=>F i q-G q) (σ.prod μ):=
    ((hW.comp_fst μ).const_mul (2*C)).mono' ((hF i).sub hG).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q=>hb i q.1 q.2))
  have hEm(i:I):Measurable (E i):=by
    exact ((((hF i).sub hG).comp measurable_swap).stronglyMeasurable.integral_prod_right').measurable
  have hEb(i:I)(ω:Ω):‖E i ω‖≤D:=by
    have hh:=norm_integral_le_of_norm_le (hW.const_mul (2*C))
      (Filter.Eventually.of_forall (fun p=>hb i p ω))
    simpa only [integral_const_mul,D] using hh
  have hEi(i:I):Integrable (fun ω=>‖E i ω‖) μ:=
    (integrable_const D).mono' (hEm i).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
        exact hEb i ω))
  have hE2(i:I):Integrable (fun ω=>‖E i ω‖^2) μ:=
    (integrable_const (D^2)).mono' ((hEm i).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hEb i ω) 2))
  have hE1bound(i:I):(∫ω,‖E i ω‖ ∂μ)≤∫q,‖F i q-G q‖ ∂σ.prod μ:=by
    have hh:=(hdiff i).norm
    have hswap:Integrable (Function.uncurry (fun ω p=>‖F i (p,ω)-G (p,ω)‖)) (μ.prod σ):=by
      convert! hh.swap using 1
    calc
      _≤∫ω,∫p,‖F i (p,ω)-G (p,ω)‖ ∂σ ∂μ:=
        integral_mono_ae (hEi i) hh.integral_prod_right
          (Filter.Eventually.of_forall (fun ω=>norm_integral_le_integral_norm _))
      _=_:=by rw [integral_integral_swap hswap,integral_prod _ hh]
  have hE2bound(i:I):(∫ω,‖E i ω‖^2 ∂μ)≤D*(∫q,‖F i q-G q‖ ∂σ.prod μ):=by
    calc
      _≤∫ω,D*‖E i ω‖ ∂μ:=integral_mono_ae (hE2 i) ((hEi i).const_mul D)
        (Filter.Eventually.of_forall (fun ω=>by nlinarith [hEb i ω,norm_nonneg (E i ω)]))
      _=D*(∫ω,‖E i ω‖ ∂μ):=integral_const_mul _ _
      _≤_:=mul_le_mul_of_nonneg_left (hE1bound i) hD
  refine ⟨hE2,?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun i=>integral_nonneg (fun _=>sq_nonneg _)))
    (Filter.Eventually.of_forall hE2bound)
  simpa only [mul_zero] using hlim.const_mul D

end SHE.WeightedHistoryL2Limit
