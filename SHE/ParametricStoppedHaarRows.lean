module
public import SHE.JointFrozenReferenceFields
public import SHE.NativePhysicalRowFields
public import SHE.NativeFrozenSpatialObservation
public import SHE.NativePastBracket
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ParametricStoppedHaarRows
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeObservationCovariance
open scoped NNReal ENNReal
local instance parametricStoppedHaarRows_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance parametricStoppedHaarRows_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance parametricStoppedHaarRows_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance parametricStoppedHaarRows_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance parametricStoppedHaarRows_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance parametricStoppedHaarRows_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable (v b q:X→ℝ≥0)(center:X→HeatCircle)
variable (f:X×(ℝ≥0×Ω)→EllipticField ell M)
variable (hf:StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)] f)

def raw (z:X×(ℝ≥0×Ω)):RealHaarInput:=
  if v z.1<z.2.1∧z.2.1<q z.1 then row hell (f z) (b z.1) z.2.1 (center z.1) else 0

include hf in
theorem raw_predictable (hv:Measurable v)(hb:Measurable b)(hq:Measurable q)(hc:Measurable center):
    StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)]
      (raw hell v b q center f):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have ht:Measurable (fun z:X×(ℝ≥0×Ω)=>z.2.1):=
    (PredictableClock.time_measurable 𝓕).comp measurable_snd
  have hr:=NativePhysicalRowFields.row_measurable_comp hell hf.measurable
    (NNReal.continuous_coe.measurable.comp (hb.comp measurable_fst))
    (NNReal.continuous_coe.measurable.comp ht) (hc.comp measurable_fst)
  exact (hr.ite ((measurableSet_lt (hv.comp measurable_fst) ht).inter
    (measurableSet_lt ht (hq.comp measurable_fst))) measurable_const).stronglyMeasurable

include hf in
theorem field_section (x:X):StronglyMeasurable[𝓕.predictable] (fun p=>f (x,p)):=
  hf.comp_measurable (measurable_const.prodMk measurable_id)

variable (hqb:∀x,q x≤b x)(hbH:∀x,b x≤H)
/-- Every parameter uses the SAME original full-H predictable space. -/
def process (x:X):Process (E:=RealHaarInput) 𝓕 μ H:=
  NativeFrozenSpatialObservation.row 𝓕 μ H (b x) (q x) (v x) hell hM (fun p=>f (x,p))
    (field_section 𝓕 f hf x) (hbH x) (hqb x) (center x) 0

theorem process_ae (x:X):process 𝓕 μ H hell hM v b q center f hf hqb hbH x=ᵐ[energyMeasure μ H]
    (fun p=>raw hell v b q center f (x,p)):=by
  have hqT:(q x:ℝ)≤(b x:ℝ)+max (0:ℝ) 0:=by simpa using NNReal.coe_le_coe.mpr (hqb x)
  filter_upwards [PastItoInputs.post_ae 𝓕 μ H (v x)
    (FullHorizonEndpoint.process 𝓕 μ H (q x) hell hM (fun p=>f (x,p)) (field_section 𝓕 f hf x)
      hqT (center x) ((hqb x).trans (hbH x))),
    FullHorizonEndpoint.process_ae 𝓕 μ H (q x) hell hM (fun p=>f (x,p)) (field_section 𝓕 f hf x)
      hqT (center x) ((hqb x).trans (hbH x))] with p hp hr
  change process 𝓕 μ H hell hM v b q center f hf hqb hbH x p=_ at hp
  rw [hp]
  by_cases hv:v x<p.1
  · rw [if_pos hv,hr]
    by_cases hq:p.1<q x
    · have ht:(p.1:ℝ)<(b x:ℝ)+max (0:ℝ) 0:=by
        exact (NNReal.coe_lt_coe.mpr hq).trans_le hqT
      have ht':(p.1:ℝ)<(b x:ℝ):=by simpa only [max_self,add_zero] using ht
      simp only [FullHorizonEndpoint.raw,NativeObservationEndpoint.fullIntegrand,
        Set.indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (q x:ℝ) by exact_mod_cast hq),
        max_self,add_zero]
      rw [if_pos ht',raw,if_pos (show v x<p.1∧p.1<q x from ⟨hv,hq⟩)]
    · rw [FullHorizonEndpoint.raw,Set.indicator_of_notMem
        (show p∉StoppedItoInputs.before (Ω:=Ω) (q x:ℝ) by exact_mod_cast hq),raw,
        if_neg (fun hh=>hq hh.2)]
  · rw [if_neg hv,raw,if_neg (fun hh=>hv hh.1)]

include hqb hM in
/-- A uniform native heat cap valid even when the partial stop equals
the original target. Coefficients may depend on every parameter and
on the original source sample. -/
theorem raw_norm_sq (x:X)(p:ℝ≥0×Ω):
    ‖raw hell v b q center f (x,p)‖^2≤
      (Iio (q x)).indicator (fun s:ℝ≥0=>M*(1+heatConstant*((q x:ℝ)-(s:ℝ))^(-(1/2:ℝ)))) p.1:=by
  by_cases hs:v x<p.1∧p.1<q x
  · rw [raw,if_pos hs,Set.indicator_of_mem (show p.1∈Iio (q x) from hs.2)]
    have ht:(p.1:ℝ)+(b x:ℝ)-(q x:ℝ)<b x:=by
      have hh:(p.1:ℝ)<q x:=by exact_mod_cast hs.2
      linarith
    have hr:(p.1:ℝ)≤(p.1:ℝ)+(b x:ℝ)-(q x:ℝ):=by
      have hh:=NNReal.coe_le_coe.mpr (hqb x)
      linarith
    have hh:=NativeObservationProcess.row_norm_sq_bound hell (f (x,p)) ht hr (center x)
    simpa only [show (b x:ℝ)-((p.1:ℝ)+(b x:ℝ)-(q x:ℝ))=(q x:ℝ)-(p.1:ℝ) by ring] using hh
  · rw [raw,if_neg hs,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0)]
    exact Set.indicator_nonneg (fun s hs=>mul_nonneg hM
      (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le
        (Real.rpow_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hs.le)) _)))) _
end SHE.ParametricStoppedHaarRows
