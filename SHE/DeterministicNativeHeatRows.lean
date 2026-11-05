module

public import SHE.FullHorizonEndpointVersion
public import SHE.GaussianDeterministicRows

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.DeterministicNativeHeatRows
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open NativeObservationCovariance NativeObservationEndpoint NativeObservationProcess
open scoped NNReal ENNReal
local instance rowSigma : MeasurableSpace RealHaarInput := borel _
local instance rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fieldSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance fieldBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance fieldSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H b : ℝ≥0) {ell M T:ℝ} (hell:0<ell)(hM:0≤M)
variable (f:ℝ≥0→EllipticField ell M)(hf:Measurable f)(hT:(b:ℝ)≤T)(x:HeatCircle)

abbrev field : ℝ≥0×Ω→EllipticField ell M := fun p=>f p.1

include hf in
theorem field_predictable : StronglyMeasurable[𝓕.predictable] (field (Ω:=Ω) f) :=
  (hf.comp (PredictableClock.time_measurable 𝓕)).stronglyMeasurable

def raw (t:ℝ):RealHaarInput:=
  if (t.toNNReal:ℝ)<(b:ℝ) then
    if (t.toNNReal:ℝ)<T then row hell (f t.toNNReal) T (t.toNNReal:ℝ) x else 0
  else 0

include 𝓕 μ hf in
theorem raw_measurable : Measurable (raw (T:=T) b hell f x) := by
  let ω0:Ω:=Classical.choice (nonempty_of_isProbabilityMeasure μ)
  have hm := (FullHorizonEndpoint.raw_predictable (T:=T) 𝓕 b hell (field (Ω:=Ω) f)
    (field_predictable 𝓕 f hf) x).mono (predictable_le_product 𝓕)
  have hh := hm.measurable.comp (continuous_real_toNNReal.measurable.prodMk (measurable_const (a:=ω0)))
  convert! hh using 1

include 𝓕 μ hf hM hT in
theorem square_integrable (v:ℝ≥0)(hvb:v≤b):
    IntervalIntegrable (fun t=>‖raw (T:=T) b hell f x t‖^2) volume (v:ℝ) b := by
  apply (CovarianceEndpoint.endpoint_majorant_integrable (q:=(v:ℝ)) (s:=(b:ℝ)) M).mono_fun'
  · exact ((raw_measurable (T:=T) 𝓕 μ b hell f hf x).norm.pow_const 2).aestronglyMeasurable
  · rw [uIoc_of_le (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    have ht0:0≤t:=v.2.trans ht.1.le
    have htb:t<(b:ℝ):=lt_of_le_of_ne ht.2 hne
    have htT:t<T:=htb.trans_le hT
    simp only [raw,Real.coe_toNNReal t ht0,ite_eq_left htb,ite_eq_left htT,
      Real.norm_of_nonneg (sq_nonneg _)]
    have hh:=row_norm_sq_bound hell (f t.toNNReal)
      (show t+T-(b:ℝ)<T by linarith) (show t≤t+T-(b:ℝ) by linarith) x
    convert! hh using 1 <;> ring

def process (hbH:b≤H):Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b hell hM (field (Ω:=Ω) f)
    (field_predictable 𝓕 f hf) hT x hbH

theorem process_ae (hbH:b≤H):process 𝓕 μ H b hell hM f hf hT x hbH=ᵐ[energyMeasure μ H]
    fun p=>raw (T:=T) b hell f x (p.1:ℝ) := by
  filter_upwards [FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM (field (Ω:=Ω) f)
    (field_predictable 𝓕 f hf) hT x hbH] with p hp
  change FullHorizonEndpoint.process 𝓕 μ H b hell hM (field (Ω:=Ω) f)
    (field_predictable 𝓕 f hf) hT x hbH p=_
  rw [hp]
  simp only [raw,FullHorizonEndpoint.raw,field,indicator_apply,StoppedItoInputs.before,
    mem_ofPred_eq,fullIntegrand,Real.toNNReal_coe]

theorem bound (hbH:b≤H)(hb1:(b:ℝ)≤1):
    SingularInputBounds.Bound 𝓕 μ H b (M*(1+heatConstant)) (process 𝓕 μ H b hell hM f hf hT x hbH):=
  FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hell hM (field (Ω:=Ω) f)
    (field_predictable 𝓕 f hf) hT x hbH hb1

end SHE.DeterministicNativeHeatRows
