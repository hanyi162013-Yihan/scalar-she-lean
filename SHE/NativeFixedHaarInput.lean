module

public import SHE.FixedTargetKernelBound
public import SHE.NativeStoppedBracket
public import SHE.FixedHaarIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.NativeFixedHaarInput
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation
open scoped NNReal ENNReal
local instance nativeFixedHaarInput_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFixedHaarInput_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFixedHaarInput_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFixedHaarInput_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFixedHaarInput_sigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFixedHaarInput_borel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeFixedHaarInput_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFixedHaarInput_realSecond : SecondCountableTopology DyadicApproximation.RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

def raw (t : ℝ≥0) (p : ℝ≥0×Ω) : RealHaarIntegrand.Columns:=
  NativeHeatObservation.kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)

include hf in
theorem raw_predictable (t : ℝ≥0) : StronglyMeasurable[𝓕.predictable] (raw hell f t) :=
  ((NativeObservationProcess.kernel_measurable ell M hell).comp
    ((measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).prodMk hf.measurable)).stronglyMeasurable

include hM in
/-- Every native deterministic target has finite genuine common-Haar
Hilbert energy on the ORIGINAL full horizon, including target<H. -/
theorem energy (t : ℝ≥0) (htH : t≤H) (ht1 : (t:ℝ)≤1) :
    (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖raw hell f t (s,ω)‖^2) ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal (FixedTargetKernelBound.constant M*(2*(t:ℝ)^(1/2:ℝ))) := by
  let C:=FixedTargetKernelBound.constant M
  have hC : 0≤C:=FixedTargetKernelBound.constant_nonneg hM
  calc
    _≤∫⁻ s,ENNReal.ofReal C*(Iio t).indicator
        (fun s : ℝ≥0=>ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)))) s ∂timeMeasure H := by
      apply lintegral_mono
      intro s
      have hp (ω : Ω) : ENNReal.ofReal (‖raw hell f t (s,ω)‖^2)≤
          ENNReal.ofReal C*(Iio t).indicator
            (fun s : ℝ≥0=>ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)))) s := by
        by_cases hst : s<t
        · rw [indicator_of_mem (show s∈Iio t from hst),←ENNReal.ofReal_mul hC]
          apply ENNReal.ofReal_le_ofReal
          exact FixedTargetKernelBound.kernel_bound hell
            (sub_pos.mpr (by exact_mod_cast hst)) (by linarith [s.2]) (f (s,ω))
        · rw [indicator_of_notMem (show s∉Iio t from hst)]
          simp only [mul_zero]
          rw [raw,NativeHeatObservation.kernel_zero hell
            (sub_nonpos.mpr (by exact_mod_cast le_of_not_gt hst)),norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),ENNReal.ofReal_zero]
      simpa only [lintegral_const,measure_univ,mul_one] using lintegral_mono (μ:=μ) hp
    _=_:=by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Iio,
        NativeStoppedBracket.timeMeasure_before htH,causal_rpow_mass (by norm_num : (-1:ℝ) < -(1/2:ℝ))]
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      rw [←ENNReal.ofReal_mul hC]
      congr 1
      ring

include hM hf in
theorem memLp (t : ℝ≥0) (htH : t≤H) (ht1 : (t:ℝ)≤1) :
    @MemLp _ _ 𝓕.predictable _ _ (raw hell f t) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  have hs:=raw_predictable 𝓕 hell f hf t
  have ha:=hs.mono (predictable_le_product 𝓕)
  have hm : Measurable (fun p=>ENNReal.ofReal (‖raw hell f t p‖^2)):=ha.measurable.norm.pow_const 2 |>.ennreal_ofReal
  have hE : (∫⁻ p,ENNReal.ofReal (‖raw hell f t p‖^2) ∂energyMeasure μ H)<∞:=by
    rw [energyMeasure,lintegral_prod _ hm.aemeasurable]
    exact (energy μ H hell hM f t htH ht1).trans_lt ENNReal.ofReal_lt_top
  have hi : Integrable (fun p=>‖raw hell f t p‖^2) (energyMeasure μ H):=
    ⟨(ha.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))).mpr hE⟩
  have hmem:=(memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr hi
  exact (le_of_eq (eLpNorm_trim (predictable_le_product 𝓕) hs)).trans_lt hmem

def input (t : ℝ≥0) (htH : t≤H) (ht1 : (t:ℝ)≤1) :
    Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  (memLp 𝓕 μ H hell hM f hf t htH ht1).toLp (raw hell f t)

theorem input_ae (t : ℝ≥0) (htH : t≤H) (ht1 : (t:ℝ)≤1) :
    input 𝓕 μ H hell hM f hf t htH ht1=ᵐ[energyMeasure μ H] raw hell f t :=
  ae_eq_of_ae_eq_trim (memLp 𝓕 μ H hell hM f hf t htH ht1).coeFn_toLp

theorem singular_cap (t : ℝ≥0) (htH : t≤H) (ht1 : (t:ℝ)≤1) :
    ∀ᵐ p∂energyMeasure μ H,p.1≤t→‖input 𝓕 μ H hell hM f hf t htH ht1 p‖^2≤
      FixedTargetKernelBound.constant M*((t:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) := by
  filter_upwards [input_ae 𝓕 μ H hell hM f hf t htH ht1] with p hp hpt
  rw [hp]
  rcases lt_or_eq_of_le hpt with hlt|rfl
  · exact FixedTargetKernelBound.kernel_bound hell (sub_pos.mpr (by exact_mod_cast hlt))
      (by linarith [p.1.2]) (f p)
  · rw [raw,sub_self,NativeHeatObservation.kernel_zero hell le_rfl,norm_zero]
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),Real.zero_rpow (by norm_num : -(1/2:ℝ)≠0),mul_zero,le_refl]

end SHE.NativeFixedHaarInput
