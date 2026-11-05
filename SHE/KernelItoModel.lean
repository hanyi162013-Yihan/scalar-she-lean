module

public import SHE.PredictableItoEnergy
public import SHE.KernelEnergyMeasure
public import SHE.KernelEnergyCauchy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.KernelItoLimit
open MeasureTheory Set Filter PredictableL2 ApproximationCells HaarKernelL2Approximation
open scoped NNReal ENNReal Topology

variable {Ω C E A : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ] {h : ℝ≥0}

/-- Deterministic hypotheses for constructing a parameterized stochastic
convolution by finite predictable cells. An actual application must
construct these kernels, prove their energy and convergence, and identify
each stopped input. No stochastic word estimate is part of this object. -/
structure Model (A C : Type*) [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [MeasurableSpace C] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0) where
  raw : A → ℝ≥0 × (ℝ≥0 × Ω) → C
  approx : A → ℕ → ℝ≥0 × (ℝ≥0 × Ω) → C
  raw_measurable : ∀ a,Measurable (raw a)
  approx_measurable : ∀ a n,Measurable (approx a n)
  raw_energy_finite : ∀ a,(∫⁻ p,ENNReal.ofReal (‖raw a p‖^2) ∂measure μ h) < ∞
  approx_tendsto : ∀ a,∀ᵐ p ∂measure μ h,Tendsto (fun n => approx a n p) atTop (𝓝 (raw a p))
  approx_norm_le : ∀ a n,∀ᵐ p ∂measure μ h,‖approx a n p‖ ≤ ‖raw a p‖
  input : A → ℕ → ℕ → Process (E := C) 𝓕 μ h
  input_stopped : ∀ a n k,∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → input a n k p=0
  input_at : ∀ a n t,0 < t → t ≤ h →
    input a n (index n t) =ᵐ[energyMeasure μ h] (fun p => approx a n (t,p))

variable (K : Model A C 𝓕 μ h)
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)

def output (a : A) (n : ℕ) : Process (E := E) 𝓕 μ h :=
  PredictableItoCells.output I n (K.input a n) (K.input_stopped a n)

theorem output_pair_energy (a b : A) (n m : ℕ) :
    ENNReal.ofReal (‖output K I a n-output K I b m‖^2)=
      ∫⁻ p,ENNReal.ofReal (‖K.approx a n p-K.approx b m p‖^2) ∂measure μ h := by
  have hm : Measurable (fun p => ENNReal.ofReal (‖K.approx a n p-K.approx b m p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((K.approx_measurable a n).sub (K.approx_measurable b m)).norm.pow_const 2)
  rw [output,output,PredictableItoCells.output_difference_energy,triple_lintegral μ h hm]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (K.input_at a n t ht.1 ht.2),
    Measure.ae_ae_of_ae_prod (K.input_at b m t ht.1 ht.2)] with s hs hs'
  apply lintegral_congr_ae
  filter_upwards [hs,hs'] with ω hω hω'
  rw [hω,hω']

def error (a : A) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p,ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2) ∂measure μ h

omit [SFinite μ] in
theorem error_tendsto (a : A) : Tendsto (error K a) atTop (𝓝 0) := by
  have hr : Measurable (fun p => ENNReal.ofReal (‖K.raw a p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((K.raw_measurable a).norm.pow_const 2)
  have hf : (∫⁻ p,ENNReal.ofReal 4*ENNReal.ofReal (‖K.raw a p‖^2) ∂measure μ h) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (K.raw_energy_finite a).ne
  have ht := tendsto_lintegral_of_dominated_convergence (μ := measure μ h)
    (fun p => ENNReal.ofReal 4*ENNReal.ofReal (‖K.raw a p‖^2))
    (F := fun n p => ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2)) (f := fun _ => 0)
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (((K.approx_measurable a n).sub (K.raw_measurable a)).norm.pow_const 2))
    (fun n => (K.approx_norm_le a n).mono (fun p hp => by
      have htri := norm_sub_le (K.approx a n p) (K.raw a p)
      have hs : ‖K.approx a n p-K.raw a p‖^2 ≤ 4*‖K.raw a p‖^2 := by
        nlinarith [norm_nonneg (K.approx a n p-K.raw a p),norm_nonneg (K.raw a p)]
      change ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2) ≤
        ENNReal.ofReal 4*ENNReal.ofReal (‖K.raw a p‖^2)
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      exact ENNReal.ofReal_le_ofReal hs)) hf
    ((K.approx_tendsto a).mono (fun p hp => by
      have hs : Tendsto (fun n => K.approx a n p-K.raw a p) atTop (𝓝 (0:C)) := by
        simpa only [sub_self] using hp.sub (tendsto_const_nhds (x := K.raw a p))
      have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.norm.pow 2)
      change Tendsto (fun n => ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2))
        atTop (𝓝 (ENNReal.ofReal (‖(0:C)‖^2))) at hn
      simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero] using hn))
  change Tendsto (fun n => ∫⁻ p,ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2) ∂measure μ h) atTop (𝓝 0)
  simpa only [lintegral_zero] using ht

theorem output_difference_bound (a : A) (n m : ℕ) :
    ENNReal.ofReal (‖output K I a n-output K I a m‖^2) ≤ 2*error K a n+2*error K a m := by
  have he (n : ℕ) : Measurable (fun p => ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((K.approx_measurable a n).sub (K.raw_measurable a)).norm.pow_const 2)
  rw [output_pair_energy]
  calc
    _ ≤ ∫⁻ p,(2:ℝ≥0∞)*ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2)+
        2*ENNReal.ofReal (‖K.approx a m p-K.raw a p‖^2) ∂measure μ h := by
      apply lintegral_mono
      intro p
      have htri : ‖K.approx a n p-K.approx a m p‖ ≤
          ‖K.approx a n p-K.raw a p‖+‖K.approx a m p-K.raw a p‖ := by
        simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub
          (K.approx a n p) (K.raw a p) (K.approx a m p)
      have hs : ‖K.approx a n p-K.approx a m p‖^2 ≤
          2*‖K.approx a n p-K.raw a p‖^2+2*‖K.approx a m p-K.raw a p‖^2 := by
        nlinarith [norm_nonneg (K.approx a n p-K.approx a m p),norm_nonneg (K.approx a n p-K.raw a p),
          norm_nonneg (K.approx a m p-K.raw a p),sq_nonneg
          (‖K.approx a n p-K.raw a p‖-‖K.approx a m p-K.raw a p‖)]
      have hb := ENNReal.ofReal_le_ofReal hs
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)] at hb
      simpa only [ENNReal.ofReal_ofNat] using hb
    _ = _ := by
      have h2n : Measurable (fun p => (2:ℝ≥0∞)*ENNReal.ofReal (‖K.approx a n p-K.raw a p‖^2)) :=
        measurable_const.mul (he n)
      rw [lintegral_add_left h2n,lintegral_const_mul' _ _ (by norm_num),lintegral_const_mul' _ _ (by norm_num)]
      rfl

theorem output_cauchy (a : A) : CauchySeq (output K I a) :=
  KernelEnergyCauchy.cauchy_of_energy_error _ _ (error_tendsto K a) (output_difference_bound K I a)

end SHE.KernelItoLimit
