module

public import SHE.KernelItoModel

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
variable (K : Model A C 𝓕 μ h)
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)

omit [SFinite μ] in
theorem pair_energy_tendsto (a b : A) :
    Tendsto (fun n => ∫⁻ p,ENNReal.ofReal (‖K.approx a n p-K.approx b n p‖^2) ∂measure μ h)
      atTop (𝓝 (∫⁻ p,ENNReal.ofReal (‖K.raw a p-K.raw b p‖^2) ∂measure μ h)) := by
  have hfm : Measurable (fun p => ENNReal.ofReal (‖K.raw a p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((K.raw_measurable a).norm.pow_const 2)
  have hgm : Measurable (fun p => ENNReal.ofReal (‖K.raw b p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((K.raw_measurable b).norm.pow_const 2)
  have hf : (∫⁻ p,(2:ℝ≥0∞)*(ENNReal.ofReal (‖K.raw a p‖^2)+ENNReal.ofReal (‖K.raw b p‖^2)) ∂measure μ h) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ (by norm_num),lintegral_add_left hfm]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr
      ⟨(K.raw_energy_finite a).ne,(K.raw_energy_finite b).ne⟩)
  apply tendsto_lintegral_of_dominated_convergence
    (fun p => (2:ℝ≥0∞)*(ENNReal.ofReal (‖K.raw a p‖^2)+ENNReal.ofReal (‖K.raw b p‖^2)))
  · intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      (((K.approx_measurable a n).sub (K.approx_measurable b n)).norm.pow_const 2)
  · intro n
    filter_upwards [K.approx_norm_le a n,K.approx_norm_le b n] with p hfn hgn
    have htri := norm_sub_le (K.approx a n p) (K.approx b n p)
    have hs : ‖K.approx a n p-K.approx b n p‖^2 ≤ 2*(‖K.raw a p‖^2+‖K.raw b p‖^2) := by
      nlinarith [norm_nonneg (K.approx a n p-K.approx b n p),norm_nonneg (K.raw a p),
        norm_nonneg (K.raw b p),sq_nonneg (‖K.raw a p‖-‖K.raw b p‖)]
    have hb := ENNReal.ofReal_le_ofReal hs
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),ENNReal.ofReal_ofNat] using hb
  · exact hf
  · filter_upwards [K.approx_tendsto a,K.approx_tendsto b] with p hfa hfb
    have hs := hfa.sub hfb
    have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.norm.pow 2)
    change Tendsto (fun n => ENNReal.ofReal (‖K.approx a n p-K.approx b n p‖^2))
      atTop (𝓝 (ENNReal.ofReal (‖K.raw a p-K.raw b p‖^2))) at hn
    exact hn

variable [CompleteSpace E]

/-- Constructed complete predictable L² limit for any actual kernel model
whose deterministic approximation obligations have been discharged. -/
def convolution (a : A) : Process (E := E) 𝓕 μ h := limUnder atTop (output K I a)

theorem approximation_tendsto (a : A) :
    Tendsto (output K I a) atTop (𝓝 (convolution K I a)) :=
  (output_cauchy K I a).tendsto_limUnder

theorem difference_isometry (a b : A) :
    ENNReal.ofReal (‖convolution K I a-convolution K I b‖^2)=
      ∫⁻ p,ENNReal.ofReal (‖K.raw a p-K.raw b p‖^2) ∂measure μ h := by
  have hs := (approximation_tendsto K I a).sub (approximation_tendsto K I b)
  have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.norm.pow 2)
  change Tendsto (fun n => ENNReal.ofReal (‖output K I a n-output K I b n‖^2)) atTop
    (𝓝 (ENNReal.ofReal (‖convolution K I a-convolution K I b‖^2))) at hout
  have hkernel := pair_energy_tendsto K a b
  have heq : (fun n => ENNReal.ofReal (‖output K I a n-output K I b n‖^2))=
      (fun n => ∫⁻ p,ENNReal.ofReal (‖K.approx a n p-K.approx b n p‖^2) ∂measure μ h) := by
    funext n
    exact output_pair_energy K I a b n n
  rw [← heq] at hkernel
  exact tendsto_nhds_unique hout hkernel

end SHE.KernelItoLimit
