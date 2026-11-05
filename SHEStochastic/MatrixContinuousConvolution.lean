module

public import SHEStochastic.MatrixTimeMoments
public import SHE.DampedContinuousVersion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixContinuousConvolution
open MeasureTheory Set SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ) ≤ 1) {U : ℝ} (hU : 0 ≤ U) (a : Fields (d := d) F U)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))

def process (r : ℝ) (ω : Ω) : Physical (d := d) :=
  MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N
    (DampedUnitTimeMoments.clock H r) (DampedUnitTimeMoments.clock_bound H r) ω

theorem process_measurable (r : ℝ) : Measurable (process hH hU a N r) :=
  (Lp.stronglyMeasurable _).measurable

theorem unit_moment16 {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫⁻ ω, ENNReal.ofReal (‖process hH hU a N s ω-process hH hU a N t ω‖^16) ∂μ) ≤
      ENNReal.ofReal (MatrixTimeMoments.momentConstant d U*|s-t|^2) := by
  have hb := MatrixTimeMoments.symmetric_increment_moment16 hH hU a N
    (DampedUnitTimeMoments.clock H s) (DampedUnitTimeMoments.clock H t)
    (DampedUnitTimeMoments.clock_bound H s) (DampedUnitTimeMoments.clock_bound H t)
  have hc : ((DampedUnitTimeMoments.clock H s : ℝ)-(DampedUnitTimeMoments.clock H t : ℝ))^2 ≤ |s-t|^2 := by
    rw [DampedUnitTimeMoments.clock_coe H hs,DampedUnitTimeMoments.clock_coe H ht,← mul_sub,mul_pow,sq_abs]
    have hh2 : (H : ℝ)^2 ≤ 1 := by nlinarith [H.2]
    exact (mul_le_mul_of_nonneg_right hh2 (sq_nonneg (s-t))).trans_eq (one_mul _)
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hc (MatrixTimeMoments.momentConstant_nonneg U)))

def version (t : ℝ≥0) (ω : Ω) : Physical (d := d) :=
  KolmogorovModification.modification (process hH hU a N) (DampedContinuousVersion.normalizedTime H t) ω

/-- Simultaneously continuous vector paths follow from the already
proved scalar-time Kolmogorov construction, with a generic Hilbert target. -/
theorem continuous (hH0 : 0 < H) (ω : Ω) : Continuous (fun t => version hH hU a N t ω) :=
  (KolmogorovModification.continuousOn_modification (process hH hU a N) ω).comp_continuous
    (DampedContinuousVersion.continuous_normalizedTime H) (DampedContinuousVersion.normalizedTime_mem hH0)

theorem measurable (hH0 : 0 < H) (t : ℝ≥0) : Measurable (version hH hU a N t) :=
  KolmogorovModification.modification_measurable μ (process hH hU a N)
    (fun r _ => process_measurable hH hU a N r) (MatrixTimeMoments.momentConstant_nonneg U)
    (fun s hs t ht => unit_moment16 hH hU a N hs ht) (DampedContinuousVersion.normalizedTime_mem hH0 t)

theorem version_ae (hH0 : 0 < H) (t : ℝ≥0) :
    version hH hU a N t =ᵐ[μ] MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N
      (min t H) (min_le_right _ _) := by
  have he := KolmogorovModification.modification_ae μ (process hH hU a N)
    (fun r _ => process_measurable hH hU a N r) (MatrixTimeMoments.momentConstant_nonneg U)
    (fun s hs t ht => unit_moment16 hH hU a N hs ht) (DampedContinuousVersion.normalizedTime_mem hH0 t)
  change version hH hU a N t =ᵐ[μ] MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N
    (DampedUnitTimeMoments.clock H (DampedContinuousVersion.normalizedTime H t)) _ at he
  simpa only [DampedContinuousVersion.clock_normalizedTime hH0] using he

theorem version_ae_of_le (hH0 : 0 < H) (t : ℝ≥0) (ht : t ≤ H) :
    version hH hU a N t =ᵐ[μ] MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t ht := by
  simpa only [min_eq_left ht] using version_ae hH hU a N hH0 t

theorem joint_measurable (hH0 : 0 < H) : Measurable (fun p : ℝ≥0 × Ω => version hH hU a N p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (continuous hH hU a N hH0) (measurable hH hU a N hH0)

theorem convolution_ae_version (hH0 : 0 < H) :
    MatrixPredictableConvolution.convolution hH U hU N a =ᵐ[energyMeasure μ H]
      fun p : ℝ≥0 × Ω => version hH hU a N p.1 p.2 :=
  KernelItoVersion.convolution_ae_version (model F μ H hH U hU) (NativeMatrixConvolution.terminalIto N) a
    (fun t ht => MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t ht)
    (fun t ht htH => MatrixFixedApproximation.integral_tendsto hH hU a N t ht htH)
    _ (joint_measurable hH hU a N hH0).stronglyMeasurable (version_ae_of_le hH hU a N hH0)

theorem adapted_versions (hH0 : 0 < H) (t : ℝ≥0) :
    ∃ Z : Ω → Physical (d := d), StronglyMeasurable[F t] Z ∧ version hH hU a N t =ᵐ[μ] Z := by
  let q := min t H
  let v := MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable q (min_le_right _ _)
  have hs : ∀ᵐ p ∂energyMeasure μ H, q < p.1 → v p=0 := by
    filter_upwards [MatrixAnalyticConvolution.input_ae F μ H hH U hU a.value a.upper a.measurable q
      (min_le_right _ _)] with p hp hpt
    rw [hp]
    exact MatrixAnalyticKernel.zero (sub_nonpos.mpr (by exact_mod_cast hpt.le)) (a.value p)
  obtain ⟨Z,hZ,he⟩ := (NativeMatrixConvolution.terminalIto N).adapted q v hs
  exact ⟨Z,hZ.mono (F.mono (min_le_left _ _)),(version_ae hH hU a N hH0 t).trans he⟩

/-- Null completeness supplies predictability of the simultaneously
continuous native modification; the completeness hypothesis is explicit. -/
theorem predictable (hnull : NullCompleteFiltration.ContainsNullSets F μ) (hH0 : 0 < H) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => version hH hU a N p.1 p.2) :=
  NullCompleteFiltration.predictable_of_continuous_versions F μ hnull _
    (adapted_versions hH hU a N hH0) (continuous hH hU a N hH0)

end SHEStochastic.MatrixContinuousConvolution
