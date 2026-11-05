module

public import SHEStochastic.HilbertGaussianLaw
public import SHE.PredictableSteps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeUnitGaussianCell
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

/-- A unit row frozen in the original past gives a genuine Gaussian
cell integral independent of that entire past, even when its direction
is random in the noise Hilbert space. -/
theorem law_and_independent (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) (R : Ω → C)
    (hR : StronglyMeasurable[F s] R) (hunit : ∀ ω, ‖R ω‖ = 1) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    let Z := FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H
      (HilbertSimpleInputs.step s t hst htH R hR 1 (fun ω ↦ (hunit ω).le)))
    HasLaw (Z : Ω → ℝ) (gaussianReal 0 (t - s)) μ ∧
      Indep (MeasurableSpace.comap (Z : Ω → ℝ) (borel ℝ)) (F s) μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let U := HilbertSimpleInputs.step s t hst htH R hR 1 (fun ω ↦ (hunit ω).le)
  let u := HilbertSimpleInputs.embedding F μ H U
  let q (r : ℝ≥0) : ℝ := (Set.Ioc s t).indicator (fun _ ↦ 1) r
  have hq : Integrable q νt := (integrable_const (1 : ℝ)).indicator measurableSet_Ioc
  have hq0 (r : ℝ≥0) : 0 ≤ q r := Set.indicator_nonneg (fun _ _ ↦ zero_le_one) r
  have hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1) := by
    have hc := (stronglyMeasurable_const (b := (1 : ℝ))).indicator
      (measurableSet_predictable_Ioc_prod (𝓕 := F) s t MeasurableSet.univ)
    convert hc using 1
    funext p
    simp only [q, Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true]
  have hu : ∀ᵐ p ∂ν, p.1 ≤ s → u p = 0 := by
    filter_upwards [HilbertSimpleInputs.embedding_ae F μ H U] with p hp hs
    rw [hp]
    change U.val p.1 p.2 = 0
    rw [HilbertSimpleInputs.step_apply]
    exact Set.indicator_of_notMem (fun h ↦ (not_lt.mpr hs) h.1) _
  have hprofile : ∀ᵐ p ∂ν, ‖u p‖ ^ 2 = q p.1 := by
    filter_upwards [HilbertSimpleInputs.embedding_ae F μ H U] with p hp
    rw [hp]
    change ‖U.val p.1 p.2‖ ^ 2 = q p.1
    rw [HilbertSimpleInputs.step_apply]
    by_cases hm : p.1 ∈ Set.Ioc s t <;> simp [q, hm, hunit]
  have hi : (∫ r, q r ∂νt) = ((t - s : ℝ≥0) : ℝ) := by
    simpa only [q, NNReal.coe_sub hst, mul_one] using
      HilbertSimplePartition.integral_cell_const s t hst htH (1 : ℝ)
  have hh := HilbertGaussianLaw.law_and_independent P e s (hst.trans htH) u hu q hq hq0 hqp hprofile
  simpa only [hi, Real.toNNReal_coe] using hh

end SHEStochastic.NativeUnitGaussianCell
