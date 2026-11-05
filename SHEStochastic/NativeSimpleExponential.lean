module

public import SHEStochastic.DiscreteGaussianExponential
public import SHEStochastic.NativeHilbertCellMGF
public import SHEStochastic.HilbertSimpleGaussian
public import SHEStochastic.HilbertSimplePartition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeSimpleExponential
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition HilbertSimpleGaussian

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- All stochastic fields of the finite-partition exponential model
are supplied by the actual native integral and its proved Hilbert-cell
identities. Nothing new is accepted as an external input. -/
def model (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) :
    DiscreteGaussianExponential.Model (gridFiltration V 0) μ where
  increment := cellVersion P e V
  variance := HilbertSimpleGaussian.variance V
  increment_adapted k := by
    rw [gridFiltration_apply, Nat.zero_add]
    exact cellVersion_measurable P e V k
  variance_adapted k := by
    rw [gridFiltration_apply, Nat.zero_add]
    exact ((stronglyMeasurable_marshalMult F H V.val k).norm.pow 2).const_mul _
  variance_nonneg k ω := mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)
  exp_integrable k a := by
    have hK0 : 0 ≤ (V.val.value.support.card : ℝ) * V.val.valueBound :=
      mul_nonneg (Nat.cast_nonneg _) V.val.valueBound_nonneg
    obtain ⟨hi, _⟩ := NativeHilbertCellMGF.freeze P e
      (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))
      (marshalPart_le_T F H V.val V.property (k + 1))
      (marshalMult F H V.val k) (stronglyMeasurable_marshalMult F H V.val k)
      _ hK0 (marshalMult_norm_le F H V.val k) v hv a
    change Integrable (fun ω ↦ Real.exp (a * cellIntegral P e V k ω)) μ at hi
    exact hi.congr ((cellVersion_ae P e V k).mono fun ω hω ↦
      congrArg (fun x : ℝ ↦ Real.exp (a * x)) hω)
  normalized k a := by
    rw [gridFiltration_apply, Nat.zero_add]
    have hK0 : 0 ≤ (V.val.value.support.card : ℝ) * V.val.valueBound :=
      mul_nonneg (Nat.cast_nonneg _) V.val.valueBound_nonneg
    obtain ⟨_, hc⟩ := NativeHilbertCellMGF.density P e
      (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))
      (marshalPart_le_T F H V.val V.property (k + 1))
      (marshalMult F H V.val k) (stronglyMeasurable_marshalMult F H V.val k)
      _ hK0 (marshalMult_norm_le F H V.val k) v hv a
    change μ[fun ω ↦ Real.exp (a * cellIntegral P e V k ω -
      a ^ 2 * (((marshalPart F H V.val (k + 1) - marshalPart F H V.val k : ℝ≥0) : ℝ)) *
        ‖marshalMult F H V.val k ω‖ ^ 2 / 2) | F (marshalPart F H V.val k)] =ᵐ[μ] fun _ ↦ 1 at hc
    have he : (fun ω ↦ Real.exp (a * cellVersion P e V k ω -
        a ^ 2 * HilbertSimpleGaussian.variance V k ω / 2)) =ᵐ[μ]
        (fun ω ↦ Real.exp (a * cellIntegral P e V k ω -
          a ^ 2 * (((marshalPart F H V.val (k + 1) - marshalPart F H V.val k : ℝ≥0) : ℝ)) *
            ‖marshalMult F H V.val k ω‖ ^ 2 / 2)) := by
      filter_upwards [cellVersion_ae P e V k] with ω hω
      change Real.exp (a * cellVersion P e V k ω - a ^ 2 * HilbertSimpleGaussian.variance V k ω / 2) = _
      rw [← hω]
      congr 1
      dsimp [HilbertSimpleGaussian.variance]
      ring
    exact (condExp_congr_ae he).trans hc

theorem source_ae (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) (N : ℕ)
    (hN : marshalPart F H V.val N = H) :
    FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) =ᵐ[μ]
      (model P e V v hv).sumIncrement N := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hi : (∑ k ∈ Finset.range N, cellIntegral P e V k : Lp ℝ 2 μ) =
      FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) := by
    simpa only [map_sum, cellIntegral] using congrArg (FiniteCylindricalIto.rawIntegral P.toCoordinates e)
      (HilbertSimplePartition.embedding_sum (μ := μ) V hN)
  have hp := partialSum_ae P e V 0 N
  simp only [Nat.zero_add] at hp
  rw [hi] at hp
  filter_upwards [hp] with ω hω
  change FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) ω =
    ∑ k ∈ Finset.range N, cellVersion P e V k ω
  change FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) ω =
    ∑ k ∈ Finset.range N, cellVersion P e V (0 + k) ω at hω
  simpa only [Nat.zero_add] using hω

theorem energy_eq (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) (N : ℕ)
    (hN : marshalPart F H V.val N = H) (ω : Ω) :
    (model P e V v hv).sumVariance N ω =
      ∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
  change (∑ k ∈ Finset.range N, HilbertSimpleGaussian.variance V k ω) = _
  have he (k : ℕ) : HilbertSimpleGaussian.variance V k ω =
      (((marshalPart F H V.val (k + 1) : ℝ≥0) : ℝ) - marshalPart F H V.val k) *
        ‖marshalMult F H V.val k ω‖ ^ 2 := by
    rw [HilbertSimpleGaussian.variance, NNReal.coe_sub
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))]
  simp_rw [he]
  exact HilbertSimplePartition.energy_sum V hN ω

theorem exponential_ae (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) (N : ℕ)
    (hN : marshalPart F H V.val N = H) (a : ℝ) :
    (model P e V v hv).exponential a N =ᵐ[μ]
      (fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e
        (HilbertSimpleInputs.embedding F μ H V) ω - a ^ 2 *
          (∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H) / 2)) := by
  filter_upwards [source_ae P e V v hv N hN] with ω hω
  change Real.exp (a * (model P e V v hv).sumIncrement N ω -
    a ^ 2 * (model P e V v hv).sumVariance N ω / 2) = _
  rw [← hω, energy_eq P e V v hv N hN ω]

/-- Mean one for the actual native simple-input stochastic exponential,
with its pathwise time energy. -/
theorem mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) (N : ℕ)
    (hN : marshalPart F H V.val N = H) (a : ℝ) :
    let ρ := fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e
      (HilbertSimpleInputs.embedding F μ H V) ω - a ^ 2 *
        (∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H) / 2)
    Integrable ρ μ ∧ (∫ ω, ρ ω ∂μ) = 1 := by
  have he := exponential_ae P e V v hv N hN a
  exact ⟨((model P e V v hv).exponential_integrable a N).congr he,
    (integral_congr_ae he.symm).trans ((model P e V v hv).integral_eq_one a N)⟩

theorem square_integral_le (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) (N : ℕ)
    (hN : marshalPart F H V.val N = H) (a K : ℝ)
    (hcap : ∀ᵐ ω ∂μ, (∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H) ≤ K) :
    let ρ := fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e
      (HilbertSimpleInputs.embedding F μ H V) ω - a ^ 2 *
        (∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H) / 2)
    Integrable (fun ω ↦ ρ ω ^ 2) μ ∧ (∫ ω, ρ ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) := by
  have hMcap : ∀ᵐ ω ∂μ, (model P e V v hv).sumVariance N ω ≤ K := by
    simpa only [energy_eq P e V v hv N hN] using hcap
  obtain ⟨hi, hb⟩ := (model P e V v hv).square_integral_le a N K hMcap
  have he := (exponential_ae P e V v hv N hN a).mono fun ω hω ↦ congrArg (fun x : ℝ ↦ x ^ 2) hω
  exact ⟨hi.congr he, (integral_congr_ae (Filter.EventuallyEq.symm he)).trans_le hb⟩

end SHEStochastic.NativeSimpleExponential
