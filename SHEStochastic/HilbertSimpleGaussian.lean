module

public import SHEStochastic.HilbertSimplePartition
public import SHEStochastic.HilbertGaussianStep
public import SHEStochastic.GaussianCharacteristicDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.HilbertSimpleGaussian
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition HilbertSimplePartition

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

variable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (V : HilbertSimpleInputs.bounded (E := C) F H)

def cellIntegral (k : ℕ) : Lp ℝ 2 μ :=
  FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H (cell V k))

theorem cell_adapted (k : ℕ) :
    AEStronglyMeasurable[F (marshalPart F H V.val (k + 1))]
      (cellIntegral P e V k : Ω → ℝ) μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply FiniteCylindricalIto.rawIntegral_adapted
  filter_upwards [HilbertSimpleInputs.embedding_ae F μ H (cell V k)] with p hp ht
  rw [hp]
  change (cell V k).val p.1 p.2 = 0
  simp only [cell, HilbertSimpleInputs.step_apply]
  exact Set.indicator_of_notMem
    (fun h : p.1 ∈ Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)) ↦
      (not_le.mpr ht) h.2) _

def cellVersion (k : ℕ) : Ω → ℝ :=
  (cell_adapted P e V k).mk (cellIntegral P e V k)

theorem cellVersion_measurable (k : ℕ) :
    StronglyMeasurable[F (marshalPart F H V.val (k + 1))] (cellVersion P e V k) :=
  (cell_adapted P e V k).stronglyMeasurable_mk

theorem cellVersion_ae (k : ℕ) : cellIntegral P e V k =ᵐ[μ] cellVersion P e V k :=
  (cell_adapted P e V k).ae_eq_mk

/-- The starting cell may be any cell, so weights from the entire past
at that boundary can be retained, not just weights measurable at time zero. -/
def gridFiltration (j : ℕ) : Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := F (marshalPart F H V.val (j + k))
  mono' := fun _ _ h ↦ F.mono (marshalPart_mono F H V.val V.property (Nat.add_le_add_left h j))
  le' k := F.le _

@[simp] theorem gridFiltration_apply (j k : ℕ) :
    gridFiltration V j k = F (marshalPart F H V.val (j + k)) := rfl

def partialSum (j k : ℕ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range k, cellVersion P e V (j + l) ω

theorem partialSum_adapted (j : ℕ) :
    StronglyAdapted (gridFiltration V j) (partialSum P e V j) := by
  intro k
  apply Finset.stronglyMeasurable_fun_sum
  intro l hl
  apply (cellVersion_measurable P e V (j + l)).mono
  apply F.mono
  apply marshalPart_mono F H V.val V.property
  have hlk := Finset.mem_range.mp hl
  omega

theorem partialSum_increment (j k : ℕ) (ω : Ω) :
    partialSum P e V j (k + 1) ω - partialSum P e V j k ω = cellVersion P e V (j + k) ω := by
  simp [partialSum, Finset.sum_range_succ]

theorem partialSum_ae (j k : ℕ) :
    (∑ l ∈ Finset.range k, cellIntegral P e V (j + l) : Lp ℝ 2 μ) =ᵐ[μ]
      partialSum P e V j k := by
  have ha : ∀ᵐ ω ∂μ, ∀ l : ℕ, cellIntegral P e V (j + l) ω = cellVersion P e V (j + l) ω :=
    ae_all_iff.mpr (fun l ↦ cellVersion_ae P e V (j + l))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range k) (fun l ↦ cellIntegral P e V (j + l)), ha]
    with ω hs hω
  rw [hs]
  simp only [Finset.sum_apply, partialSum]
  exact Finset.sum_congr rfl (fun l _ ↦ hω l)

def variance (k : ℕ) (ω : Ω) : ℝ :=
  (((marshalPart F H V.val (k + 1) - marshalPart F H V.val k : ℝ≥0) : ℝ)) *
    ‖marshalMult F H V.val k ω‖ ^ 2

theorem variance_integrable (k : ℕ) : Integrable (variance V k) μ := by
  have hR := (stronglyMeasurable_marshalMult F H V.val k).mono (F.le _)
  have hLp : MemLp (marshalMult F H V.val k) 2 μ :=
    MemLp.of_bound hR.aestronglyMeasurable _
      (Filter.Eventually.of_forall (marshalMult_norm_le F H V.val k))
  exact hLp.norm.integrable_sq.const_mul _

theorem conditional_increment (j k : ℕ) :
    μ[fun ω ↦ Complex.exp
      (((partialSum P e V j (k + 1) ω - partialSum P e V j k ω : ℝ) : ℂ) * Complex.I)
        | gridFiltration V j k] =ᵐ[μ]
      (fun ω ↦ (Real.exp (-variance V (j + k) ω / 2) : ℂ)) := by
  have hc := HilbertGaussianStep.condExp_step P e
    (marshalPart F H V.val (j + k)) (marshalPart F H V.val (j + k + 1))
    (marshalPart_mono F H V.val V.property (Nat.le_succ _))
    (marshalPart_le_T F H V.val V.property _)
    (marshalMult F H V.val (j + k)) (stronglyMeasurable_marshalMult F H V.val (j + k))
    _ (marshalMult_norm_le F H V.val (j + k))
  have ha : (fun ω ↦ Complex.exp
      (((partialSum P e V j (k + 1) ω - partialSum P e V j k ω : ℝ) : ℂ) * Complex.I)) =ᵐ[μ]
      (fun ω ↦ Complex.exp ((cellIntegral P e V (j + k) ω : ℂ) * Complex.I)) := by
    filter_upwards [cellVersion_ae P e V (j + k)] with ω hω
    rw [partialSum_increment, hω]
  exact (condExp_congr_ae ha).trans hc

/-- Quantitative Gaussian recognition for the actual native integral of
a finite block of time cells, retaining an arbitrary bounded weight from
the full past at the starting boundary. -/
theorem weighted_defect (j N : ℕ) (φ : Ω → ℂ)
    (hφ : StronglyMeasurable[F (marshalPart F H V.val j)] φ)
    (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) (q : ℕ → ℝ) (hq : ∀ k, 0 ≤ q k) :
    ‖(∫ ω, φ ω * Complex.exp
      ((((∑ l ∈ Finset.range N, cellIntegral P e V (j + l) : Lp ℝ 2 μ) ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (Real.exp (-(∑ k ∈ Finset.range N, q k) / 2) : ℂ) * (∫ ω, φ ω ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, ∫ ω, |variance V (j + k) ω - q k| ∂μ := by
  have hφ0 : StronglyMeasurable[gridFiltration V j 0] φ := by simpa [gridFiltration] using hφ
  have hh := GaussianCharacteristicDefect.weighted_finite_steps_defect
    (gridFiltration V j) φ hφ0 hφbound (partialSum P e V j) (partialSum_adapted P e V j)
    (Filter.Eventually.of_forall fun ω ↦ by simp [partialSum])
    (fun k ↦ variance V (j + k)) (fun k ↦ variance_integrable V (j + k))
    (fun k ω ↦ mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)) q hq
    (conditional_increment P e V j) N
  have he := integral_congr_ae ((partialSum_ae P e V j N).mono fun ω hω ↦
    congrArg (fun x : ℝ ↦ φ ω * Complex.exp ((x : ℂ) * Complex.I)) hω)
  rw [he]
  exact hh

end SHEStochastic.HilbertSimpleGaussian
