module

public import SHEStochastic.HilbertGaussianVector

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeRowRepresentatives
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

theorem inputMeasure_eq : ν = (energyMeasure μ H).trim (predictable_le_product F) :=
  (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)).symm

/-- Transfer an original product-measure representative to the native
predictable input without changing the chosen row. -/
theorem transport_ae (v : Process (E := C) F μ H) (f : ℝ≥0 × Ω → C)
    (hf : StronglyMeasurable[F.predictable] f) (hv : v =ᵐ[energyMeasure μ H] f) :
    FiniteCylindricalIto.processTransport v =ᵐ[ν] f := by
  have ht : v =ᵐ[ν] f := by
    rw [inputMeasure_eq]
    exact ae_eq_trim_of_measurable (predictable_le_product F)
      (Lp.stronglyMeasurable v).measurable hf.measurable hv
  exact (FiniteCylindricalIto.processTransport_ae v).trans ht

theorem stop_transport_ae (t : ℝ≥0) (v : Process (E := C) F μ H) :
    FiniteCylindricalIto.processTransport (stop F μ H t v) =ᵐ[ν]
      (fun p ↦ (Set.Iio t).indicator (fun _ ↦ v p) p.1) := by
  have hh := transport_ae (stop F μ H t v) ((before (Ω := Ω) (t : ℝ)).indicator v)
    ((Lp.stronglyMeasurable v).indicator (before_measurable F t)) (stop_ae F μ H t v)
  exact hh.mono fun p hp ↦ by
    simpa only [before, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio, NNReal.coe_lt_coe] using hp

theorem gram_ae {n : ℕ} (R : Fin n → Process (E := C) F μ H) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ᵐ p ∂energyMeasure μ H, ∀ i j, inner ℝ (R i p) (R j p) = G i j) :
    ∀ᵐ p ∂ν, ∀ i j, inner ℝ (R i p) (R j p) = G i j := by
  rw [inputMeasure_eq]
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  exact ae_eq_trim_of_measurable (predictable_le_product F)
    ((Lp.stronglyMeasurable (R i)).inner (Lp.stronglyMeasurable (R j))).measurable
    measurable_const (hG.mono fun p hp ↦ hp i j)

/-- A constant Gram can be represented by deterministic vectors. The
zero-horizon case is handled without extracting a point from a null measure. -/
theorem exists_reference {n : ℕ} (R : Fin n → Process (E := C) F μ H)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ᵐ p ∂energyMeasure μ H, ∀ i j, inner ℝ (R i p) (R j p) = G i j) :
    ∃ d : Fin n → C, ∀ᵐ p ∂ν, ∀ i j,
      inner ℝ (R i p) (R j p) = inner ℝ (d i) (d j) := by
  by_cases hν : ν = 0
  · exact ⟨fun _ ↦ 0, by simp [hν]⟩
  · haveI : NeZero ν := ⟨hν⟩
    obtain ⟨p, hp⟩ := (gram_ae R G hG).exists
    exact ⟨fun i ↦ R i p, (gram_ae R G hG).mono fun z hz i j ↦ (hz i j).trans (hp i j).symm⟩

theorem deterministic_stop_predictable (t : ℝ≥0) (d : C) :
    StronglyMeasurable[F.predictable]
      (fun p : ℝ≥0 × Ω ↦ (Set.Iio t).indicator (fun _ ↦ d) p.1) := by
  have hh := (stronglyMeasurable_const (b := d)).indicator (before_measurable F (t : ℝ))
  convert hh using 1
  funext p
  simp only [before, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio, NNReal.coe_lt_coe]

/-- The stopped rows inherit a deterministic time-dependent Gram from
the original constant Gram, including zero horizon and zero directions. -/
theorem stopped_profiles {n : ℕ} (R : Fin n → Process (E := C) F μ H)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ᵐ p ∂energyMeasure μ H, ∀ i j, inner ℝ (R i p) (R j p) = G i j)
    (t : Fin n → ℝ≥0) :
    ∀ x : EuclideanSpace ℝ (Fin n), ∃ q : ℝ≥0 → ℝ,
      Integrable q νt ∧ (∀ r, 0 ≤ q r) ∧
      StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1) ∧
      (∀ᵐ p ∂ν, ‖HilbertGaussianVector.combination
        (fun i ↦ FiniteCylindricalIto.processTransport (stop F μ H (t i) (R i))) x p‖ ^ 2 = q p.1) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨d, hd⟩ := exists_reference R G hG
  apply HilbertGaussianVector.profiles_of_gram _
    (fun i r ↦ (Set.Iio (t i)).indicator (fun _ ↦ d i) r)
  · intro i
    exact (memLp_const (d i)).indicator measurableSet_Iio.nullMeasurableSet
  · intro i
    exact deterministic_stop_predictable (F := F) (t i) (d i)
  · filter_upwards [ae_all_iff.mpr (fun i ↦ stop_transport_ae (t i) (R i)), hd] with p hs hp
    intro i j
    rw [hs i, hs j]
    by_cases hi : p.1 < t i <;> by_cases hj : p.1 < t j <;>
      simp [Set.indicator_apply, Set.mem_Iio, hi, hj, hp i j]

end SHEStochastic.NativeRowRepresentatives
