module

public import SHEStochastic.NativeClockIntegral
public import SHEStochastic.NativeRowRepresentatives
public import SHE.PastItoAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeStoppedGram
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.PastItoInputs
open NativeRowRepresentatives
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

/-- Every observation keeps its own time: the covariance is exactly
`min(t_i,t_j) G_ij`, obtained from the original input inner product. -/
theorem stopped_gram (R : Fin n → Process (E := C) F μ H)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ᵐ p ∂energyMeasure μ H, ∀ i j, inner ℝ (R i p) (R j p) = G i j)
    (t : Fin n → ℝ≥0) (htH : ∀ i, t i ≤ H) :
    Matrix.gram ℝ (fun i ↦ FiniteCylindricalIto.processTransport (stop F μ H (t i) (R i))) =
      (fun i j ↦ (min (t i) (t j) : ℝ≥0) * G i j) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  ext i j
  rw [Matrix.gram_apply, L2.inner_def]
  have he : (fun p ↦ inner ℝ
      (FiniteCylindricalIto.processTransport (stop F μ H (t i) (R i)) p)
      (FiniteCylindricalIto.processTransport (stop F μ H (t j) (R j)) p)) =ᵐ[ν]
      (fun p ↦ (Set.Iio (min (t i) (t j))).indicator (fun _ ↦ G i j) p.1) := by
    filter_upwards [stop_transport_ae (t i) (R i), stop_transport_ae (t j) (R j), gram_ae R G hG]
      with p hi hj hp
    rw [hi, hj]
    by_cases hti : p.1 < t i <;> by_cases htj : p.1 < t j <;>
      simp [Set.indicator_apply, Set.mem_Iio, lt_min_iff, hti, htj, hp i j]
  rw [integral_congr_ae he,
    HilbertSimpleEnergyDefect.integral_time_profile _
      ((integrable_const (G i j)).indicator measurableSet_Iio)
      (deterministic_stop_predictable (F := F) (min (t i) (t j)) (G i j)),
    NativeClockIntegral.before_const H _ ((min_le_left _ _).trans (htH i))]

theorem band_predictable (a t : ℝ≥0) (f : ℝ≥0 × Ω → C)
    (hf : StronglyMeasurable[F.predictable] f) :
    StronglyMeasurable[F.predictable]
      (fun p ↦ (Set.Ioo a t).indicator (fun _ ↦ f p) p.1) := by
  have hm := (eventAfter_measurable F a (A := Set.univ) MeasurableSet.univ).inter
    (before_measurable F (t : ℝ))
  convert hf.indicator hm using 1
  funext p
  simp only [Set.indicator_apply, eventAfter, before, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_Ioi, Set.mem_univ, and_true, Set.mem_setOf_eq, Set.mem_Ioo, NNReal.coe_lt_coe]

theorem band_transport_ae (a t : ℝ≥0) (R : Process (E := C) F μ H) :
    FiniteCylindricalIto.processTransport (post F μ H a (stop F μ H t R)) =ᵐ[ν]
      (fun p ↦ (Set.Ioo a t).indicator (fun _ ↦ R p) p.1) := by
  apply transport_ae _ _ (band_predictable a t R (Lp.stronglyMeasurable R))
  filter_upwards [post_ae F μ H a (stop F μ H t R), stop_ae F μ H t R] with p hp hs
  rw [hp, hs]
  by_cases ha : a < p.1 <;> by_cases ht : p.1 < t <;>
    simp [ha, ht, Set.indicator_apply, Set.mem_Ioo, before, NNReal.coe_lt_coe]

theorem band_profiles (R : Fin n → Process (E := C) F μ H)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ᵐ p ∂energyMeasure μ H, ∀ i j, inner ℝ (R i p) (R j p) = G i j)
    (a t : ℝ≥0) :
    ∀ x : EuclideanSpace ℝ (Fin n), ∃ q : ℝ≥0 → ℝ,
      Integrable q νt ∧ (∀ r, 0 ≤ q r) ∧
      StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1) ∧
      (∀ᵐ p ∂ν, ‖HilbertGaussianVector.combination
        (fun i ↦ FiniteCylindricalIto.processTransport (post F μ H a (stop F μ H t (R i)))) x p‖ ^ 2 = q p.1) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨d, hd⟩ := exists_reference R G hG
  apply HilbertGaussianVector.profiles_of_gram _
    (fun i r ↦ (Set.Ioo a t).indicator (fun _ ↦ d i) r)
  · intro i
    exact (memLp_const (d i)).indicator measurableSet_Ioo.nullMeasurableSet
  · intro i
    exact band_predictable a t (fun _ ↦ d i) stronglyMeasurable_const
  · filter_upwards [ae_all_iff.mpr (fun i ↦ band_transport_ae a t (R i)), hd] with p hs hp
    intro i j
    rw [hs i, hs j]
    by_cases hmem : p.1 ∈ Set.Ioo a t <;> simp [hmem, hp i j]

end SHEStochastic.NativeStoppedGram
