module

public import SHEStochastic.ProductIndependence
public import SHEStochastic.FiniteScalarIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.RandomInitialBrownianFamily
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal

variable {X Ω ι : Type*} [mX : MeasurableSpace X] [mΩ : MeasurableSpace Ω] [DecidableEq ι]

def initialFiltration : Filtration ℝ≥0 mX where
  seq _ := mX
  mono' _ _ _ := le_rfl
  le' _ := le_rfl

variable (ρ : Measure X) (μ : Measure Ω) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
  (F : Filtration ℝ≥0 mΩ) (H : ℝ≥0) (P : FiniteScalarIto.Family F μ H ι)

abbrev Space := IndependentNoiseCompletion.Space ρ μ
def filtration := IndependentNoiseCompletion.filtration ρ μ initialFiltration F

theorem future_independent (n : ℕ) (a : Fin n → ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H) :
    Indep (MeasurableSpace.comap (fun z : Space ρ μ ↦
      (WithLp.toLp 2 (fun i ↦ P.W (a i) t z.2 - P.W (a i) s z.2) : WordRecursion.State n))
      inferInstance) (filtration ρ μ F s) (IndependentNoiseCompletion.measure ρ μ) := by
  let v (sample : Ω) : WordRecursion.State n :=
    WithLp.toLp 2 (fun i ↦ P.W (a i) t sample - P.W (a i) s sample)
  have hm : Measurable v := (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    (measurable_pi_iff.mpr fun i ↦
      (FiniteScalarIto.measurable_coordinate P.toCoordinates (a i) t).sub
        (FiniteScalarIto.measurable_coordinate P.toCoordinates (a i) s))
  have hi := ProductIndependence.independent_completed_past ρ μ initialFiltration F s
    (m₁ := ⊥) (n₁ := MeasurableSpace.comap v inferInstance) bot_le hm.comap_le
    (indep_bot_left _) ((P.law n a).2 s t hst ht)
  apply indep_of_indep_of_le_left hi
  change MeasurableSpace.comap (v ∘ Prod.snd) _ ≤ (⊥ : MeasurableSpace X).prod
    (MeasurableSpace.comap v inferInstance)
  rw [← MeasurableSpace.comap_comp]
  exact le_sup_right

/-- Add an independent initial-state distribution while keeping the
actual native Brownian coordinates and completing all joint null sets.
The initial state is available at time zero, independently of the noise. -/
def family : FiniteScalarIto.Family (filtration ρ μ F)
    (IndependentNoiseCompletion.measure ρ μ) H ι where
  W i t z := P.W i t z.2
  adapted i t :=
    ((P.adapted i t).comp (@measurable_snd X Ω mX (F t))).mono le_sup_left le_rfl
  continuous i z := P.continuous i z.2
  law n a := ⟨fun t ht ↦ ((P.law n a).1 t ht).fun_comp
    (IndependentNoiseCompletion.snd_preserving ρ μ).hasLaw,
    future_independent ρ μ F H P n a⟩

theorem initial_adapted (t : ℝ≥0) :
    Measurable[filtration ρ μ F t] (Prod.fst : Space ρ μ → X) :=
  (@measurable_fst X Ω mX (F t)).mono le_sup_left le_rfl

theorem contains_null : NullCompleteFiltration.ContainsNullSets (filtration ρ μ F)
    (IndependentNoiseCompletion.measure ρ μ) :=
  IndependentNoiseCompletion.contains_null ρ μ initialFiltration F

end SHEStochastic.RandomInitialBrownianFamily
