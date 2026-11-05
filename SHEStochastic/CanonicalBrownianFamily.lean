module

public import SHEStochastic.CanonicalBrownianCoordinates
public import SHEStochastic.RandomInitialBrownianFamily
public import SHEStochastic.BrownianCoordinateVersions
public import SHE.HaarInfinite

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.CanonicalBrownianFamily
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal
local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "μ" => CanonicalBrownianMeasure.measure
abbrev Space := IndependentNoiseCompletion.Space ρ μ
local instance (priority := 2000) completedSigma : MeasurableSpace Space :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×CanonicalBrownianChannels.Sample) inferInstance ((ρ).prod μ)
def measure : Measure Space := IndependentNoiseCompletion.measure ρ μ
instance probability : IsProbabilityMeasure measure := by
  unfold measure
  infer_instance

def filtration := IndependentNoiseCompletion.filtration ρ μ
  RandomInitialBrownianFamily.initialFiltration CanonicalBrownianCoordinates.filtration

/-- Null completion preserves the entire countable-channel future
increment law and independence from the full completed past. -/
theorem future_independent (n : ℕ) (a : Fin n → ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun z : Space => (WithLp.toLp 2
      (fun i => CanonicalBrownianChannels.value (a i) t z.2-CanonicalBrownianChannels.value (a i) s z.2) :
        GaussianIncrement.State n)) inferInstance) (filtration s) measure := by
  let v := fun ω : CanonicalBrownianChannels.Sample => (WithLp.toLp 2
    (fun i => CanonicalBrownianChannels.value (a i) t ω-CanonicalBrownianChannels.value (a i) s ω) :
      GaussianIncrement.State n)
  have hm : Measurable v := (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    (measurable_pi_iff.mpr (fun i => (CanonicalBrownianChannels.measurable_value (a i) t).sub
      (CanonicalBrownianChannels.measurable_value (a i) s)))
  have hi := ProductIndependence.independent_completed_past ρ μ
    RandomInitialBrownianFamily.initialFiltration CanonicalBrownianCoordinates.filtration s
    (m₁ := ⊥) (n₁ := MeasurableSpace.comap v inferInstance) bot_le hm.comap_le
    (indep_bot_left _) (CanonicalBrownianCoordinates.future_independent n a s t hst)
  apply indep_of_indep_of_le_left hi
  change MeasurableSpace.comap (v ∘ Prod.snd) _ ≤ (⊥ : MeasurableSpace Unit).prod
    (MeasurableSpace.comap v inferInstance)
  rw [←MeasurableSpace.comap_comp]
  exact le_sup_right

def coordinates : FiniteScalarIto.Coordinates filtration measure 1 ℕ where
  W i t z := CanonicalBrownianChannels.value i t z.2
  adapted i t :=
    ((CanonicalBrownianCoordinates.adapted i t).comp
      (@measurable_snd Unit CanonicalBrownianChannels.Sample inferInstance
        (CanonicalBrownianCoordinates.filtration t))).mono le_sup_left le_rfl
  law n a := ⟨fun t ht => (CanonicalBrownianCoordinates.finite_law a t ht).fun_comp
    (IndependentNoiseCompletion.snd_preserving ρ μ).hasLaw,
    fun s t hst _ => future_independent n a s t hst⟩

theorem contains_null : NullCompleteFiltration.ContainsNullSets filtration measure :=
  IndependentNoiseCompletion.contains_null ρ μ RandomInitialBrownianFamily.initialFiltration
    CanonicalBrownianCoordinates.filtration

/-- An actually constructed continuous adapted native Brownian family.
No Brownian-existence hypothesis remains in these data. -/
def natural : FiniteScalarIto.Family filtration measure 1 ℕ :=
  BrownianCoordinateVersions.family coordinates (by norm_num) le_rfl contains_null

/-- Any countable noise index is obtained by an injective relabeling
of the constructed countably many channels. -/
def reindex {ι : Type*} [DecidableEq ι] (e : ι ↪ ℕ) : FiniteScalarIto.Family filtration measure 1 ι where
  W i := natural.W (e i)
  adapted i := natural.adapted (e i)
  continuous i := natural.continuous (e i)
  law n a := by
    simpa only [Function.Embedding.apply_eq_iff_eq] using natural.law n (fun i => e (a i))

/-- The original infinite matrix Haar driver is available on a concrete
probability space, with the exact index used by the native SPDE solver. -/
def haar (n : ℕ) : FiniteScalarIto.Family filtration measure 1 (Fin n×FiniteHaar.HaarNode) :=
  reindex ⟨Encodable.encode,Encodable.encode_injective⟩

end SHEStochastic.CanonicalBrownianFamily
