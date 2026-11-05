module

public import SHEStochastic.SimpleProcessLinearMap
public import SHEStochastic.FiniteCylindricalSimple

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.HilbertSimpleInputs
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- Bounded predictable simple rows supported before the fixed horizon. -/
def bounded : Submodule ℝ (SimpleProcess E F) where
  carrier := {V | ∀ p ∈ V.value.support, p.2 ≤ H}
  add_mem' {V W} hV hW p hp := by
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
    · exact hV p h
    · exact hW p h
  zero_mem' p hp := absurd hp (by simp)
  smul_mem' c V hV p hp := hV p (Finsupp.support_smul hp)

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

theorem memLp (V : SimpleProcess E F) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    MemLp (Function.uncurry ⇑V) 2 ν := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  haveI : IsFiniteMeasure ν := by
    unfold FiniteScalarIto.inputMeasure
    infer_instance
  obtain ⟨K, hK⟩ := V.coe_bounded
  exact MemLp.of_bound V.isStronglyPredictable.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun p ↦ hK p.1 p.2)

def embedding : bounded (E := E) F H →ₗ[ℝ] Lp E 2 ν := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact
    { toFun := fun V ↦ (memLp F μ H V.val).toLp (Function.uncurry ⇑V.val)
      map_add' := fun V W ↦ by
        apply Lp.ext
        filter_upwards [(memLp F μ H (V + W).val).coeFn_toLp,
          (memLp F μ H V.val).coeFn_toLp, (memLp F μ H W.val).coeFn_toLp,
          Lp.coeFn_add ((memLp F μ H V.val).toLp _) ((memLp F μ H W.val).toLp _)]
          with p ha hv hw hs
        rw [ha, hs]
        simp only [Pi.add_apply]
        rw [hv, hw]
        exact congrFun (congrFun (SimpleProcess.coe_add V.val W.val) p.1) p.2
      map_smul' := fun c V ↦ by
        apply Lp.ext
        filter_upwards [(memLp F μ H (c • V).val).coeFn_toLp,
          (memLp F μ H V.val).coeFn_toLp,
          Lp.coeFn_smul c ((memLp F μ H V.val).toLp _)] with p ha hv hs
        rw [RingHom.id_apply, ha, hs]
        simp only [Pi.smul_apply]
        rw [hv]
        exact congrFun (congrFun (SimpleProcess.coe_smul c V.val) p.1) p.2 }

theorem embedding_ae (V : bounded (E := E) F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    embedding F μ H V =ᵐ[ν] Function.uncurry ⇑V.val := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (memLp F μ H V.val).coeFn_toLp

variable {F H}

/-- One left-adapted Hilbert-valued time cell, kept as an ordinary
simple process so its integral and partition identities can be reused. -/
def step (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) (R : Ω → E)
    (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) :
    bounded (E := E) F H :=
  ⟨{ valueBot := 0
     value := Finsupp.single (s, t) R
     le_of_mem_support_value := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       exact hst
     measurable_valueBot := measurable_const
     measurable_value' := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]
       exact hR.measurable
     bounded_valueBot := ⟨0, by simp⟩
     bounded_value := ⟨K, fun p hp ω ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]
       exact hK ω⟩ },
   fun p hp ↦ by
     obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
     exact htH⟩

@[simp] theorem step_apply (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) (R : Ω → E)
    (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K)
    (r : ℝ≥0) (ω : Ω) :
    (step s t hst htH R hR K hK).val r ω =
      (Set.Ioc s t).indicator (fun _ ↦ R ω) r := by
  simp [step, SimpleProcess.apply_eq, Finsupp.sum_single_index]

def map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (L : E →L[ℝ] G) (V : bounded (E := E) F H) : bounded (E := G) F H :=
  ⟨SimpleProcessLinearMap.map L V.val,
    fun p hp ↦ V.property p (SimpleProcessLinearMap.support_map L V.val hp)⟩

theorem embedding_map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (L : E →L[ℝ] G) (V : bounded (E := E) F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    embedding F μ H (map L V) = L.compLpL 2 ν (embedding F μ H V) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  filter_upwards [embedding_ae F μ H (map L V),
    L.coeFn_compLpL (embedding F μ H V), embedding_ae F μ H V] with p ha hb hv
  rw [ha, hb, hv]
  exact SimpleProcessLinearMap.apply_map L V.val p.1 p.2

theorem embedding_scalar (V : FiniteScalarIto.Simple F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    embedding F μ H V = FiniteScalarIto.embedding F μ H V := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rfl

section Density
variable {C ι : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] [Countable ι] [DecidableEq ι]

/-- Hilbert-valued bounded predictable simple rows are dense, using the
already proved scalar and cylindrical density rather than a second
predictable-sigma-algebra approximation argument. -/
theorem embedding_dense (e : HilbertBasis ι ℝ C) :
    DenseRange (embedding (E := C) F μ H) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hi (v : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
      FiniteCylindricalIto.simpleEmbedding (μ := μ) e v ∈ LinearMap.range (embedding (E := C) F μ H) := by
    induction v using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (LinearMap.range (embedding (E := C) F μ H)).zero_mem
    | single i v =>
        rw [FiniteCylindricalIto.simpleEmbedding_single]
        refine ⟨map (ColumnsHilbertSum.unit e i).toContinuousLinearMap v, ?_⟩
        rw [embedding_map, embedding_scalar]
        rfl
    | add v w hv hw =>
        rw [map_add]
        exact (LinearMap.range (embedding (E := C) F μ H)).add_mem hv hw
  apply (FiniteCylindricalIto.simpleEmbedding_dense (F := F) (μ := μ) (H := H) e).mono
  rintro x ⟨v, rfl⟩
  exact hi v
end Density

end SHEStochastic.HilbertSimpleInputs
