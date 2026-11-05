module

public import SHEStochastic.NativeBoundedWeakLimit
public import SHEStochastic.CanonicalInitialLaw
public import SHE.ConditionalInitialState

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.CanonicalInitialKernel
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)
  (Q : Measure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H)) [IsProbabilityMeasure Q]

def initialLaw : Measure E := Q.map (state H 0)

instance : IsProbabilityMeasure (initialLaw H Q) :=
  (Measure.isProbabilityMeasure_map_iff
    ((state_adapted (E := E) (ι := ι) H 0).mono ((filtration H).le 0) le_rfl).aemeasurable).mpr inferInstance

/-- Condition one constructed random-initial law at its initial state.
This provides a Borel kernel without a selection of solutions at every state. -/
def kernel : Kernel E (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :=
  condDistrib id (state H 0) Q

instance : IsMarkovKernel (kernel H Q) := by unfold kernel; infer_instance

theorem matching_initial : ∀ᵐ z ∂initialLaw H Q, ∀ᵐ x ∂kernel H Q z, state H 0 x = z := by
  have hm : Measurable (state (E := E) (ι := ι) H 0) :=
    (state_adapted H 0).mono ((filtration H).le 0) le_rfl
  exact ConditionalInitialState.known_state Q (state H 0) id hm measurable_id
    (state H 0) id hm measurable_id (Filter.Eventually.of_forall fun _ ↦ rfl)

theorem retains (p : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H → Prop)
    (hp : MeasurableSet {x | p x}) (hQ : ∀ᵐ x ∂Q, p x) :
    ∀ᵐ z ∂initialLaw H Q, ∀ᵐ x ∂kernel H Q z, p x := by
  have hm : Measurable (state (E := E) (ι := ι) H 0) :=
    (state_adapted H 0).mono ((filtration H).le 0) le_rfl
  apply Measure.ae_ae_of_ae_compProd (μ := initialLaw H Q) (κ := kernel H Q)
    (p := fun z ↦ p z.2)
  change ∀ᵐ z ∂(Q.map (state H 0)) ⊗ₘ condDistrib id (state H 0) Q, p z.2
  rw [compProd_map_condDistrib hm.aemeasurable measurable_id.aemeasurable]
  exact (ae_map_iff (hm.prodMk measurable_id).aemeasurable (measurable_snd hp)).mpr hQ

theorem reconstruct : ((initialLaw H Q) ⊗ₘ kernel H Q).map Prod.snd = Q := by
  have hm : Measurable (state (E := E) (ι := ι) H 0) :=
    (state_adapted H 0).mono ((filtration H).le 0) le_rfl
  change ((Q.map (state H 0)) ⊗ₘ condDistrib id (state H 0) Q).map Prod.snd = Q
  rw [compProd_map_condDistrib hm.aemeasurable measurable_id.aemeasurable,
    Measure.map_map measurable_snd (hm.prodMk measurable_id)]
  exact Measure.map_id

theorem initialLaw_eq_of_joint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : Ω → E) (hξ : Measurable ξ)
    (hjoint : Q.map (CanonicalInitialLaw.initial H) =
      μ.map (fun sample ↦ (ξ sample, fun _ : ι ↦ (0 : ℝ)))) :
    initialLaw H Q = μ.map ξ := by
  have hh := congrArg (fun ν : Measure (E × (ι → ℝ)) ↦ ν.map Prod.fst) hjoint
  rw [Measure.map_map measurable_fst (CanonicalInitialLaw.continuous_initial H).measurable,
    Measure.map_map measurable_fst (hξ.prodMk measurable_const)] at hh
  have he : Prod.fst ∘ CanonicalInitialLaw.initial (E := E) (ι := ι) H = state H 0 := by
    funext x
    simp [CanonicalInitialLaw.initial, state, clock, StoppedPathPasting.origin]
  rw [he] at hh
  exact hh

theorem driver_initial (hzero : ∀ i, coordinate H i 0 =ᵐ[Q] fun _ ↦ (0 : ℝ)) :
    ∀ᵐ z ∂initialLaw H Q, ∀ᵐ x ∂kernel H Q z, ∀ i, coordinate H i 0 x = 0 := by
  have hi (i : ι) := retains H Q (fun x ↦ coordinate H i 0 x = 0)
    (measurableSet_eq_fun ((coordinate_adapted H i 0).mono ((filtration H).le 0) le_rfl)
      measurable_const) (hzero i)
  filter_upwards [ae_all_iff.mpr hi] with z hz
  exact ae_all_iff.mpr hz

end SHEStochastic.CanonicalInitialKernel
