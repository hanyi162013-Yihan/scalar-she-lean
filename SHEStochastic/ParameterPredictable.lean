module

public import SHE.ContinuousPredictable
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.ParameterPredictable
open MeasureTheory Set
open scoped NNReal

variable {X Ω : Type*} [mX : MeasurableSpace X] [mΩ : MeasurableSpace Ω]

def filtration (F : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 (mX.prod mΩ) where
  seq t := mX.prod (F t)
  mono' _ _ h := sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.mono h))
  le' t := sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le t))

/-- Lift a past-measurable parameter/sample set to a predictable time band. -/
theorem band_set (m : MeasurableSpace Ω) (σ : MeasurableSpace (ℝ≥0 × Ω))
    (s : Set ℝ≥0)
    (hband : ∀ a : Set Ω, MeasurableSet[m] a → MeasurableSet[σ] (s ×ˢ a))
    (A : Set (X × Ω)) (hA : MeasurableSet[mX.prod m] A) :
    MeasurableSet[mX.prod σ] {z : X × (ℝ≥0 × Ω) | z.2.1 ∈ s ∧ (z.1, z.2.2) ∈ A} := by
  letI : MeasurableSpace Ω := m
  induction A, hA using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
  | empty => simpa using (MeasurableSet.empty : MeasurableSet[mX.prod σ] ∅)
  | basic A hA =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hA
    convert ha.prod (hband b hb) using 1
    ext z
    simp only [mem_setOf_eq, mem_prod]
    tauto
  | compl A hA ih =>
    have hwhole : MeasurableSet[mX.prod σ] ((univ : Set X) ×ˢ (s ×ˢ (univ : Set Ω))) :=
      MeasurableSet.univ.prod (hband univ MeasurableSet.univ)
    convert hwhole.diff ih using 1
    ext z
    simp only [mem_setOf_eq, mem_prod, mem_univ, mem_compl_iff, mem_sdiff, true_and, and_true]
    tauto
  | iUnion f _ _ ih =>
    convert MeasurableSet.iUnion ih using 1
    ext z
    simp only [mem_setOf_eq, mem_iUnion, exists_and_left]

/-- Moving the fixed parameter to the sample coordinate preserves the
actual predictable sigma algebras in the direction used by joint versions. -/
theorem transpose (F : Filtration ℝ≥0 mΩ) :
    @Measurable (X × (ℝ≥0 × Ω)) (ℝ≥0 × (X × Ω))
      (mX.prod F.predictable) (filtration (X := X) F).predictable
      (fun z ↦ (z.2.1, (z.1, z.2.2))) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[mX.prod F.predictable]
      {z : X × (ℝ≥0 × Ω) | z.2.1 ∈ ({0} : Set ℝ≥0) ∧ (z.1, z.2.2) ∈ A}
    exact band_set (F 0) F.predictable {0}
      (fun _ ha ↦ measurableSet_predictable_singleton_bot_prod ha) A hA
  · intro t A hA
    change MeasurableSet[mX.prod F.predictable]
      {z : X × (ℝ≥0 × Ω) | z.2.1 ∈ Ioi t ∧ (z.1, z.2.2) ∈ A}
    exact band_set (F t) F.predictable (Ioi t)
      (fun _ ha ↦ measurableSet_predictable_Ioi_prod ha) A hA

end SHEStochastic.ParameterPredictable
