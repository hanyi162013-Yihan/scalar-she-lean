module

public import SHEStochastic.NativeRowRepresentatives
public import SHE.PredictableClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeDeterministicRows
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "ν" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

/-- The native predictable measure retains the original deterministic clock. -/
theorem time_preserving : @MeasurePreserving (ℝ≥0 × Ω) ℝ≥0 F.predictable _
    Prod.fst ν νt := by
  have hp (A : Set ℝ≥0) (hA : MeasurableSet A) :
      (energyMeasure μ H) (Prod.fst ⁻¹' A) = νt A := by
    have hm : MeasurePreserving (Prod.fst : ℝ≥0 × Ω → ℝ≥0)
        ((timeMeasure H).prod μ) (timeMeasure H) := measurePreserving_fst
    rw [show energyMeasure μ H = (timeMeasure H).prod μ from rfl,
      hm.measure_preimage hA.nullMeasurableSet, timeMeasure_eq]
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  refine ⟨PredictableClock.time_measurable F, ?_⟩
  ext A hA
  rw [Measure.map_apply (PredictableClock.time_measurable F) hA,
    NativeRowRepresentatives.inputMeasure_eq,
    trim_measurableSet_eq (predictable_le_product F)
      ((PredictableClock.time_measurable F) hA)]
  exact hp A hA

/-- Square integrability of a deterministic representative is inherited
from the already constructed native input. -/
theorem memLp (S : Lp C 2 ν) (D : ℝ≥0 → C) (hD : StronglyMeasurable D)
    (hS : S =ᵐ[ν] (fun p : ℝ≥0 × Ω => D p.1)) : MemLp D 2 νt := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hm := time_preserving (F := F) (μ := μ) (H := H)
  have hprod : MemLp (D ∘ Prod.fst) 2 ν := MemLp.ae_eq hS (Lp.memLp S)
  have hh := (memLp_map_measure_iff
    (hm.map_eq.symm ▸ hD.aestronglyMeasurable) hm.aemeasurable).2 hprod
  rwa [hm.map_eq] at hh

theorem integrable_inner (D E : ℝ≥0 → C) (hD : MemLp D 2 νt) (hE : MemLp E 2 νt) :
    Integrable (fun r => inner ℝ (D r) (E r)) νt := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hD.toLp D) (hE.toLp E)).congr
  filter_upwards [hD.coeFn_toLp, hE.coeFn_toLp] with r hd he
  rw [hd, he]

/-- The native input Gram is the literal time integral of its deterministic
row covariance, including repeated observations and singular Gram matrices. -/
theorem pairing (S T : Lp C 2 ν) (D E : ℝ≥0 → C)
    (hD : StronglyMeasurable D) (hE : StronglyMeasurable E)
    (hDp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => D p.1))
    (hEp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => E p.1))
    (hS : S =ᵐ[ν] (fun p : ℝ≥0 × Ω => D p.1))
    (hT : T =ᵐ[ν] (fun p : ℝ≥0 × Ω => E p.1)) :
    inner ℝ S T = ∫ r, inner ℝ (D r) (E r) ∂νt := by
  rw [L2.inner_def]
  calc
    _ = ∫ p, inner ℝ (D p.1) (E p.1) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hS, hT] with p hs ht
      rw [hs, ht]
    _ = _ := HilbertSimpleEnergyDefect.integral_time_profile _
      (integrable_inner D E (memLp S D hD hS) (memLp T E hE hT)) (hDp.inner hEp)

theorem time_positive : ∀ᵐ p ∂ν, 0 < p.1 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hh : ∀ᵐ r ∂νt, r ∈ Set.Ioc 0 H := ae_restrict_mem measurableSet_Ioc
  exact ((time_preserving (F := F) (μ := μ) (H := H)).quasiMeasurePreserving.ae hh).mono
    (fun _ h => h.1)

/-- Deterministic native rows give their joint Gaussian law directly.
This common constructor serves bounded spatial tests and point heat rows. -/
theorem gaussian {ι : Type*} [Countable ι] [DecidableEq ι] {n : ℕ}
    (N : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (S : Fin n → Lp C 2 ν) (D : Fin n → ℝ≥0 → C)
    (hD : ∀ i, StronglyMeasurable (D i))
    (hDp : ∀ i, StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => D i p.1))
    (hS : ∀ i, S i =ᵐ[ν] (fun p : ℝ≥0 × Ω => D i p.1)) :
    HasLaw (HilbertGaussianVector.nativeVector N e S)
      (multivariateGaussian 0 (Matrix.gram ℝ S)) μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply (HilbertGaussianVector.law_and_independent N e 0 (show 0 ≤ H from zero_le) S _ _).1
  · intro i
    exact (time_positive (F := F) (μ := μ) (H := H)).mono
      fun p hp h => False.elim (not_le_of_gt hp h)
  · apply HilbertGaussianVector.profiles_of_gram S D
    · intro i
      exact memLp (S i) (D i) (hD i) (hS i)
    · exact hDp
    · filter_upwards [ae_all_iff.mpr hS] with p hp
      intro i j
      rw [hp i,hp j]

end SHEStochastic.NativeDeterministicRows
