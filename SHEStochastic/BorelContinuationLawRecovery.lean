module

public import SHEStochastic.BorelObservablePath
public import SHEStochastic.StoppedContinuationMeasure
public import SHEStochastic.BorelStoppedLawLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BorelContinuationLawRecovery
open MeasureTheory ProbabilityTheory StoppedPathPasting
open scoped NNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (H : ℝ≥0) (a : E → ℝ) (ha : Measurable a) (R : ℝ)
  (X : Ω → Path H E) (hX : Measurable X)

/-- Distributional recovery for a merely Borel state observable, such
as the extended uniform norm expressed on L2. Continuity is required
only almost surely along the original and constructed solution paths.
The recovery functional itself is globally Borel. -/
theorem stopped_law (μ : Measure Ω) [SFinite μ]
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ]
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ a (X ω t)))
    (hp : ∀ᵐ z ∂StoppedContinuationMeasure.joint H X
      (fun ω ↦ BorelObservablePath.exit H a R (X ω)) hX
      ((BorelObservablePath.measurable_exit H a ha R).comp hX) μ κ,
      Continuous (fun t ↦ a (StoppedContinuationMeasure.value H X
        (fun ω ↦ BorelObservablePath.exit H a R (X ω)) z t))) :
    (StoppedContinuationMeasure.law H X (fun ω ↦ BorelObservablePath.exit H a R (X ω)) hX
      ((BorelObservablePath.measurable_exit H a ha R).comp hX) μ κ).map
        (BorelObservablePath.stopped H a R) = μ.map (fun ω ↦ BorelObservablePath.stopped H a R (X ω)) := by
  let r : Ω → Time H := fun ω ↦ BorelObservablePath.exit H a R (X ω)
  have hr : Measurable r := (BorelObservablePath.measurable_exit H a ha R).comp hX
  let ν := StoppedContinuationMeasure.joint H X r hX hr μ κ
  have hf : MeasurePreserving Prod.fst ν μ := by
    refine ⟨measurable_fst, ?_⟩
    change (μ ⊗ₘ StoppedContinuationMeasure.continuation H X r hX hr κ).fst = μ
    exact Measure.fst_compProd μ _
  have hm : Measurable (fun ω ↦ BorelObservablePath.stopped H a R (X ω)) :=
    (BorelObservablePath.measurable_stopped H a ha R).comp hX
  have he : (fun z : Ω × Path H E ↦ BorelObservablePath.stopped H a R
      (StoppedContinuationMeasure.value H X r z)) =ᵐ[ν]
        fun z ↦ BorelObservablePath.stopped H a R (X z.1) := by
    filter_upwards [hf.quasiMeasurePreserving.ae hc, hp] with z hc hz
    exact BorelObservablePath.stopped_paste H a R (X z.1) z.2 hc hz
  change (ν.map (StoppedContinuationMeasure.value H X r)).map (BorelObservablePath.stopped H a R) = _
  rw [Measure.map_map (BorelObservablePath.measurable_stopped H a ha R)
    (StoppedContinuationMeasure.measurable_value H X r hX hr)]
  calc
    _ = ν.map (fun z ↦ BorelObservablePath.stopped H a R (X z.1)) := Measure.map_congr he
    _ = (ν.map Prod.fst).map (fun ω ↦ BorelObservablePath.stopped H a R (X ω)) :=
      (Measure.map_map hm measurable_fst).symm
    _ = _ := by rw [hf.map_eq]

/-- Equality of the constructed bounded continuation laws at every
cutoff gives equality of the original unbounded path laws. The remaining
SPDE task is to verify that those constructed laws solve the bounded
equation, then apply its proved uniqueness theorem. -/
theorem laws_eq {Ω' : Type*} [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Y : Ω' → Path H E) (hY : Measurable Y)
    (κ : ℕ → Kernel E (Path H E)) [∀ n, IsMarkovKernel (κ n)]
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ a (X ω t)))
    (hcY : ∀ᵐ ω ∂ν, Continuous (fun t ↦ a (Y ω t)))
    (hpX : ∀ n : ℕ, ∀ᵐ z ∂StoppedContinuationMeasure.joint H X
      (fun ω ↦ BorelObservablePath.exit H a n (X ω)) hX
      ((BorelObservablePath.measurable_exit H a ha n).comp hX) μ (κ n),
      Continuous (fun t ↦ a (StoppedContinuationMeasure.value H X
        (fun ω ↦ BorelObservablePath.exit H a n (X ω)) z t)))
    (hpY : ∀ n : ℕ, ∀ᵐ z ∂StoppedContinuationMeasure.joint H Y
      (fun ω ↦ BorelObservablePath.exit H a n (Y ω)) hY
      ((BorelObservablePath.measurable_exit H a ha n).comp hY) ν (κ n),
      Continuous (fun t ↦ a (StoppedContinuationMeasure.value H Y
        (fun ω ↦ BorelObservablePath.exit H a n (Y ω)) z t)))
    (same : ∀ n : ℕ, StoppedContinuationMeasure.law H X
      (fun ω ↦ BorelObservablePath.exit H a n (X ω)) hX
      ((BorelObservablePath.measurable_exit H a ha n).comp hX) μ (κ n) =
        StoppedContinuationMeasure.law H Y (fun ω ↦ BorelObservablePath.exit H a n (Y ω)) hY
          ((BorelObservablePath.measurable_exit H a ha n).comp hY) ν (κ n)) :
    μ.map X = ν.map Y := by
  apply BorelStoppedLawLimit.laws_eq H a ha μ ν X Y hX hY
  intro n
  have hx := stopped_law H a ha n X hX μ (κ n) hcX (hpX n)
  have hy := stopped_law H a ha n Y hY ν (κ n) hcY (hpY n)
  exact hx.symm.trans ((congrArg (fun m : Measure (Path H E) ↦ m.map (BorelObservablePath.stopped H a n))
    (same n)).trans hy)

end SHEStochastic.BorelContinuationLawRecovery
