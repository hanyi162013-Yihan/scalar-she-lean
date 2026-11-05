module

public import SHEStochastic.GlobalBoundedHeatLocalization
public import SHE.StoppedInputAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.GlobalBoundedHeatStoppedLocality
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- A future heat target may be stopped at an earlier observation time.
Only that observation time needs to precede the actual state exit. -/
theorem integral_agrees (hc : ∀ sample, Continuous (fun t ↦ U (t, sample)))
    (N : ℕ) (S : ℝ≥0) (hSH : S ≤ H) (x : HeatCircle) (T : ℝ≥0)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) ≤ ContinuousNormExit.exit (fun t sample ↦ U (t, sample)) N sample →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H T
        (UnboundedLocalizedHeatRows.globalRow F U hU hG hβ hβ1 μ H N S hSH x)) sample =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H T
        (GlobalBoundedHeatCoefficientLift.input F U hU hG hβ hβ1.le B hb μ H S hSH x)) sample := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let u := UnboundedLocalizedHeatRows.globalRow F U hU hG hβ hβ1 μ H N S hSH x
  let v := GlobalBoundedHeatCoefficientLift.input F U hU hG hβ hβ1.le B hb μ H S hSH x
  apply NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hnull _ _ T
  · exact (StoppedInputAlgebra.stop_stop F μ H T T u).trans (by rw [min_self])
  · exact (StoppedInputAlgebra.stop_stop F μ H T T v).trans (by rw [min_self])
  · exact UnboundedL2Localization.exit_stopping F U hU hc N
  · filter_upwards [StoppedItoInputs.stop_ae F μ H T u, StoppedItoInputs.stop_ae F μ H T v,
      GlobalBoundedHeatLocalization.row_agrees F U hU hG hβ hβ1 B hb μ H hc N S hSH x]
      with p hu hv hr hp
    rw [hu, hv]
    by_cases ht : (p.1 : ℝ) < T
    · rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) T from ht),
        Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) T from ht)]
      exact hr hp
    · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) T from ht),
        Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) T from ht)]

end SHEStochastic.GlobalBoundedHeatStoppedLocality
