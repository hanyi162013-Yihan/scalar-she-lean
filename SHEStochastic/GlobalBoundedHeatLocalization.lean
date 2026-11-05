module

public import SHEStochastic.GlobalBoundedHeatCoefficientLift
public import SHEStochastic.UnboundedLocalizedHeatRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalBoundedHeatLocalization
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

include hb in
theorem row_agrees (hc : ∀ sample, Continuous (fun t ↦ U (t, sample)))
    (N : ℕ) (T : ℝ≥0) (hTH : T ≤ H) (x : HeatCircle) :
    ∀ᵐ p ∂energyMeasure μ H,
      (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit (fun t sample ↦ U (t, sample)) N p.2 →
        UnboundedLocalizedHeatRows.globalRow F U hU hG hβ hβ1 μ H N T hTH x p =
          GlobalBoundedHeatCoefficientLift.input F U hU hG hβ hβ1.le B hb μ H T hTH x p := by
  filter_upwards [UnboundedLocalizedHeatRows.globalRow_ae F U hU hG hβ hβ1 μ H N T hTH x,
    GlobalBoundedHeatCoefficientLift.input_ae F U hU hG hβ hβ1.le B hb μ H T hTH x] with p hl hr hp
  rw [hl, hr]
  apply Lp.ext
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [HolderStateRows.row_ae (UnboundedL2Localization.state U N)
    (UnboundedL2Localization.predictable F U hU N) hG hβ hβ1.le
      (UnboundedHeatFamily.kernelFamily T x) p,
    BoundedHeatCoefficientLift.family_ae F U hU hG hβ hβ1.le B hb T x p] with y hl hr
  change HolderStateRows.row _ _ _ _ _ _ p y = _
  rw [hl, hr, UnboundedL2Localization.agrees_before_exit U hc N p hp]
  rfl

/-- Uniform bounded-coefficient convolution and the original localized
convolution have the same native terminal values before the actual exit. -/
theorem integral_agrees (hc : ∀ sample, Continuous (fun t ↦ U (t, sample)))
    (N : ℕ) (T : ℝ≥0) (hTH : T ≤ H) (x : HeatCircle)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) ≤ ContinuousNormExit.exit (fun t sample ↦ U (t, sample)) N sample →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (UnboundedLocalizedHeatRows.globalRow F U hU hG hβ hβ1 μ H N T hTH x) sample =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (GlobalBoundedHeatCoefficientLift.input F U hU hG hβ hβ1.le B hb μ H T hTH x) sample := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  apply NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hnull _ _ T
  · exact UnboundedFiniteHorizonInput.input_stop F _ _ hG hβ hβ1 μ H T hTH x _
  · exact GlobalBoundedHeatCoefficientLift.input_stop F U hU hG hβ hβ1.le B hb μ H T hTH x
  · exact UnboundedL2Localization.exit_stopping F U hU hc N
  · exact row_agrees F U hU hG hβ hβ1 B hb μ H hc N T hTH x

end SHEStochastic.GlobalBoundedHeatLocalization
