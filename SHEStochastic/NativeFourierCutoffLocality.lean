module

public import SHEStochastic.NativeUniformFourierPrefix
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.UnboundedJointNativePasting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativeFourierCutoffLocality
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting
open UnboundedJointCanonicalPathMartingale PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)



local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

include hH hnull hEquation hM hu₀ in
theorem physical_bound_before (R : ℕ) :
    ∀ᵐ p ∂energyMeasure μ H,
      (p.1 : WithTop ℝ≥0) < (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R p.2) : WithTop ℝ≥0) →
      ∀ᵐ y ∂haarAddCircle, ‖physical W p y‖ ≤ R := by
  have hg := (Measure.quasiMeasurePreserving_snd (μ := PredictableL2.timeMeasure H) (ν := μ)).ae
    (regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀)
  filter_upwards [hg] with p hp ht
  have htNN : p.1 < AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R p.2) :=
    WithTop.coe_lt_coe.mp ht
  have ht' : (p.1 : ℝ) < (uniformExit H W hcW R p.2).val := htNN
  let t : Time (min H 1) := ⟨p.1, p.1.property, ht'.le.trans (uniformExit H W hcW R p.2).property.2⟩
  have hb := UniformCoefficientExit.before_bound (haarAddCircle (T := 1)) (min H 1) R
    (NativeContinuousPath.path (min H 1) W hcW p.2) hp.1 hp.2 t ht'
  have he : NativeContinuousPath.path (min H 1) W hcW p.2 t = W p.1 p.2 := by
    change W (p.1 : ℝ).toNNReal p.2 = W p.1 p.2
    rw [Real.toNNReal_coe]
  rw [he] at hb
  apply (L2ExtendedUniformNorm.le_ofReal_iff haarAddCircle (physical W p) R (by positivity)).mp
  exact (NativePhysicalState.uniform_norm_push (W p.1 p.2)).trans_le hb

include hH hnull hEquation hM hu₀ in
/-- The localized original Fourier input and the bounded coefficient
cutoff input agree before both actual stopping times. -/
theorem row_agrees (R N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∀ᵐ p ∂energyMeasure μ H,
      (p.1 : WithTop ℝ≥0) < min (exit W N p.2)
        (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R p.2) : WithTop ℝ≥0) →
      UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n p =
        BoundedFourierInput.input F μ H W hW (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
          (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
          (UnboundedCoefficientCutoff.bounded hG R) a n p := by
  have hl := ae_eq_of_ae_eq_trim (FourierHeatInput.growing_ae_trim F
    (UnboundedL2Localization.state (physical W) N)
    (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
    hG hβ hβ1 μ H (UnboundedL2Localization.history_bound (physical W) μ H N) a n)
  filter_upwards [hl, BoundedFourierInput.input_ae F μ H W hW (UnboundedCoefficientCutoff.holder hG R)
    hβ hβ1 (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
      (UnboundedCoefficientCutoff.bounded hG R) a n,
    physical_bound_before F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R]
    with p hl hr hp ht
  change UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n p = _ at hl
  rw [hl, hr, BoundedFourierInput.row]
  apply congrArg (fun v ↦ FourierHeatInput.multiplier H n p • v)
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [FourierHeatRowAverage.row, HolderStateRows.row_operator,
    UnboundedL2Localization.agrees_before_exit (physical W) (physical_continuous W hcW) N p
      (ht.trans_le (min_le_left _ _))]
  exact StateNoiseCovariance.row_congr haarAddCircle hβ hβ1.le hG
    (UnboundedCoefficientCutoff.holder hG R) (NativeFourierHeatCoordinate.weight a n) (physical W p)
    ((hp (ht.trans_le (min_le_right _ _))).mono fun y hy ↦
      (UnboundedCoefficientCutoff.agrees G R hy).symm)

include hH hnull hEquation hM hu₀ in
/-- Existing random-stop locality identifies the SAME native integrals
of the original localized row and its bounded cutoff. -/
theorem integral_agrees (R N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) ≤ min (exit W N ω)
      (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R ω) : WithTop ℝ≥0) →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n)) ω =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW
          (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
          (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
          (UnboundedCoefficientCutoff.bounded hG R) a n)) ω := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  apply NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hnull _ _ T
  · rw [StoppedInputAlgebra.stop_stop, min_self]
  · rw [StoppedInputAlgebra.stop_stop, min_self]
  · exact (exit_stopping F W hW hcW N).min
      (UnboundedNativeUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀
        hH hcW hnull hEquation M hM hu₀ R)
  · filter_upwards [StoppedItoInputs.stop_ae F μ H T
      (UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n),
      StoppedItoInputs.stop_ae F μ H T (BoundedFourierInput.input F μ H W hW
        (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
        (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
        (UnboundedCoefficientCutoff.bounded hG R) a n),
      row_agrees F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R N a n]
      with p hl hr hp ht
    rw [hl, hr]
    by_cases h : p ∈ StoppedItoInputs.before (Ω := Ω) T
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hp ht]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

end SHEStochastic.NativeFourierCutoffLocality
