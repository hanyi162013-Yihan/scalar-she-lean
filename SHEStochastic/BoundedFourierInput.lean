module

public import SHEStochastic.UnboundedNativeFourierEquation
public import SHEStochastic.StateNoiseCovariance
public import SHEStochastic.NativeBandMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.BoundedFourierInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance

def row (p : ℝ≥0 × Ω) : Lp V 2 (haarAddCircle (T := 2 * Real.pi)) :=
  FourierHeatInput.multiplier H n p •
    StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight a n) (physical W p)

include hW in
theorem predictable : StronglyMeasurable[F.predictable] (row H W hG hβ hβ1 a n) :=
  (FourierHeatInput.multiplier_measurable F H n).smul
    ((StateNoiseCovariance.row_continuous haarAddCircle hβ hβ1.le hG (weight a n)).comp_stronglyMeasurable
      (physical_predictable F W hW))

def cap : ℝ≥0 := ⟨Real.exp ((H : ℝ)*(n : ℝ)^2)*‖a‖*B, by positivity⟩

include hb in
theorem norm_bound (p : ℝ≥0 × Ω) : ‖row H W hG hβ hβ1 a n p‖ ≤ cap H B a n := by
  rw [row, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ Real.exp ((H : ℝ)*(n : ℝ)^2) * (‖weight a n‖*B) :=
      mul_le_mul (FourierHeatInput.multiplier_bound H n p)
        (StateNoiseCovariance.row_bound haarAddCircle hβ hβ1.le hG (weight a n) B B.property hb _)
        (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp ((H : ℝ)*(n : ℝ)^2) * (‖a‖*B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (weight_norm_bound a n) B.property)
        (Real.exp_pos _).le
    _ = _ := by
      change Real.exp ((H : ℝ)*(n : ℝ)^2)*(‖a‖*(B : ℝ)) =
        Real.exp ((H : ℝ)*(n : ℝ)^2)*‖a‖*(B : ℝ)
      ring

def input : Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (MemLp.of_bound (predictable F H W hW hG hβ hβ1 a n).aestronglyMeasurable
    (cap H B a n) (Filter.Eventually.of_forall (norm_bound H W hG hβ hβ1 B hb a n))).toLp _

theorem input_ae_trim : input F μ H W hW hG hβ hβ1 B hb a n =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
    row H W hG hβ hβ1 a n := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (MemLp.of_bound (μ := (energyMeasure μ H).trim (predictable_le_product F))
    (predictable F H W hW hG hβ hβ1 a n).aestronglyMeasurable
    (cap H B a n) (Filter.Eventually.of_forall (norm_bound H W hG hβ hβ1 B hb a n))).coeFn_toLp

theorem input_ae : input F μ H W hW hG hβ hβ1 B hb a n =ᵐ[energyMeasure μ H]
    row H W hG hβ hβ1 a n :=
  ae_eq_of_ae_eq_trim (input_ae_trim F μ H W hW hG hβ hβ1 B hb a n)

/-- The common bound depends only on the coefficient cap, the Fourier
test and the horizon. It is independent of the initial state and the
coefficient's Hölder seminorm. -/
theorem input_bound : ∀ᵐ p ∂FiniteScalarIto.inputMeasure F μ H,
    ‖input F μ H W hW hG hβ hβ1 B hb a n p‖ ≤ cap H B a n := by
  rw [NativeRowRepresentatives.inputMeasure_eq]
  filter_upwards [input_ae_trim F μ H W hW hG hβ hβ1 B hb a n] with p hp
  rw [hp]
  exact norm_bound H W hG hβ hβ1 B hb a n p

include hb in
theorem agrees_before (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (N : ℕ) :
    ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < exit W N p.2 →
      UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n p =
        input F μ H W hW hG hβ hβ1 B hb a n p := by
  have hl := ae_eq_of_ae_eq_trim (FourierHeatInput.growing_ae_trim F
    (UnboundedL2Localization.state (physical W) N)
    (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
    hG hβ hβ1 μ H (UnboundedL2Localization.history_bound (physical W) μ H N) a n)
  filter_upwards [hl, input_ae F μ H W hW hG hβ hβ1 B hb a n] with p hl hr hp
  rw [hr]
  change UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n p = _ at hl
  rw [hl]
  apply congrArg (fun v ↦ FourierHeatInput.multiplier H n p • v)
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [FourierHeatRowAverage.row, HolderStateRows.row_operator,
    UnboundedL2Localization.agrees_before_exit (physical W) (physical_continuous W hcW) N p hp]
  rfl

/-- The actual localized equation and the uniformly bounded Fourier
input have the same native integral before the original L2 exit. -/
theorem integral_agrees {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (N : ℕ) (T : ℝ≥0) :
    ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) ≤ exit W N sample →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T
          (UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n)) sample =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (input F μ H W hW hG hβ hβ1 B hb a n)) sample := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  apply NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hnull _ _ T
  · rw [StoppedInputAlgebra.stop_stop, min_self]
  · rw [StoppedInputAlgebra.stop_stop, min_self]
  · exact exit_stopping F W hW hcW N
  · filter_upwards [StoppedItoInputs.stop_ae F μ H T
      (UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N a n),
      StoppedItoInputs.stop_ae F μ H T (input F μ H W hW hG hβ hβ1 B hb a n),
      agrees_before F μ H W hW hG hβ hβ1 B hb a n hcW N] with p hl hr hp ht
    rw [hl, hr]
    by_cases h : p ∈ StoppedItoInputs.before (Ω := Ω) T
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hp ht]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

end SHEStochastic.BoundedFourierInput
