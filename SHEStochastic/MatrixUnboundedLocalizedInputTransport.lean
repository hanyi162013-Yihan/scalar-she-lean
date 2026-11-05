module

public import SHEStochastic.MatrixUnboundedNativeFourierInputTransport
public import SHEStochastic.MatrixUnboundedCompletedLocalField
public import SHEStochastic.NoiseRestrictionStop

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedLocalizedInputTransport
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := borel _
local instance : BorelSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration 1)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S

/-- The localized native L2 state, pulled back to the original unit circle. -/
def unitState (N : ℕ) (p : ℝ≥0 × RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Physical (d := Fin n) :=
  (VectorNativeHaarBasis.equivalence (n := n)).symm
    (UnboundedL2Localization.state (MatrixUnboundedCompletedLocalField.nativeState S) N p)

theorem predictable (N : ℕ) : StronglyMeasurable[(Fc).predictable] (unitState S N) :=
  (VectorNativeHaarBasis.equivalence (n := n)).symm.continuous.comp_stronglyMeasurable
    (UnboundedL2Localization.predictable (Fc)
      (MatrixUnboundedCompletedLocalField.nativeState S)
      (MatrixUnboundedCompletedLocalField.native_predictable S) N)

theorem native (N : ℕ) (p : ℝ≥0 × RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    VectorNativeHaarBasis.equivalence (unitState S N p) =
      UnboundedL2Localization.state (MatrixUnboundedCompletedLocalField.nativeState S) N p :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem energy (H : ℝ≥0) (N : ℕ) :
    Integrable (fun p => ‖unitState S N p‖^2) (energyMeasure μc H) := by
  letI : IsFiniteMeasure (energyMeasure μc H) := by
    unfold energyMeasure
    infer_instance
  apply (integrable_const ((N : ℝ)^2)).mono'
  · exact (((predictable S N).mono (predictable_le_product (Fc))).norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := UnboundedL2Localization.norm_bound
      (MatrixUnboundedCompletedLocalField.nativeState S) N p
    rw [← (VectorNativeHaarBasis.equivalence (n := n)).norm_map (unitState S N p),
      native S N p] at *
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The native localized Fourier row is exactly the original matrix row
formed from the pulled-back localized state. -/
theorem input (H : ℝ≥0) (N : ℕ) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    FourierHeatInput.growingInput (Fc)
      (UnboundedL2Localization.state (MatrixUnboundedCompletedLocalField.nativeState S) N)
      (UnboundedL2Localization.predictable (Fc)
        (MatrixUnboundedCompletedLocalField.nativeState S)
        (MatrixUnboundedCompletedLocalField.native_predictable S) N)
      (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H
      (UnboundedL2Localization.history_bound
        (MatrixUnboundedCompletedLocalField.nativeState S) μc H N) a m =
    NoiseRestrictionBounds.input
      (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry
      (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
        (unitState S N) (predictable S N) (energy S H N) i a m) := by
  have hb : ∀ᵐ p ∂energyMeasure μc H,
      ‖VectorNativeHaarBasis.equivalence (unitState S N p)‖ ≤ (N : ℝ) := by
    filter_upwards [UnboundedL2Localization.history_bound
      (MatrixUnboundedCompletedLocalField.nativeState S) μc H N] with p hp
    rw [native S N p]
    exact hp
  simpa only [unitState, LinearIsometryEquiv.apply_symm_apply] using
    MatrixUnboundedNativeFourierInputTransport.input (Fc) μc H G hG hβ hβ1
    (unitState S N) (predictable S N) (energy S H N) hb i a m

/-- The corresponding cylindrical Ito integrals agree on the completed
global probability space for each finite horizon. -/
theorem integral (H : ℝ≥0) (N : ℕ) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (FiniteCylindricalIto.terminalIto
      (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
      (VectorNativeHaarBasis.basis (n := n))).integral
      (FourierHeatInput.growingInput (Fc)
        (UnboundedL2Localization.state (MatrixUnboundedCompletedLocalField.nativeState S) N)
        (UnboundedL2Localization.predictable (Fc)
          (MatrixUnboundedCompletedLocalField.nativeState S)
          (MatrixUnboundedCompletedLocalField.native_predictable S) N)
        (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H
        (UnboundedL2Localization.history_bound
          (MatrixUnboundedCompletedLocalField.nativeState S) μc H N) a m) =
    (FiniteCylindricalIto.terminalIto
      (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
      (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
      (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
        (unitState S N) (predictable S N) (energy S H N) i a m) := by
  have hb : ∀ᵐ p ∂energyMeasure μc H,
      ‖VectorNativeHaarBasis.equivalence (unitState S N p)‖ ≤ (N : ℝ) := by
    filter_upwards [UnboundedL2Localization.history_bound
      (MatrixUnboundedCompletedLocalField.nativeState S) μc H N] with p hp
    rw [native S N p]
    exact hp
  simpa only [unitState, LinearIsometryEquiv.apply_symm_apply] using
    MatrixUnboundedNativeFourierInputTransport.integral (Fc) μc H G hG hβ hβ1
    (unitState S N) (predictable S N) (energy S H N) hb
    (MatrixUnboundedCompletedGlobal.family S H) i a m

/-- The exact noise transport also commutes with stopping at an earlier
observation time within a fixed finite horizon. -/
theorem stopped_integral (H T : ℝ≥0) (N : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (FiniteCylindricalIto.terminalIto
      (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
      (VectorNativeHaarBasis.basis (n := n))).integral
      (StoppedItoInputs.stop (Fc) μc H T
        (FourierHeatInput.growingInput (Fc)
          (UnboundedL2Localization.state (MatrixUnboundedCompletedLocalField.nativeState S) N)
          (UnboundedL2Localization.predictable (Fc)
            (MatrixUnboundedCompletedLocalField.nativeState S)
            (MatrixUnboundedCompletedLocalField.native_predictable S) N)
          (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H
          (UnboundedL2Localization.history_bound
            (MatrixUnboundedCompletedLocalField.nativeState S) μc H N) a m)) =
    (FiniteCylindricalIto.terminalIto
      (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
      (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
      (StoppedItoInputs.stop (Fc) μc H T
        (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
          (unitState S N) (predictable S N) (energy S H N) i a m)) := by
  rw [input S H N i a m]
  rw [← NoiseRestrictionStop.commutes (Fc) μc H T
    (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry]
  change (restrictNoise
    (FiniteCylindricalIto.terminalIto
      (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
      (VectorNativeHaarBasis.basis (n := n)))
    (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry).integral
      (StoppedItoInputs.stop (Fc) μc H T
        (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
          (unitState S N) (predictable S N) (energy S H N) i a m)) = _
  exact congrArg (fun J => J.integral
    (StoppedItoInputs.stop (Fc) μc H T
      (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
        (unitState S N) (predictable S N) (energy S H N) i a m)))
    (MatrixUnboundedNativeItoTransport.terminal
      (MatrixUnboundedCompletedGlobal.family S H))

end SHEStochastic.MatrixUnboundedLocalizedInputTransport
