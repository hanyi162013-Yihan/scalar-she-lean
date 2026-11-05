module

public import SHEStochastic.MatrixUnboundedCompletedBeforeExitInput
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.NativeStoppedInputComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCompletedExitIto
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

/-- Before L2 exit, the localized and true global matrix Fourier Ito
integrals are equal on the same completed Brownian realization. -/
theorem integral_eq (H : ℝ≥0) (N : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μc,
      (H : WithTop ℝ≥0) ≤ ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      (FiniteCylindricalIto.terminalIto
        (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
        (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
          (MatrixUnboundedLocalizedInputTransport.unitState S N)
          (MatrixUnboundedLocalizedInputTransport.predictable S N)
          (MatrixUnboundedLocalizedInputTransport.energy S H N) i a m) ω =
      (FiniteCylindricalIto.terminalIto
        (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
        (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
          (MatrixUnboundedCompletedGlobal.state S)
          (MatrixUnboundedCompletedGlobal.predictable S)
          (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m) ω := by
  let J := FiniteCylindricalIto.terminalIto
    (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
    (MatrixPredictableHaarRotation.basis (d := Fin n))
  let u := MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
    (MatrixUnboundedLocalizedInputTransport.unitState S N)
    (MatrixUnboundedLocalizedInputTransport.predictable S N)
    (MatrixUnboundedLocalizedInputTransport.energy S H N) i a m
  let v := MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
    (MatrixUnboundedCompletedGlobal.state S)
    (MatrixUnboundedCompletedGlobal.predictable S)
    (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m
  exact NativeRandomStopLocality.integral_eq_before (Fc) μc H J
    (FiniteCylindricalIto.pastLocality
      (MatrixUnboundedCompletedGlobal.family S H)
      (MatrixPredictableHaarRotation.basis (d := Fin n)))
    (FiniteCylindricalIto.continuousStoppedVersions
      (MatrixUnboundedCompletedGlobal.family S H)
      (MatrixPredictableHaarRotation.basis (d := Fin n)))
    (MatrixUnboundedCompletedGlobal.contains_null S) u v H
    (FiniteItoStoppedVersions.stop_horizon u)
    (FiniteItoStoppedVersions.stop_horizon v)
    (ContinuousNormExit.exit
      (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N)
    (UnboundedL2Localization.exit_stopping (Fc)
      (MatrixUnboundedCompletedLocalField.nativeState S)
      (MatrixUnboundedCompletedLocalField.native_predictable S)
      (MatrixUnboundedCompletedLocalField.native_continuous S) N)
    (MatrixUnboundedCompletedBeforeExitInput.input S H N i a m)

/-- The continuous native heat field and the unbounded global matrix
equation use the same Fourier Ito integral up to L2 exit. -/
theorem native_integral_eq (H : ℝ≥0) (N : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μc,
      (H : WithTop ℝ≥0) ≤ ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
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
            (MatrixUnboundedCompletedLocalField.nativeState S) μc H N) a m) ω =
      (FiniteCylindricalIto.terminalIto
        (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
        (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
          (MatrixUnboundedCompletedGlobal.state S)
          (MatrixUnboundedCompletedGlobal.predictable S)
          (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m) ω := by
  rw [MatrixUnboundedLocalizedInputTransport.integral S H N i a m]
  exact integral_eq S H N i a m

/-- At any earlier observation time in a fixed horizon, the stopped
native convolution row equals the stopped original global matrix row
before the norm exit. -/
theorem native_stopped_integral_eq (H T : ℝ≥0) (N : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μc,
      (T : WithTop ℝ≥0) ≤ ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
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
              (MatrixUnboundedCompletedLocalField.nativeState S) μc H N) a m)) ω =
      (FiniteCylindricalIto.terminalIto
        (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
        (StoppedItoInputs.stop (Fc) μc H T
          (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
            (MatrixUnboundedCompletedGlobal.state S)
            (MatrixUnboundedCompletedGlobal.predictable S)
            (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m)) ω := by
  let J := FiniteCylindricalIto.terminalIto
    (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
    (MatrixPredictableHaarRotation.basis (d := Fin n))
  let u := MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
    (MatrixUnboundedLocalizedInputTransport.unitState S N)
    (MatrixUnboundedLocalizedInputTransport.predictable S N)
    (MatrixUnboundedLocalizedInputTransport.energy S H N) i a m
  let v := MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
    (MatrixUnboundedCompletedGlobal.state S)
    (MatrixUnboundedCompletedGlobal.predictable S)
    (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m
  have hh := NativeStoppedInputComparison.integral_eq_before (Fc) μc H J
    (FiniteCylindricalIto.pastLocality
      (MatrixUnboundedCompletedGlobal.family S H)
      (MatrixPredictableHaarRotation.basis (d := Fin n)))
    (FiniteCylindricalIto.continuousStoppedVersions
      (MatrixUnboundedCompletedGlobal.family S H)
      (MatrixPredictableHaarRotation.basis (d := Fin n)))
    (MatrixUnboundedCompletedGlobal.contains_null S) u v T
    (ContinuousNormExit.exit
      (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N)
    (UnboundedL2Localization.exit_stopping (Fc)
      (MatrixUnboundedCompletedLocalField.nativeState S)
      (MatrixUnboundedCompletedLocalField.native_predictable S)
      (MatrixUnboundedCompletedLocalField.native_continuous S) N)
    (MatrixUnboundedCompletedBeforeExitInput.input S H N i a m)
  rw [MatrixUnboundedLocalizedInputTransport.stopped_integral S H T N i a m]
  exact hh

end SHEStochastic.MatrixUnboundedCompletedExitIto
