module

public import SHEStochastic.MatrixUnboundedContinuousConvolution
public import SHEStochastic.GlobalLocalizedFourierRemainder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedLocalFourierConvolution
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar HeatParameterCover HeatParameterCoordinates
open HeatParameterPullback GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration 1)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S

/-- Before every L2 exit, each Fourier coefficient of the assembled
vector heat field is exactly the stochastic integral of the original
matrix row evaluated on the localized vector state. -/
theorem coordinate (H : ℝ≥0) (hH : 0<H) (i : Fin n)
    (N : ℕ) (T : ℝ≥0) (hTH : T≤H) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μc,
      (T : WithTop ℝ≥0) < ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      NativeFourierHeatCoordinate.coordinate a m
        (L2EuclideanCoordinates.coordinates ν
          (MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH T hTH) ω) i) =
      Real.exp (-(T : ℝ)*(m : ℝ)^2)*
        (FiniteCylindricalIto.terminalIto
          (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
          (VectorNativeHaarBasis.basis (n := n))).integral
          (StoppedItoInputs.stop (Fc) μc H T
            (FourierHeatInput.growingInput (Fc)
              (UnboundedL2Localization.state
                (MatrixUnboundedCompletedLocalField.nativeState S) N)
              (UnboundedL2Localization.predictable (Fc)
                (MatrixUnboundedCompletedLocalField.nativeState S)
                (MatrixUnboundedCompletedLocalField.native_predictable S) N)
              (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H
              (UnboundedL2Localization.history_bound
                (MatrixUnboundedCompletedLocalField.nativeState S) μc H N) a m)) ω := by
  let U := MatrixUnboundedCompletedLocalField.nativeState S
  have hU := MatrixUnboundedCompletedLocalField.native_predictable S
  let V := UnboundedL2Localization.state U N
  have hV := UnboundedL2Localization.predictable (Fc) U hU N
  have hb := UnboundedL2Localization.history_bound U μc H N
  let Y := MatrixUnboundedContinuousConvolution.rowField S H i
  have hm : ∀ p, Measurable (Y p) :=
    MatrixUnboundedContinuousConvolution.rowField_measurable S H i
  have hc : ∀ ω, Continuous (fun p => Y p ω) :=
    MatrixUnboundedContinuousConvolution.rowField_continuous S H i
  have hl (p : Parameter) : ∀ᵐ ω ∂μc,
      (GlobalHeatParameter.time H p : WithTop ℝ≥0)<
        ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω →
      Y p ω=UnboundedGlobalHeatContinuity.observation (Fc) V hV
        (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H hb
        (MatrixUnboundedCompletedGlobal.family S H)
        (VectorNativeHaarBasis.basis (n := n)) p ω := by
    exact MatrixUnboundedContinuousConvolution.rowField_local S H i N p
  have hs := GlobalLocalizedFourierRemainder.coordinate (Fc) V hV
    (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H hH hb
    (MatrixUnboundedCompletedGlobal.family S H) (VectorNativeHaarBasis.basis (n := n))
    Y hm hc (ContinuousNormExit.exit (fun t ω => U (t,ω)) N)
    (UnboundedL2Localization.exit_stopping (Fc) U hU
      (MatrixUnboundedCompletedLocalField.native_continuous S) N)
    hl T hTH a m
  simpa only [Y,MatrixUnboundedContinuousConvolution.component,
    MatrixUnboundedContinuousConvolution.scalarRemainder] using hs

end SHEStochastic.MatrixUnboundedLocalFourierConvolution
