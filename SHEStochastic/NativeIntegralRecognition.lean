module

public import SHEStochastic.FiniteCylindricalSimple
public import SHEStochastic.NativeInputEquiv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeIntegralRecognition
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

/-- Mixed pairings on the existing dense simple inputs, together with
the exact second moment, identify a candidate variable with the SAME
native integral. This is Hilbert-space duality, not a martingale
representation premise. -/
theorem integral (r : Process (E := C) F μ H) (M : Lp ℝ 2 μ)
    (hEnergy : ‖M‖^2 = ‖r‖^2)
    (hPair : letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      ∀ s : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H),
        inner ℝ M (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding e s)) =
          inner ℝ (FiniteCylindricalIto.processTransport r) (FiniteCylindricalIto.simpleEmbedding e s)) :
    M = (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let A := (innerSL ℝ M).comp (FiniteCylindricalIto.rawIntegral P.toCoordinates e).toContinuousLinearMap
  let B := innerSL ℝ (FiniteCylindricalIto.processTransport r)
  have he := congrFun ((FiniteCylindricalIto.simpleEmbedding_dense e).equalizer
    A.continuous B.continuous (funext hPair)) (FiniteCylindricalIto.processTransport r)
  change inner ℝ M ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r) =
    inner ℝ (FiniteCylindricalIto.processTransport r) (FiniteCylindricalIto.processTransport r) at he
  rw [real_inner_self_eq_norm_sq, LinearIsometry.norm_map] at he
  have hn := norm_sub_sq_real M ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r)
  rw [LinearIsometry.norm_map, he, hEnergy] at hn
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (M-(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r)]

end SHEStochastic.NativeIntegralRecognition
