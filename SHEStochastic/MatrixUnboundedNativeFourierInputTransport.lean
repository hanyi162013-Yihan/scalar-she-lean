module

public import SHEStochastic.MatrixUnboundedNativeItoTransport
public import SHEStochastic.MatrixUnboundedFourierInput
public import SHEStochastic.NoiseRestrictionBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedNativeFourierInputTransport
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

private theorem analysis_row (u : Physical (d := Fin n)) :
    (VectorNativeHaarBasis.analysis (n := n)).symm (VectorWhiteCoordinates.analysis u) =
      VectorNativeHaarBasis.equivalence u := by
  apply (VectorNativeHaarBasis.analysis (n := n)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [VectorNativeHaarBasis.analysis,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0)
  (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
  {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (U : ℝ≥0×Ω → Physical (d := Fin n))
  (hU : StronglyMeasurable[F.predictable] U)
  (hEnergy : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))
  {R : ℝ}
  (hBound : ∀ᵐ p ∂energyMeasure μ H,
    ‖VectorNativeHaarBasis.equivalence (U p)‖ ≤ R)

/-- Under exact spatial rescaling, the growing unbounded Fourier input
is the fixed unitary image of the original matrix input. -/
theorem input (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    FourierHeatInput.growingInput F
      (fun p => VectorNativeHaarBasis.equivalence (U p))
      ((VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable hU)
      (MatrixDiffusionRows.holder hG i) hβ hβ1 μ H hBound a m =
      NoiseRestrictionBounds.input
        (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry
        (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1.le U hU hEnergy i a m) := by
  let native := fun p => VectorNativeHaarBasis.equivalence (U p)
  let hnative := (VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable hU
  let unitRow := fun p => StateNoiseCovariance.row (AddCircle.haarAddCircle (T := (1 : ℝ)))
    hβ hβ1.le (MatrixDiffusionRows.holder hG i) (MatrixFourierCoordinates.weight a m) (U p)
  apply Lp.ext
  filter_upwards [FourierHeatInput.growing_ae_trim F native hnative
      (MatrixDiffusionRows.holder hG i) hβ hβ1 μ H hBound a m,
    NoiseRestrictionBounds.input_ae_trim
      (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry
      (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1.le U hU hEnergy i a m),
    MatrixUnboundedFourierInput.input_ae_trim F μ H G hG hβ hβ1.le U hU hEnergy i a m]
    with p hn hm hu
  rw [hn,hm,hu]
  change FourierHeatInput.multiplier H m p •
      FourierHeatRowAverage.row F native hnative
        (MatrixDiffusionRows.holder hG i) hβ hβ1 a m p =
    (VectorNativeHaarBasis.analysis (n := n)).symm
      (FourierHeatInput.multiplier H m p •
        VectorWhiteCoordinates.analysis (unitRow p))
  rw [MatrixUnboundedNativeRowTransport.row F U hU
    (MatrixDiffusionRows.holder hG i) hβ hβ1 a m p,
    map_smul,analysis_row]

/-- Consequently the two full cylindrical Ito integrals of the
unbounded Fourier row are literally equal, not merely equal in law. -/
theorem integral (P : FiniteScalarIto.Family F μ H (Fin n×FiniteHaar.HaarNode))
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (FiniteCylindricalIto.terminalIto P.toCoordinates (VectorNativeHaarBasis.basis (n := n))).integral
      (FourierHeatInput.growingInput F
        (fun p => VectorNativeHaarBasis.equivalence (U p))
        ((VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable hU)
        (MatrixDiffusionRows.holder hG i) hβ hβ1 μ H hBound a m) =
    (FiniteCylindricalIto.terminalIto P.toCoordinates
      (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
      (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1.le U hU hEnergy i a m) := by
  rw [input F μ H G hG hβ hβ1 U hU hEnergy hBound i a m]
  change (restrictNoise
    (FiniteCylindricalIto.terminalIto P.toCoordinates (VectorNativeHaarBasis.basis (n := n)))
    (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry).integral
      (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1.le U hU hEnergy i a m) = _
  rw [MatrixUnboundedNativeItoTransport.terminal P]

end SHEStochastic.MatrixUnboundedNativeFourierInputTransport
