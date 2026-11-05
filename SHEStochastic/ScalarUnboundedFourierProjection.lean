module

public import SHEStochastic.ScalarUnboundedFourierRow

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnboundedFourierProjection
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar
  MatrixInfiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)
local notation "Vec" => Physical (d := Fin 1)
local notation "Noise" => Lp ℝ 2 ν₂
local notation "Input₁" => Input (d := Fin 1)
local notation "comp₀" => VectorHeatObservation.component (0 : Fin 1)
local notation "L" => ScalarUnboundedFourierRow.noiseEquiv
local notation "G" => ScalarUnboundedOneDimensional.coefficient
local instance : SecondCountableTopology Vec := Lp.SecondCountableTopology
local instance : MeasurableSpace Vec := borel _
local instance : BorelSpace Vec := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  (L).toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Input₁ := borel _
local instance : BorelSpace Input₁ := ⟨rfl⟩

def basis : HilbertBasis (Fin 1 × HaarNode) ℝ Noise :=
  NativeNoiseEquivalence.basis L MatrixPredictableHaarRotation.basis

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (U : ℝ≥0 × Ω → Vec) (hU : StronglyMeasurable[F.predictable] U)
  (hEnergy : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))

/-- The original scalar growing Fourier row on the projected state. -/
def row (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0 × Ω) : Noise :=
  FourierHeatInput.multiplier H n p • StateNoiseCovariance.row ν₂ hβ hβ₁ hg
    (NativeFourierHeatCoordinate.weight a n) (NativePhysicalState.push (comp₀ (U p)))

def input (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Process (E := Noise) F μ H :=
  NoiseRestrictionBounds.input (L).symm.toLinearIsometry
    (MatrixUnboundedFourierInput.input F μ H (G g) (ScalarUnboundedOneDimensional.holder hg)
      hβ hβ₁ U hU hEnergy 0 a n)

theorem input_ae (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    input hg hβ hβ₁ U hU hEnergy a n =ᵐ[energyMeasure μ H]
      row (H := H) hg hβ hβ₁ U a n := by
  let v := MatrixUnboundedFourierInput.input F μ H (G g) (ScalarUnboundedOneDimensional.holder hg)
    hβ hβ₁ U hU hEnergy 0 a n
  filter_upwards [ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim (L).symm.toLinearIsometry v),
    MatrixUnboundedFourierInput.input_ae F μ H (G g) (ScalarUnboundedOneDimensional.holder hg)
      hβ hβ₁ U hU hEnergy 0 a n] with p hp hv
  change input hg hβ hβ₁ U hU hEnergy a n p = (L).symm (v p) at hp
  change v p = _ at hv
  rw [hp,hv]
  apply (L).injective
  rw [LinearIsometryEquiv.apply_symm_apply,row,LinearIsometryEquiv.map_smul]
  rw [ScalarUnboundedFourierRow.row hg hβ hβ₁]
  rfl

private theorem stopped_input (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    NoiseRestrictionBounds.input (L).toLinearIsometry
      (StoppedItoInputs.stop F μ H t (input hg hβ hβ₁ U hU hEnergy a n)) =
    StoppedItoInputs.stop F μ H t
      (MatrixUnboundedFourierInput.input F μ H (G g) (ScalarUnboundedOneDimensional.holder hg)
        hβ hβ₁ U hU hEnergy 0 a n) := by
  let v := MatrixUnboundedFourierInput.input F μ H (G g) (ScalarUnboundedOneDimensional.holder hg)
    hβ hβ₁ U hU hEnergy 0 a n
  let u := input hg hβ hβ₁ U hU hEnergy a n
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim (L).toLinearIsometry
      (StoppedItoInputs.stop F μ H t u)),
    StoppedItoInputs.stop_ae F μ H t u,StoppedItoInputs.stop_ae F μ H t v,
    ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim (L).symm.toLinearIsometry v)]
      with p hmap hu hv huv
  change u p = (L).symm (v p) at huv
  rw [hmap,hu,hv]
  by_cases h : p ∈ StoppedItoInputs.before (Ω := Ω) t
  · rw [Set.indicator_of_mem h,Set.indicator_of_mem h,huv]
    exact (L).apply_symm_apply _
  · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h]
    exact (L).map_zero

/-- The actual projected scalar stochastic Fourier identity uses the
same stopped Brownian integrals, after a fixed unitary basis change. -/
theorem equation (P : FiniteScalarIto.Family F μ H (Fin 1 × HaarNode)) (Z : Ω → Vec)
    (heq : MatrixUnboundedFourierPullback.Equation (F := F) (μ := μ) (H := H)
      (G g) (ScalarUnboundedOneDimensional.holder hg) hβ hβ₁ U hU hEnergy P Z)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t≤H) :
    (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2) * NativeFourierHeatCoordinate.coordinate a n (comp₀ (U (t,ω))))
      =ᵐ[μ] fun ω => NativeFourierHeatCoordinate.coordinate a n (comp₀ (Z ω)) +
        (FiniteCylindricalIto.terminalIto P.toCoordinates basis).integral
          (StoppedItoInputs.stop F μ H t (input hg hβ hβ₁ U hU hEnergy a n)) ω := by
  rw [basis,←NativeNoiseEquivalence.integral_eq P L MatrixPredictableHaarRotation.basis]
  have hstop := stopped_input hg hβ hβ₁ U hU hEnergy a n t
  filter_upwards [heq 0 a n t ht] with ω hω
  change _ = _ + (FiniteCylindricalIto.terminalIto P.toCoordinates MatrixPredictableHaarRotation.basis).integral
    (NoiseRestrictionBounds.input (L).toLinearIsometry
      (StoppedItoInputs.stop F μ H t (input hg hβ hβ₁ U hU hEnergy a n))) ω
  rw [hstop]
  exact hω

end SHEStochastic.ScalarUnboundedFourierProjection
