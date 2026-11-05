module

public import SHEStochastic.MatrixAnalyticConvolution
public import SHEStochastic.MatrixPointHeatInput

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixAnalyticObservation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
    (s T : ℝ≥0) (hs : s ≤ H) (hT : T ≤ H) (hsT : s < T) (x : HeatCircle) (i : d)
local notation "ν" => ((energyMeasure μ H).trim (predictable_le_product F))
local notation "test" => VectorPointHeatTest.test ((T : ℝ)-(s : ℝ)) x i
include hsT

/-- Heating the actual L2 convolution to an original target produces
exactly its original-target point input, stopped at the observation time. -/
theorem input_eq :
    (HilbertColumns.mapCLM (innerSL ℝ test)).compLpL 2 ν
      (MatrixAnalyticConvolution.input F μ H hH U hU Q hUpper hQ s hs)=
        StoppedItoInputs.stop F μ H (s : ℝ) (MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ T hT x i) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (innerSL ℝ test)).coeFn_compLpL
      (MatrixAnalyticConvolution.input F μ H hH U hU Q hUpper hQ s hs)),
    MatrixAnalyticConvolution.input_ae F μ H hH U hU Q hUpper hQ s hs,
    StoppedItoInputs.stop_ae F μ H (s : ℝ) (MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ T hT x i),
    MatrixPointHeatInput.input_ae F μ H hH U hU Q hUpper hQ T hT x i] with p ha hc hb hp
  rw [ha,hc,MatrixAnalyticConvolution.stopped_observed (show (s : ℝ)<(T : ℝ) from hsT),hb]
  simp only [StoppedItoInputs.before,Set.indicator_apply,Set.mem_setOf_eq]
  by_cases ht : (p.1 : ℝ)<(s : ℝ)
  · rw [if_pos ht,if_pos ht,hp]
  · rw [if_neg ht,if_neg ht]

theorem commutes (N : FiniteScalarIto.Family F μ H (d × HaarNode)) :
    (innerSL ℝ test).compLpL 2 μ (MatrixAnalyticConvolution.value F μ H hH U hU Q hUpper hQ N s hs)=
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (StoppedItoInputs.stop F μ H (s : ℝ) (MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ T hT x i)) := by
  have h := HilbertTerminalIto.commutes F μ H VectorWhiteCoordinates.basis
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)
    (innerSL ℝ test) (MatrixAnalyticConvolution.input F μ H hH U hU Q hUpper hQ s hs)
  rw [input_eq F μ H hH U hU Q hUpper hQ s T hs hT hsT x i] at h
  exact h

/-- The actual scalar finite-Ito observation and the actual Hilbert
mild convolution agree on their original probability space. -/
theorem observation_ae (N : FiniteScalarIto.Family F μ H (d × HaarNode)) :
    (fun ω => VectorHeatObservation.observation ((T : ℝ)-(s : ℝ)) x
      (MatrixAnalyticConvolution.value F μ H hH U hU Q hUpper hQ N s hs ω) i) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (StoppedItoInputs.stop F μ H (s : ℝ) (MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ T hT x i)) := by
  have h := (innerSL ℝ test).coeFn_compLpL (MatrixAnalyticConvolution.value F μ H hH U hU Q hUpper hQ N s hs)
  rw [commutes F μ H hH U hU Q hUpper hQ s T hs hT hsT x i N] at h
  filter_upwards [h] with ω hω
  rw [← VectorPointHeatTest.pairing (show 0<(T : ℝ)-(s : ℝ) from sub_pos.mpr hsT)]
  exact hω.symm

end SHEStochastic.MatrixAnalyticObservation
