module
public import SHE.OriginalSingleHaarInputs
public import SHE.OriginalNativeWhiteHeatRows
public import SHE.BoundedHaarRowApproximation
public import SHE.ItoLocalityTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.OriginalSingleHaarApproximation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2 Set Filter
open scoped NNReal ENNReal Topology
local instance singleApprox_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance singleApprox_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance singleApprox_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance singleApprox_realSigma : MeasurableSpace RealL2 := borel _
local instance singleApprox_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance singleApprox_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance singleApprox_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (D : SmoothApproximation.ScalarData)
variable (U : ℝ≥0→Ω→RealL2) (hU : IsStronglyPredictable 𝓕 U)
variable (q : ℝ≥0) (ε : ℝ) (hε : 0<ε) (x : StoppedFourier.HeatCircle)

theorem row_eq : OriginalSingleHaarInputs.row 𝓕 μ H D U hU q ε hε x=
    OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x := by
  apply PastItoAlgebra.eq_of_ambient_ae
  have hw := OriginalNativeWhiteHeatRows.input_ae D U 𝓕 hU μ H q ε hε x
  rw [OriginalNativeWhiteHeatRows.raw_eq_target] at hw
  exact (OriginalSingleHaarInputs.row_ae 𝓕 μ H D U hU q ε hε x).trans hw.symm

def approximation (n : ℕ) : Process (E:=RealHaarInput) 𝓕 μ H :=
  BoundedHaarRowApproximation.input 𝓕 μ H q
    (OriginalNativeFrozenRows.row D q ((q:ℝ)+ε) x)
    (OriginalNativeFrozenRows.row_continuous D q ((q:ℝ)+ε) x (by linarith))
    U hU.stronglyAdapted (OriginalNativeFrozenRows.bound D q ((q:ℝ)+ε))
    (OriginalNativeFrozenRows.row_norm_le D q ((q:ℝ)+ε) x (by linarith)) n

theorem approximation_tendsto (hc : ∀ω,Continuous (fun t=>U t ω)) :
    Tendsto (approximation 𝓕 μ H D U hU q ε hε x) atTop
      (𝓝 (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)) := by
  apply BoundedHaarRowApproximation.input_tendsto
    𝓕 μ H q (OriginalNativeFrozenRows.row D q ((q:ℝ)+ε) x)
    (OriginalNativeFrozenRows.row_continuous D q ((q:ℝ)+ε) x (by linarith))
    U hU.stronglyAdapted (OriginalNativeFrozenRows.bound D q ((q:ℝ)+ε))
    (OriginalNativeFrozenRows.row_norm_le D q ((q:ℝ)+ε) x (by linarith))
    (hU.mono (predictable_le_product 𝓕)).measurable hc (Real.sqrt_nonneg _) _
  rw [←OriginalNativeWhiteHeatRows.raw_eq_target]
  exact OriginalNativeWhiteHeatRows.input_ae D U 𝓕 hU μ H q ε hε x

theorem integral_input (J : StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H) :
    (OriginalSingleHaarInputs.integral 𝓕 μ H J).integral
      (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)=
    J.integral (SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry U) hU
      (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x) := by
  rw [←row_eq 𝓕 μ H D U hU q ε hε x]
  exact OriginalSingleHaarInputs.integral_toHaar 𝓕 μ H J _

theorem locality (J : StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)
    (hlocal : StandardTerminalPastLocality J) :
    StandardTerminalPastLocality (OriginalSingleHaarInputs.integral 𝓕 μ H J) :=
  ItoLocalityTransport.rotation 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.continuous.measurable.comp measurable_snd) J hlocal

/-- The SAME original physical integral is the samplewise limit of a
subsequence of the actual finite time/Haar integrals. -/
theorem exists_ae_subsequence (hc : ∀ω,Continuous (fun t=>U t ω))
    (J : StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H) :
    ∃ns:ℕ→ℕ,StrictMono ns ∧ ∀ᵐω∂μ,
      Tendsto (fun n=>((OriginalSingleHaarInputs.integral 𝓕 μ H J).integral
        (approximation 𝓕 μ H D U hU q ε hε x (ns n)):Lp ℝ 2 μ) ω)
      atTop (𝓝 ((J.integral (SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry U) hU
        (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x):Lp ℝ 2 μ) ω)) := by
  have ht := ((OriginalSingleHaarInputs.integral 𝓕 μ H J).integral.continuous.tendsto
    (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)).comp
      (approximation_tendsto 𝓕 μ H D U hU q ε hε x hc)
  rw [integral_input 𝓕 μ H D U hU q ε hε x J] at ht
  exact (tendstoInMeasure_of_tendsto_Lp (p:=2) (μ:=μ) ht).exists_seq_tendsto_ae
end SHE.OriginalSingleHaarApproximation
