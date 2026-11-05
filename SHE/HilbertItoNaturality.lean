module

public import SHE.NativeObservationNaturality
public import SHE.PastItoAlgebra
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.HilbertItoNaturality
open MeasureTheory PredictableL2 NativeObservationNaturality NativeHeatObservation DyadicApproximation FiniteHaar
open scoped ENNReal NNReal
local instance hilbertItoNaturality_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance hilbertItoNaturality_circleSecondCountable : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance hilbertItoNaturality_realSecondCountable : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance hilbertItoNaturality_realSigma : MeasurableSpace RealL2 := borel _
local instance hilbertItoNaturality_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance hilbertItoNaturality_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance hilbertItoNaturality_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance hilbertItoNaturality_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance hilbertItoNaturality_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ : StandardScalarNaturality I J)
local notation "ν"=>((energyMeasure μ H).trim (predictable_le_product 𝓕))

omit [IsProbabilityMeasure μ] in
/-- Composition of two actual column actions commutes with passage to
predictable L2 classes, with no stochastic assertion involved. -/
theorem mapped_input_comp (A : RealL2 →L[ℝ] RealL2) (L : RealL2 →L[ℝ] ℝ)
    (v : Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H) :
    ((HilbertColumns.mapCLM L).compLpL 2 ν)
      (((HilbertColumns.mapCLM A).compLpL 2 ν) v)=
      ((HilbertColumns.mapCLM (L.comp A)).compLpL 2 ν) v := by
  apply Lp.ext
  filter_upwards [(HilbertColumns.mapCLM L).coeFn_compLpL
      (((HilbertColumns.mapCLM A).compLpL 2 ν) v),
    (HilbertColumns.mapCLM A).coeFn_compLpL v,
    (HilbertColumns.mapCLM (L.comp A)).coeFn_compLpL v] with p hL hA hLA
  rw [hL,hA,hLA]
  apply lp.ext
  funext i
  rfl

include hIJ in
/-- Scalar naturality already implies full bounded-linear Hilbert
naturality for the SAME original integral. Separability combines the
scalar exceptional sets; no additional stochastic input is introduced. -/
theorem commutes (A : RealL2 →L[ℝ] RealL2)
    (v : Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H) :
    (fun ω=>A (I.integral v ω)) =ᵐ[μ]
      I.integral (((HilbertColumns.mapCLM A).compLpL 2 ν) v) := by
  let w:=((HilbertColumns.mapCLM A).compLpL 2 ν) v
  have hz : (fun ω=>A (I.integral v ω)-I.integral w ω)=ᵐ[μ] (0:Ω→RealL2) := by
    apply ae_eq_zero_of_forall_inner (𝕜:=ℝ)
    intro c
    let L : RealL2 →L[ℝ] ℝ:=innerSL ℝ c
    have h₁:=hIJ.commutes L w
    have h₂:=hIJ.commutes (L.comp A) v
    have hin:=mapped_input_comp 𝓕 μ H A L v
    change ((HilbertColumns.mapCLM L).compLpL 2 ν) w=_ at hin
    rw [hin] at h₁
    have he:=h₁.trans h₂.symm
    filter_upwards [L.coeFn_compLpL (I.integral w),(L.comp A).coeFn_compLpL (I.integral v)] with ω hω hωA
    have hh:=congrArg (fun f : Lp ℝ 2 μ=>f ω) he
    rw [hω,hωA] at hh
    change L (A (I.integral v ω)-I.integral w ω)=0
    rw [ContinuousLinearMap.comp_apply] at hh
    rw [map_sub]
    exact sub_eq_zero.mpr hh.symm
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

end SHE.HilbertItoNaturality
