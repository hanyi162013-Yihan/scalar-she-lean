module
public import SHE.SingleNativeHeatEquation
public import SHE.OriginalNativeFrozenRows
public import SHE.PredictableItoRotation
public import SHE.PastItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.OriginalSingleHaarInputs
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2 Set
open scoped NNReal ENNReal
local instance singleHaar_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance singleHaar_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance singleHaar_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance singleHaar_realSigma : MeasurableSpace RealL2 := borel _
local instance singleHaar_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance singleHaar_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance singleHaar_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def toPhysical : Process (E:=RealHaarInput) 𝓕 μ H →ₗᵢ[ℝ] Process (E:=RealL2) 𝓕 μ H :=
  PredictableItoRotation.processIsometry 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.continuous.measurable.comp measurable_snd)

def toHaar : Process (E:=RealL2) 𝓕 μ H →ₗᵢ[ℝ] Process (E:=RealHaarInput) 𝓕 μ H :=
  PredictableItoRotation.processIsometry 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.symm.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.symm.continuous.measurable.comp measurable_snd)

theorem toPhysical_toHaar (f : Process (E:=RealL2) 𝓕 μ H) :
    toPhysical 𝓕 μ H (toHaar 𝓕 μ H f)=f := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [PredictableItoRotation.processIsometry_ae 𝓕 μ H
      (fun _=>OriginalNativeFrozenRows.coordinates.toLinearIsometry)
      (OriginalNativeFrozenRows.coordinates.continuous.measurable.comp measurable_snd)
      (toHaar 𝓕 μ H f),
    PredictableItoRotation.processIsometry_ae 𝓕 μ H
      (fun _=>OriginalNativeFrozenRows.coordinates.symm.toLinearIsometry)
      (OriginalNativeFrozenRows.coordinates.symm.continuous.measurable.comp measurable_snd) f] with p hp hh
  change toPhysical 𝓕 μ H (toHaar 𝓕 μ H f) p=f p
  change toPhysical 𝓕 μ H (toHaar 𝓕 μ H f) p=_ at hp
  change toHaar 𝓕 μ H f p=_ at hh
  rw [hp,hh]
  exact OriginalNativeFrozenRows.coordinates.apply_symm_apply _

def integral (J : StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H) :
    StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H :=
  PredictableItoRotation.integral 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.continuous.measurable.comp measurable_snd) J

theorem integral_toHaar (J : StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)
    (f : Process (E:=RealL2) 𝓕 μ H) :
    (integral 𝓕 μ H J).integral (toHaar 𝓕 μ H f)=J.integral f := by
  change J.integral (toPhysical 𝓕 μ H (toHaar 𝓕 μ H f))=J.integral f
  rw [toPhysical_toHaar]

variable (D : SmoothApproximation.ScalarData)
variable (U : ℝ≥0→Ω→RealL2) (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U))

def row (q : ℝ≥0) (ε : ℝ) (hε : 0<ε) (x : StoppedFourier.HeatCircle) :
    Process (E:=RealHaarInput) 𝓕 μ H :=
  toHaar 𝓕 μ H (SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry U) hU
    (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x)

theorem row_ae (q : ℝ≥0) (ε : ℝ) (hε : 0<ε) (x : StoppedFourier.HeatCircle) :
    row 𝓕 μ H D U hU q ε hε x=ᵐ[energyMeasure μ H]
      BoundedContinuousRowFreezing.target q (OriginalNativeFrozenRows.row D q ((q:ℝ)+ε) x) U := by
  filter_upwards [PredictableItoRotation.processIsometry_ae 𝓕 μ H
      (fun _=>OriginalNativeFrozenRows.coordinates.symm.toLinearIsometry)
      (OriginalNativeFrozenRows.coordinates.symm.continuous.measurable.comp measurable_snd)
      (SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry U) hU
        (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x),
    SingleNativeHeatEquation.row_ae 𝓕 μ H D (Function.uncurry U) hU
      (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x] with p hp hs
  change row 𝓕 μ H D U hU q ε hε x p=_
  change row 𝓕 μ H D U hU q ε hε x p=_ at hp
  rw [hp,hs]
  by_cases hlt:p.1<q
  · have hc:(p.1:ℝ)<(q:ℝ) := by exact_mod_cast hlt
    simp only [BoundedContinuousRowFreezing.target,hlt,hc,ite_true,min_eq_left hlt.le]
    rfl
  · have hc:¬(p.1:ℝ)<(q:ℝ) := by exact_mod_cast hlt
    simp only [BoundedContinuousRowFreezing.target,hlt,hc,ite_false,map_zero]
end SHE.OriginalSingleHaarInputs
