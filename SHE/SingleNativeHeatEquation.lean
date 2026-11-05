module
public import SHE.OriginalNativeHeatEquation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.SingleNativeHeatEquation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2
open OrthogonalItoChannels StoppedFourier NativeHeatObservation
open scoped NNReal ENNReal
local instance singleHeat_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance singleHeat_realSigma:MeasurableSpace RealL2:=borel _
local instance singleHeat_realBorel:BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData)
variable (U:ℝ≥0×Ω→RealL2)(hU:StronglyMeasurable[𝓕.predictable] U)

/-- The genuine single physical g(U) row. It is obtained from the checked
physical row, whose auxiliary coordinate is identically zero. -/
def row{T t:ℝ}(ht:t<T)(x:HeatCircle):Process (E:=RealL2) 𝓕 μ H:=
  ((WithLp.fstL 2 ℝ RealL2 RealL2).compLpL 2
    ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
      (PredictableScalarHaarRotation.originalRow 𝓕 μ H D U hU ht x)

theorem row_ae{T t:ℝ}(ht:t<T)(x:HeatCircle):row 𝓕 μ H D U hU ht x=ᵐ[energyMeasure μ H]
    fun p=>if (p.1:ℝ)<t then
      ScalarSplittingInputs.originalInput haarAddCircle (ScalarHaarRotation.scalar D (U p))
        (ScalarHaarRotation.scalar_measurable D (U p)) D.upper (ScalarHaarRotation.scalar_bound D (U p))
        (ScalarHaarHeatRows.test (T-(p.1:ℝ)) x) else 0:=by
  filter_upwards [ae_eq_of_ae_eq_trim ((WithLp.fstL 2 ℝ RealL2 RealL2).coeFn_compLpL
    (PredictableScalarHaarRotation.originalRow 𝓕 μ H D U hU ht x)),
    PredictableScalarHaarRotation.originalRow_ae 𝓕 μ H D U hU ht x] with p hp hr
  change row 𝓕 μ H D U hU ht x p=_
  change row 𝓕 μ H D U hU ht x p=(WithLp.fstL 2 ℝ RealL2 RealL2)
    (PredictableScalarHaarRotation.originalRow 𝓕 μ H D U hU ht x p) at hp
  rw [hp,hr]
  split_ifs <;> rfl

variable (J:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)(u₀:RealL2)
/-- The original ONE cylindrical-noise equation in all positive native
heat observations. Its input is the literal bounded physical g(U) row. -/
def Equation(V:ℝ≥0→Ω→RealL2)(hV:StronglyMeasurable[𝓕.predictable] (Function.uncurry V)):Prop:=
  ∀(q:ℝ≥0),q≤H→∀(ε:ℝ)(hε:0<ε)(x:HeatCircle),
    (fun ω=>functional ε x (V q ω))=ᵐ[μ] fun ω=>functional ((q:ℝ)+ε) x u₀+
      J.integral (row 𝓕 μ H D (Function.uncurry V) hV (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x) ω

structure Data where
  value:ℝ≥0→Ω→RealL2
  continuous:∀ω,Continuous (fun t=>value t ω)
  predictable:StronglyMeasurable[𝓕.predictable] (Function.uncurry value)
  equation:Equation 𝓕 μ H D J u₀ value predictable
end SHE.SingleNativeHeatEquation
