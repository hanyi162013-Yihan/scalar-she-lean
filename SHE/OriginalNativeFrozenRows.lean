module
public import SHE.OriginalNativeRowContinuity
public import SHE.BoundedContinuousRowFreezing
public import SHE.AdditivePhysicalFactor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.OriginalNativeFrozenRows
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle Filter Set
open scoped NNReal ENNReal Topology
local instance frozenRows_unit : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance frozenRows_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance frozenRows_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance frozenRows_realSigma : MeasurableSpace RealL2 := borel _
local instance frozenRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance frozenRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance frozenRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable (D : SmoothApproximation.ScalarData) (q : ℝ≥0) (T : ℝ)
variable (x : StoppedFourier.HeatCircle)

/-- Fixed physical white-noise coordinates, independent of U and g. -/
def coordinates : RealHaarInput ≃ₗᵢ[ℝ] RealL2 := AdditivePhysicalFactor.whiteCoordinates 1 zero_lt_one

def row (p : Iic q×RealL2) : RealHaarInput :=
  coordinates.symm (OriginalNativeRowContinuity.row D T x (p.1:ℝ≥0) p.2)

theorem row_continuous (hqT : (q:ℝ)<T) : Continuous (row D q T x) := by
  have hp : Continuous (fun p:Iic q×RealL2=>(((p.1:ℝ≥0):ℝ),p.2)) := by fun_prop
  rw [continuous_iff_continuousAt]
  intro p
  have hr : ((p.1:ℝ≥0):ℝ)<T := (show ((p.1:ℝ≥0):ℝ)≤q by exact_mod_cast p.1.2).trans_lt hqT
  have hc := (OriginalNativeRowContinuity.continuousAt_row D T (p.1:ℝ≥0) hr p.2 x).comp
    (f:=fun z:Iic q×RealL2=>(((z.1:ℝ≥0):ℝ),z.2)) (x:=p) hp.continuousAt
  exact coordinates.symm.continuous.continuousAt.comp hc

def bound : ℝ := Real.sqrt (D.upper^2*(1+StoppedFourier.heatConstant*(T-(q:ℝ))^(-(1/2:ℝ))))

theorem row_norm_le (hqT : (q:ℝ)<T) (p : Iic q×RealL2) : ‖row D q T x p‖≤bound D q T := by
  have hb := OriginalNativeRowContinuity.row_norm_sq_bound D T (p.1:ℝ≥0) q
    (by exact_mod_cast p.1.2) hqT p.2 x
  have hC : 0≤D.upper^2*(1+StoppedFourier.heatConstant*(T-(q:ℝ))^(-(1/2:ℝ))) :=
    mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one
      (mul_nonneg StoppedFourier.heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr hqT).le _)))
  have he : ‖row D q T x p‖=‖OriginalNativeRowContinuity.row D T x (p.1:ℝ≥0) p.2‖ :=
    coordinates.symm.norm_map _
  rw [he]
  dsimp only [bound]
  nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg (D.upper^2*(1+StoppedFourier.heatConstant*(T-(q:ℝ))^(-(1/2:ℝ)))),
    norm_nonneg (OriginalNativeRowContinuity.row D T x (p.1:ℝ≥0) p.2)]

/-- The actual original g(U) heat rows have convergent left-frozen input
energy in fixed white coordinates, with no smoothness of g beyond Holder. -/
theorem energy_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : ℝ≥0) (hqT : (q:ℝ)<T) (U : ℝ≥0→Ω→RealL2)
    (hU : Measurable (Function.uncurry U)) (hc : ∀ω,Continuous (fun t=>U t ω)) :
    Tendsto (fun n=>∫p,‖BoundedContinuousRowFreezing.value q (row D q T x) U n p-
      BoundedContinuousRowFreezing.target q (row D q T x) U p‖^2 ∂PredictableL2.energyMeasure μ H)
      atTop (𝓝 (0:ℝ)) :=
  BoundedContinuousRowFreezing.energy_tendsto q (row D q T x) U μ H
    (row_continuous D q T x hqT) hU hc (bound D q T) (Real.sqrt_nonneg _) (row_norm_le D q T x hqT)
end SHE.OriginalNativeFrozenRows
