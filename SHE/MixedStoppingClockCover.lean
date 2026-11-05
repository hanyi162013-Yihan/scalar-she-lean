module

public import SHE.MixedStoppingClock
public import SHE.AdaptedRateLocalization
public import SHE.MixedGirsanovVectorMild
public import SHE.TimeMeasureRestriction
public import SHE.HilbertItoNaturality
public import SHE.NativeGirsanovTwoChannelTransport
public import SHE.NativeDampedHaarInput
public import SHE.NativeControlMass
public import SHE.NativeHeatColumnAction
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass
public import SHE.MixedMovingEnergy
public import SHE.MixedAdditiveControl
public import SHE.CappedStochasticExponential

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.MixedStoppingClockCover
open Set Filter Topology MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedMovingEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedMovingEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedMovingEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedMovingEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedMovingEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedMovingEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedMovingEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedMovingEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedMovingEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedMovingEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)


local notation "Raw"=>MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Cap"=>PredictableEnergyCap.capped Raw


local notation "F0"=>fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "F1"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "Drift"=>MixedCappedDampedHeatControl.drift
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S


local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology



variable(W:ℝ≥0→Ω→RealL2)(hW:StronglyMeasurable[𝓕.predictable] (Function.uncurry W))
variable(hWc:∀ω,Continuous (fun t=>W t ω))

local notation "F"=>MixedStoppingClock.rate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W
local notation "A"=>MixedStoppingClock.clock 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W

include hWc in
theorem clock_eq(N:ℕ)(t:ℝ≥0)(ω:Ω):A N t ω=PredictableEnergyCap.accumulated Raw t ω+
    ((N:ℝ)+1)⁻¹*(∫s in (0:ℝ)..(t:ℝ),(‖S.second s.toNNReal ω‖^2+‖W s.toNNReal ω‖^2)):=by
  let f:ℝ→ℝ:=fun s=>‖Raw s.toNNReal ω‖^2
  let g:ℝ→ℝ:=fun s=>‖S.second s.toNNReal ω‖^2+‖W s.toNNReal ω‖^2
  have hf:Continuous f:=((MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ω).comp continuous_real_toNNReal).norm.pow 2
  have hg:Continuous g:=(((S.second_continuous ω).comp continuous_real_toNNReal).norm.pow 2).add
    (((hWc ω).comp continuous_real_toNNReal).norm.pow 2)
  have hi:=intervalIntegral.integral_add (μ:=volume) (a:=(0:ℝ)) (b:=(t:ℝ)) (hf.intervalIntegrable 0 t)
    ((hg.const_mul (((N:ℝ)+1)⁻¹)).intervalIntegrable 0 t)
  have hm:=intervalIntegral.integral_const_mul (((N:ℝ)+1)⁻¹) g (μ:=volume) (a:=(0:ℝ)) (b:=(t:ℝ))
  exact hi.trans (congrArg (fun x:ℝ=>(∫s in (0:ℝ)..(t:ℝ),f s)+x) hm)
include hWc in
theorem covers(ω:Ω)(hc:PredictableEnergyCap.accumulated Raw H ω<1):∃N:ℕ,A N H ω<1:=by
  have hn:Tendsto (fun N:ℕ=>(N:ℝ)+1) atTop atTop:=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hi:Tendsto (fun N:ℕ=>((N:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)):=by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  let B:ℝ:=∫s in (0:ℝ)..(H:ℝ),(‖S.second s.toNNReal ω‖^2+‖W s.toNNReal ω‖^2)
  have hlim:Tendsto (fun N:ℕ=>PredictableEnergyCap.accumulated Raw H ω+((N:ℝ)+1)⁻¹*B)
      atTop (𝓝 (PredictableEnergyCap.accumulated Raw H ω)):=by
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (hi.mul_const B)
  have he:=hlim.eventually (gt_mem_nhds hc)
  obtain ⟨N,hN⟩:=he.exists
  exact ⟨N,(clock_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N H ω).trans_lt hN⟩
end SHE.MixedStoppingClockCover
