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

namespace SHE.MixedStoppingClockProperties
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
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
include hW hWc in
theorem adapted(N:ℕ):StronglyAdapted 𝓕 (A N):=
  AdaptedRateLocalization.adapted 𝓕 (F N)
    (MixedStoppingClock.adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hW N)
    (MixedStoppingClock.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N)
include hWc in
theorem continuous(N:ℕ)(ω:Ω):Continuous (fun t=>A N t ω):=
  AdaptedRateLocalization.continuous (F N)
    (MixedStoppingClock.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N) ω
include hWc in
theorem monotone(N:ℕ)(ω:Ω):Monotone (fun t=>A N t ω):=
  AdaptedRateLocalization.monotone (F N)
    (MixedStoppingClock.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N)
    (MixedStoppingClock.nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W N) ω
include hWc in
theorem raw_le(N:ℕ)(t:ℝ≥0)(ω:Ω):PredictableEnergyCap.accumulated Raw t ω≤A N t ω:=by
  let r:ℝ→ℝ:=fun s=>‖Raw s.toNNReal ω‖^2
  let f:ℝ→ℝ:=fun s=>F N s.toNNReal ω
  have hr:Continuous r:=((MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ω).comp continuous_real_toNNReal).norm.pow 2
  have hf:Continuous f:=(MixedStoppingClock.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N ω).comp continuous_real_toNNReal
  have hri:Integrable r (volume.restrict (Ioc (0:ℝ) (t:ℝ))):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.2).mp (hr.intervalIntegrable _ _)
  have hfi:Integrable f (volume.restrict (Ioc (0:ℝ) (t:ℝ))):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.2).mp (hf.intervalIntegrable _ _)
  have hle:∀s,r s≤f s:=by
    intro s
    change _≤‖Raw s.toNNReal ω‖^2+((N:ℝ)+1)⁻¹*(‖S.second s.toNNReal ω‖^2+‖W s.toNNReal ω‖^2)
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (by positivity)) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have h1:=intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ)) (f:=r) t.2
  have h2:=intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ)) (f:=f) t.2
  calc
    _=∫s in Ioc (0:ℝ) (t:ℝ),r s:=h1
    _≤∫s in Ioc (0:ℝ) (t:ℝ),f s:=integral_mono hri hfi hle
    _=_:=h2.symm
end SHE.MixedStoppingClockProperties
