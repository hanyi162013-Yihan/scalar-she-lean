module

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

namespace SHE.MixedStoppingClock
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

def rate(N:ℕ)(t:ℝ≥0)(ω:Ω):ℝ:=‖Raw t ω‖^2+
  ((N:ℝ)+1)⁻¹*(‖S.second t ω‖^2+‖W t ω‖^2)
local notation "F"=>rate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W

def clock(N:ℕ):ℝ≥0→Ω→ℝ:=AdaptedRateLocalization.accumulated (F N)
local notation "A"=>clock 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W

theorem nonneg(N:ℕ)(t:ℝ≥0)(ω:Ω):0≤F N t ω:=
  add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.mpr (by positivity)) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
include hWc in
theorem continuous(N:ℕ)(ω:Ω):Continuous (fun t=>F N t ω):=by
  exact ((MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ω).norm.pow 2).add
    ((((S.second_continuous ω).norm.pow 2).add ((hWc ω).norm.pow 2)).const_mul _)
include hW in
theorem adapted(N:ℕ):StronglyAdapted 𝓕 (F N):=by
  have hr:=MixedCappedControl.predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hp:StronglyMeasurable[𝓕.predictable] (Function.uncurry (F N)):=
    (hr.norm.pow 2).add (((S.second_predictable.norm.pow 2).add (hW.norm.pow 2)).const_mul _)
  exact (show IsStronglyPredictable 𝓕 (F N) from hp).stronglyAdapted

include hW hWc in
theorem exists_difference_input(Q:Measure Ω)[IsProbabilityMeasure Q](N:ℕ):
    ∃d:Process (E:=RealL2) 𝓕 Q H,
      d=ᵐ[energyMeasure Q H] (fun p=>if A N p.1 p.2<1 then S.second p.1 p.2-W p.1 p.2 else 0) ∧
      ‖d‖^2≤2*((N:ℝ)+1):=by
  apply AdaptedRateLocalization.exists_input 𝓕 Q H (F N) (adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hW N)
    (continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N)
    (nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W N)
    (fun t ω=>S.second t ω-W t ω) (S.second_predictable.sub hW)
    (fun ω=>(S.second_continuous ω).sub (hWc ω)) (2*((N:ℝ)+1)) (by positivity)
  intro t ω
  have hN:0<(N:ℝ)+1:=by positivity
  have hinv:((N:ℝ)+1)*((N:ℝ)+1)⁻¹=1:=mul_inv_cancel₀ hN.ne'
  have hn:=norm_sub_le (S.second t ω) (W t ω)
  have hs:‖S.second t ω-W t ω‖^2≤2*(‖S.second t ω‖^2+‖W t ω‖^2):=by
    nlinarith [norm_nonneg (S.second t ω),norm_nonneg (W t ω),norm_nonneg (S.second t ω-W t ω),sq_nonneg (‖S.second t ω‖-‖W t ω‖)]
  have hraw:0≤2*((N:ℝ)+1)*‖Raw t ω‖^2:=by positivity
  dsimp only [rate]
  nlinarith [show ((N:ℝ)+1)*(((N:ℝ)+1)⁻¹*(‖S.second t ω‖^2+‖W t ω‖^2))=
    ‖S.second t ω‖^2+‖W t ω‖^2 by rw [←mul_assoc,hinv,one_mul]]
end SHE.MixedStoppingClock
