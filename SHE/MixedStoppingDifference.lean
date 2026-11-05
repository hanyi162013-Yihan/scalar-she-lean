module

public import SHE.MixedStoppingClockProperties
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

namespace SHE.MixedStoppingDifference
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

def value(N:ℕ)(p:ℝ≥0×Ω):RealL2:=if A N p.1 p.2<1 then S.second p.1 p.2-W p.1 p.2 else 0
include hW hWc in
theorem predictable(N:ℕ):StronglyMeasurable[𝓕.predictable]
    (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W N):=by
  exact AdaptedRateLocalization.predictable 𝓕 (F N)
    (MixedStoppingClock.adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hW N)
    (MixedStoppingClock.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hWc N)
    (fun t ω=>S.second t ω-W t ω) (S.second_predictable.sub hW)
include hW hWc in
theorem path_memLp(N:ℕ)(ω:Ω):MemLp
    (fun t=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W N (t,ω)) 2 (timeMeasure H):=by
  have hp:=predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hW hWc N
  have hm:Measurable (fun t:ℝ≥0=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W N (t,ω)):=
    (hp.mono (predictable_le_product 𝓕)).measurable.comp (measurable_id.prodMk measurable_const)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (NativeControlMass.continuous_integrable H
    (((S.second_continuous ω).sub (hWc ω)).norm.pow 2)).mono'
    (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  unfold value
  split_ifs
  · change ‖S.second t ω-W t ω‖^2≤‖S.second t ω-W t ω‖^2
    exact le_rfl
  · simp only [norm_zero,zero_pow (by decide:2≠0)]
    exact sq_nonneg _
include hW hWc in
theorem integrable(Q:Measure Ω)[IsProbabilityMeasure Q](N:ℕ):
    Integrable (fun p=>‖value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W N p‖^2) (energyMeasure Q H):=by
  obtain ⟨d,hd,_⟩:=MixedStoppingClock.exists_difference_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W hW hWc Q N
  have hi:Integrable (fun p=>‖d p‖^2) (energyMeasure Q H):=
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp d)).norm.integrable_sq
  apply hi.congr
  filter_upwards [hd] with p hp
  exact congrArg (fun v:RealL2=>‖v‖^2) hp
end SHE.MixedStoppingDifference
