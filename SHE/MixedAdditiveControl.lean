module

public import SHE.MixedGlobalCurrent
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass
public import SHE.MixedMovingEnergy
public import SHE.AdditiveHaarControl

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedAdditiveControl
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


def raw(p:ℝ≥0×Ω):RealHaarInput:=
  AdditiveHaarControl.value κ hκ Λ (S.second p.1 p.2-S.first p.1 p.2)
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem predictable:StronglyMeasurable[𝓕.predictable] Raw:=
  (AdditiveHaarControl.continuous κ hκ Λ).comp_stronglyMeasurable
    (S.second_predictable.sub S.first_predictable)

theorem reconstruct(p:ℝ≥0×Ω):
    realPart (fieldFactor κ κ hκ (AdditiveHaarForcing.constantField κ hκ)
      (realInputEmbed (Raw p)))=Λ • (S.second p.1 p.2-S.first p.1 p.2):=
  AdditiveHaarControl.reconstruct κ hκ Λ _

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- The actual original-Haar additive control is a genuine predictable
L2 input. Its exact expected energy is Lambda^2/kappa times the actual
global solution difference, so any proved damping-cost limit applies
directly before a stopped Girsanov theorem is invoked. -/
theorem exists_input (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B):
    ∃u:Process (E:=RealHaarInput) 𝓕 μ H,
      u=ᵐ[energyMeasure μ H] Raw ∧ ‖u‖^2=(Λ^2/κ)*Global:=by
  have hd:=MixedMovingEnergy.global_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG
  have hp:=predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hi:Integrable (fun p=>‖Raw p‖^2) (energyMeasure μ H):=by
    convert! hd.const_mul (Λ^2/κ) using 1
    funext p
    exact AdditiveHaarControl.norm_sq κ hκ Λ _
  have hm:MemLp Raw 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (hp.mono (predictable_le_product 𝓕)).aestronglyMeasurable).mpr hi
  have hmt:@MemLp _ _ 𝓕.predictable _ _ Raw 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
    change eLpNorm Raw 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))<⊤
    rw [eLpNorm_trim (predictable_le_product 𝓕) hp]
    exact hm
  let u:Process (E:=RealHaarInput) 𝓕 μ H:=hmt.toLp Raw
  have hua:u=ᵐ[energyMeasure μ H] Raw:=ae_eq_of_ae_eq_trim hmt.coeFn_toLp
  refine ⟨u,hua,?_⟩
  rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product 𝓕) u]
  rw [integral_congr_ae (hua.mono (fun p hp=>by rw [hp]))]
  exact AdditiveHaarControl.integral_energy (energyMeasure μ H) κ hκ Λ
    (fun p=>S.second p.1 p.2-S.first p.1 p.2)
end SHE.MixedAdditiveControl
