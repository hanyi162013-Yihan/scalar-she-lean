module

public import SHE.MixedNamedLevelNoise
public import SHE.FiniteItoPostWitness

public import SHE.MixedNamedPhysicalStep
public import SHE.MixedJointIntegratedLevel
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedNamedLevelPostWitness
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

local notation "D" => MixedJointLevelData.state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem state_eq_value (p : P) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(L.observations.observations p i).target) (hqb : q≤b) (ω : Ω) :
    D p ω (q:ℝ)=MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L.observations.observations p) b q ω :=
  MixedNativeJointHistory.evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L.observations.observations p) b q hgap hqb ω

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- The actual complete canonical finite-level noise has a SAME-J input
supported after the ORIGINAL reference base. No individual coefficient
error or physical insertion is omitted from this identification. -/
theorem original_post_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
    {η:ℝ} (hη:0<η) (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p) (p:P):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral (PastItoInputs.post 𝓕 μ H R.base.toNNReal input)=ᵐ[μ]
        MixedJointIntegratedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p:=by
  let b:ℝ≥0:=(L.terminal p).toNNReal
  have hbcoe:(b:ℝ)=L.terminal p:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
  have hbH:b≤H:=by exact_mod_cast (show (b:ℝ)≤H by rw [hbcoe];exact (L.terminal_horizon p).trans hh)
  have hstrict:∀i,(b:ℝ)<(L.observations.observations p i).target:=by
    intro i
    rw [hbcoe]
    linarith [hgap p i]
  have hvb:R.base.toNNReal≤b:=Real.toNNReal_le_toNNReal (L.terminal_base p)
  have hrep:∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral (PastItoInputs.post 𝓕 μ H R.base.toNNReal input)=
        MixedJointNamedIto.scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          J hIJ₀ hIJ₁ hnull hΛ (L.observations.observations p) b hstrict hbH R.base.toNNReal
            (backward (L.window p) (L.test p)):=by
    unfold MixedJointNamedIto.scalarNoise
    exact FiniteItoPostWitness.original_post_input 𝓕 μ H _ _ _ J R.base.toNNReal b hvb _
  obtain ⟨input,hi⟩:=hrep
  refine ⟨input,?_⟩
  rw [hi]
  exact (MixedNamedLevelNoise.noise_eq_original 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
    hnull hJ hΛ hA hh hη hgap p).symm

end SHE.MixedNamedLevelPostWitness
