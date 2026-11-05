module

public import SHE.MixedNamedLevelNoise
public import SHE.TerminalItoAverageWitness
public import SHE.PastItoLimitWitness
public import SHE.MixedNamedLevelPostWitness
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

namespace SHE.MixedLevelOriginalAverage
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
/-- Original history averaging retains support after the original base,
which is needed before substituting an F_v-random reference. -/
theorem original_post_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
    {η:ℝ} (hη:0<η) (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)
    (ν:Measure P) [IsFiniteMeasure ν]:
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral (PastItoInputs.post 𝓕 μ H R.base.toNNReal input)=ᵐ[μ]
        fun ω=>∫p,MixedJointIntegratedLevel.noiseVersion
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω ∂ν:=by
  obtain ⟨B,hB,hBb⟩:=MixedJointIntegratedLevel.uniform_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ
  exact PastItoLimitWitness.bounded_post_average 𝓕 μ H R.base.toNNReal J ν
    (fun z:P×Ω=>MixedJointIntegratedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L z.1 z.2)
    (MixedJointIntegratedLevel.noiseVersion_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L) hB
    (fun p ω=>(hBb p ω).2.2.2.2)
    (fun p=>MixedNamedLevelPostWitness.original_post_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
        hnull hJ hΛ hA hh hη hgap p)

include hIJ₀ hIJ₁ in
/-- At every genuine finite cutoff level, the history-averaged canonical
noise is the ORIGINAL J applied to an actual predictable L2 input.
All parameter measurability and input existence follow from the physical
level formula and closed Hilbert range; no stochastic Fubini is assumed. -/
theorem original_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
    {η:ℝ} (hη:0<η) (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)
    (ν:Measure P) [IsFiniteMeasure ν]:
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>∫p,MixedJointIntegratedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω ∂ν:=by
  obtain ⟨B,hB,hBb⟩:=MixedJointIntegratedLevel.uniform_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ
  apply TerminalItoAverageWitness.bounded_average 𝓕 μ H J ν
    (fun z:P×Ω=>MixedJointIntegratedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L z.1 z.2)
    (MixedJointIntegratedLevel.noiseVersion_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L) hB
    (fun p ω=>(hBb p ω).2.2.2.2)
  intro p
  let b:ℝ≥0:=(L.terminal p).toNNReal
  have hbcoe:(b:ℝ)=L.terminal p:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
  have hbH:b≤H:=by exact_mod_cast (show (b:ℝ)≤H by rw [hbcoe];exact (L.terminal_horizon p).trans hh)
  have hs:∀i,(b:ℝ)<(L.observations.observations p i).target:=by
    intro i;rw [hbcoe];have hh:=hgap p i;linarith
  let N:=MixedJointNamedIto.scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hnull hΛ (L.observations.observations p) b hs hbH R.base.toNNReal
      (backward (L.window p) (L.test p))
  have he:MixedJointIntegratedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p=ᵐ[μ] N:=
    MixedNamedLevelNoise.noise_eq_original
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁ hnull hJ hΛ hA hh hη hgap p
  have hn:∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=N:=by
    classical
    dsimp only [N,MixedJointNamedIto.scalarNoise,FiniteItoNoise.noise]
    split_ifs
    · exact ⟨_,rfl⟩
    · exact ⟨0,map_zero _⟩
  obtain ⟨input,hV⟩:=hn
  exact ⟨input,by rw [hV];exact he.symm⟩

end SHE.MixedLevelOriginalAverage
