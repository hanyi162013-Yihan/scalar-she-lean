module

public import SHE.MixedLevelOriginalAverage
public import SHE.MixedLevelPhysicalGradient
public import SHE.TerminalItoRawAverage
public import SHE.RootHeatGradientContinuity
public import SHE.MixedHeatNoiseL2Limit
public import SHE.RootMixedNoiseL2Limit
public import SHE.TerminalItoClosedLimit
public import SHE.TerminalItoAverageWitness
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

namespace SHE.MixedLevelGradientBounds
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

local notation "Mean"=>MixedLevelPhysicalGradient.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "Raw"=>MixedLevelPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem gradient_bound:∃C:ℝ,0≤C ∧ ∀p t z,
    ‖fderiv ℝ (GaussianItoTest.backward (L.window p) (L.test p) t) z‖≤C:=by
  obtain ⟨C₀,hC₀,hB₀⟩:=L.test_uniform.norm_bound
  obtain ⟨C,hC,hB⟩:=L.test_uniform.fderiv.norm_bound
  refine ⟨C,hC,fun p t z=>?_⟩
  exact BackwardRegularity.gaussian_state_gradient_bound _
    ((L.test_uniform.smooth p).of_le (by simp)) (hB₀ p) (hB p) z

theorem norm_le_of_row_bound {C D:ℝ}(hC:0≤C)
    (hgrad:∀p t z,‖fderiv ℝ (GaussianItoTest.backward (L.window p) (L.test p) t) z‖≤C)
    (z:P×(ℝ≥0×Ω))(hz:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<L.terminal z.1)
    (hrow:∀i,‖MixedNativeJointPhysicalRows.physicalRow
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1) z.2 i‖≤D):
    ‖Raw z‖≤n*C*D:=by
  rw [MixedLevelPhysicalGradient.raw,if_pos hz]
  calc
    _≤∑i:Fin n,‖(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
      (Mean z) (EuclideanSpace.basisFun (Fin n) ℝ i)) •
      MixedNativeJointPhysicalRows.physicalRow
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1) z.2 i‖:=norm_sum_le _ _
    _≤∑_:Fin n,C*D:=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have hg:=(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
        (Mean z)).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
      rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at hg
      exact mul_le_mul (hg.trans (hgrad _ _ _)) (hrow i) (norm_nonneg _) hC
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];push_cast;ring

/-- The real native moving-terminal cap is valid without a positive
terminal observation gap, on every strict current section. -/
theorem norm_le_terminal_cap (hΛ:0≤Λ){C:ℝ}(hC:0≤C)
    (hgrad:∀p t z,‖fderiv ℝ (GaussianItoTest.backward (L.window p) (L.test p) t) z‖≤C)
    (z:P×(ℝ≥0×Ω))(hz:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<L.terminal z.1):
    ‖Raw z‖≤n*C*Real.sqrt (NativeObservationCaps.cap (κ+10*M) (L.terminal z.1-(z.2.1:ℝ))):=by
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hm:0≤κ+10*M:=by positivity
  have hp:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hz.2)
  apply norm_le_of_row_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hC hgrad z hz
  intro i
  apply (Real.le_sqrt (norm_nonneg _) hp).mpr
  apply MixedNativePhysicalRowBound.row_bound_uniform
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1)
    hΛ z.2.1 (sub_pos.mpr hz.2)
  · intro j;linarith [L.targets_after z.1 j]
  · intro j;exact hz.2.le.trans (L.stops_after z.1 j)
  · exact le_rfl

/-- The finite positive-gap family has a genuine uniform coarse input
cap, derived from its physical rows and actual gradient. -/
theorem raw_bound(hΛ:0≤Λ){η:ℝ}(hη:0<η)
    (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p):
    ∃B:ℝ,0≤B ∧ ∀z,‖Raw z‖≤B:=by
  obtain ⟨C,hC,hCb⟩:=gradient_bound L
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hp:=NativeObservationCaps.cap_nonneg (show 0≤κ+10*M by positivity) hη
  refine ⟨n*C*Real.sqrt (NativeObservationCaps.cap (κ+10*M) η),by positivity,?_⟩
  intro z
  by_cases hz:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<L.terminal z.1
  · apply norm_le_of_row_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hC hCb z hz
    intro i
    let c:ℝ≥0:=(L.terminal z.1).toNNReal
    have hc:(c:ℝ)=L.terminal z.1:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base z.1))
    apply (Real.le_sqrt (norm_nonneg _) hp).mpr
    apply MixedNativePhysicalRowBound.row_bound_uniform
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1) hΛ c hη
    · intro j;rw [hc];exact hgap z.1 j
    · intro j;rw [hc];exact L.stops_after z.1 j
    · rw [hc];exact hz.2.le
  · rw [MixedLevelPhysicalGradient.raw,if_neg hz,norm_zero]
    positivity

end SHE.MixedLevelGradientBounds
