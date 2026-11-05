module

public import SHE.NativeJointHistory
public import SHE.MixedNativeJointHistory
public import SHE.CutoffWordLevel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeJointHistory
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation VariableObservations CutoffWordLevel
open scoped NNReal ENNReal
local instance jointHistoryFieldsInstance1 : MeasurableSpace RealL2 := borel _
local instance jointHistoryFieldsInstance2 : BorelSpace RealL2 := ⟨rfl⟩
local instance jointHistoryFieldsInstance3 : MeasurableSpace CircleL2 := borel _
local instance jointHistoryFieldsInstance4 : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)

/-- Literal family-dependent actual joint state is Borel in history,
sample and real time, with every original stop and target retained. -/
theorem evaluate_measurable {n : ℕ} (Z : Family P n) :
    Measurable (fun p : (P×Ω)×ℝ => evaluate 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (Z.observations p.1.1) p.1.2 p.2) := by
  let U := firstData 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
  let V := secondData 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
  exact JointWordObserve.evaluate_measurable (reindexFamily Z Prod.fst measurable_fst) Λ
    (U.physicalState_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
    (V.physicalState_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
    (U.physicalField_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
    (V.physicalField_measurable.comp (measurable_fst.snd.prodMk measurable_snd))

theorem evaluate_fixed_measurable {n : ℕ} (Z : Family P n) (q : ℝ) :
    Measurable (fun p : P×Ω => evaluate 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (Z.observations p.1) p.2 q) :=
  (evaluate_measurable 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z).comp
    (measurable_id.prodMk measurable_const)

end SHE.NativeJointHistory

namespace SHE.MixedNativeJointHistory
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation VariableObservations CutoffWordLevel
open scoped NNReal ENNReal
local instance jointHistoryFieldsInstance5 : MeasurableSpace RealL2 := borel _
local instance jointHistoryFieldsInstance6 : BorelSpace RealL2 := ⟨rfl⟩
local instance jointHistoryFieldsInstance7 : MeasurableSpace CircleL2 := borel _
local instance jointHistoryFieldsInstance8 : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

/-- Literal family-dependent actual joint state is Borel in history,
sample and real time, with every original stop and target retained. -/
theorem evaluate_measurable {n : ℕ} (Z : Family P n) :
    Measurable (fun p : (P×Ω)×ℝ => evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (Z.observations p.1.1) p.1.2 p.2) := by
  let U := firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  let V := secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  exact JointWordObserve.evaluate_measurable (reindexFamily Z Prod.fst measurable_fst) Λ
    (U.physicalState_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
    (V.physicalState_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
    (U.physicalField_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
    (V.physicalField_measurable.comp (measurable_fst.snd.prodMk measurable_snd))

theorem evaluate_fixed_measurable {n : ℕ} (Z : Family P n) (q : ℝ) :
    Measurable (fun p : P×Ω => evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (Z.observations p.1) p.2 q) :=
  (evaluate_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z).comp
    (measurable_id.prodMk measurable_const)

end SHE.MixedNativeJointHistory
