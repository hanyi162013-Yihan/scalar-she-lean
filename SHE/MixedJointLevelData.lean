module

public import SHE.MixedJointDefectFields
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedJointLevelData
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
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

def state (p : P) (ω : Ω) (t : ℝ) : WordRecursion.State n := JointWordAnalytic.state L Λ U V XU XV p ω t

def leaf (p : P) (ω : Ω) : ℝ := JointWordAnalytic.leaf L Λ U V XU XV p ω

def reference (p : P) (ω : Ω) : ℝ := JointWordAnalytic.reference L Λ U V XU XV p ω

def localRemainder (p : P) (ω : Ω) : ℝ := JointWordAnalytic.remainder L Λ U V XU XV p ω

def defect (p : (P×Ω)×ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L.observations.observations p.1.1) (p.2.toNNReal,p.1.2)

def mark (p : P) (ω : Ω) : ℝ := JointWordDefect.mark L Λ U V XU XV
  (defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L) p ω

theorem leaf_measurable : Measurable (fun p : P×Ω => leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p.1 p.2) :=
  JointWordAnalytic.leaf_measurable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable

theorem reference_measurable : Measurable (fun p : P×Ω => reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p.1 p.2) :=
  JointWordAnalytic.reference_measurable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable

theorem localRemainder_measurable : Measurable (fun p : P×Ω => localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p.1 p.2) :=
  JointWordAnalytic.remainder_measurable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable

theorem defect_measurable : Measurable (defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L) :=
  MixedJointDefectFields.defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L.observations

theorem mark_measurable : Measurable (fun p : P×Ω => mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p.1 p.2) :=
  JointWordDefect.mark_measurable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable
    (defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L)

theorem defect_bound (hΛ : 0≤Λ) (p : P) (ω : Ω) {t : ℝ} (ht : t∈Ioo R.base (L.terminal p)) (i j : Fin n) :
    |defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ((p,ω),t) i j|≤
      2*M*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) := by
  rw [defect,MixedJointDefectFields.defect_eq_matrix,Real.coe_toNNReal t (R.base_nonneg.trans ht.1.le)]
  exact JointNativeDefect.entry_bound hell hΛ _ _ _ _ _ ht.2 (L.stops_after p) (L.targets_after p) i j

theorem mark_uniform_bound (hΛ : 0≤Λ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,
    ‖mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω‖≤K ∧
      IntervalIntegrable (fun t => JointWordDefect.integrand L Λ U V XU XV
        (defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L) ((p,ω),t)) volume R.base (L.terminal p) :=
  JointWordDefect.uniform_bound L Λ (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable
    (defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L)
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (fun p ω t ht => defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ p ω ht)

end SHE.MixedJointLevelData
