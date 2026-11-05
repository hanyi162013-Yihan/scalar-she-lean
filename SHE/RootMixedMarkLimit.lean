module

public import SHE.MixedJointLevelData
public import SHE.RootJointHessian
public import SHE.NativeRowTargetContinuity
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.RootMixedMarkLimit
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance rootMixedMarkLimitInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance rootMixedMarkLimitInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance rootMixedMarkLimitInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance rootMixedMarkLimitInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance rootMixedMarkLimitInstance5 : MeasurableSpace CircleL2 := borel _
local instance rootMixedMarkLimitInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance rootMixedMarkLimitInstance7 : MeasurableSpace RealL2 := borel _
local instance rootMixedMarkLimitInstance8 : BorelSpace RealL2 := ⟨rfl⟩
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

open CutoffWordHistories RootHeatBounds RootHeatTargets Filter Topology
variable (δ : ℝ) (hδ : 0<δ)

def mark (ε : ℝ≥0) (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (level L δ hδ ε k) p ω

theorem continuous_defect (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t∈Ioo R.base ((level L δ hδ 0 k).terminal p)) :
    Continuous (fun ε : ℝ≥0 => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (level L δ hδ ε k) ((p,ω),t)) := by
  let Z := fun ε : ℝ≥0 => (level L δ hδ ε k).observations.observations p
  have hσ (i : Fin (n+k)) : Continuous (fun ε : ℝ≥0 => (Z ε i).stop) := by
    convert (continuous_const (y := (Z 0 i).stop)) using 1
    funext ε
    exact stop_eq L δ hδ ε 0 k p i
  have hgap (ε : ℝ≥0) (i : Fin (n+k)) : (t.toNNReal:ℝ)<(Z ε i).target := by
    rw [Real.coe_toNNReal t (R.base_nonneg.trans ht.1.le)]
    have hh := (level L δ hδ ε k).targets_after p i
    rw [terminal_eq L δ hδ ε 0 k p] at hh
    exact ht.2.trans_le hh
  have hc := NativeRowTargetContinuity.matrix_continuous hell Λ
    (fun ε i => (Z ε i).stop) (fun ε i => (Z ε i).target) (fun i => (Z 0 i).center)
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (t.toNNReal,ω))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second (t.toNNReal,ω))
    (t.toNNReal:ℝ) hσ (target_continuous L δ hδ k p) hgap
  convert hc using 1
  funext ε
  rw [MixedJointLevelData.defect,MixedJointDefectFields.defect_eq_matrix]
  congr 1
  funext i
  exact center_eq L δ hδ ε 0 k p i

theorem continuous_integrand (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t∈Ioo R.base ((level L δ hδ 0 k).terminal p)) :
    Continuous (fun ε : ℝ≥0 => JointWordDefect.integrand (level L δ hδ ε k) Λ U V XU XV
      (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k))
      ((p,ω),t)) := by
  have hE := continuous_defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k p ω ht
  have hH := RootJointHessian.continuous_field L δ hδ Λ U V XU XV k p ω ht.2
  apply Continuous.const_mul
  unfold covarianceAction
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply j).comp (continuous_apply i)).comp hE).mul
    ((hH.clm_apply continuous_const).clm_apply continuous_const)

theorem uniform_integrand_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ ε : ℝ≥0,∀ p ω t,
    t∈Ioo R.base ((level L δ hδ 0 k).terminal p) →
    ‖JointWordDefect.integrand (level L δ hδ ε k) Λ U V XU XV
      (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k))
      ((p,ω),t)‖≤K*(1+heatConstant*((level L δ hδ 0 k).terminal p-t)^(-(1/2:ℝ))) := by
  obtain ⟨B,hBn,hB⟩ := RootJointHessian.field_uniform_bound L δ hδ Λ U V XU XV k
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  refine ⟨((n+k:ℕ):ℝ)^2*M*B,by positivity,fun ε p ω t ht => ?_⟩
  have hte : t∈Ioo R.base ((level L δ hδ ε k).terminal p) := by
    rw [terminal_eq L δ hδ ε 0 k p]
    exact ht
  have hh := JointWordDefect.integrand_bound (level L δ hδ ε k) Λ hM hBn
    (fun q => hB ε q.1.1 q.1.2 q.2)
    (fun p ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (level L δ hδ ε k) hΛ p ω ht) p ω hte
  rw [terminal_eq L δ hδ ε 0 k p] at hh
  exact hh

end SHE.RootMixedMarkLimit
