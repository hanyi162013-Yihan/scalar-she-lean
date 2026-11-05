module

public import SHE.MixedNativeJointPhysical
public import SHE.JointDefectAction
public import SHE.VariableObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.MixedJointDefectFields
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianTaylorAverage VariableObservations
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

theorem defect_eq_matrix {n : ℕ} (Z : Fin n→WordRecursion.Observation) (p : ℝ≥0×Ω) :
    MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p=
      JointNativeDefect.matrix hell Λ (fun i => (Z i).stop) (fun i => (Z i).target)
        (fun i => (Z i).center)
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first p)
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second p) (p.1:ℝ) := rfl

/-- Joint Borel dependence of the literal constructed pair's defect on
all variable observations, sample and real time. In particular history
integration does not require choosing measurable stochastic versions. -/
theorem defect_measurable {P : Type*} [MeasurableSpace P] {n : ℕ} (Z : Family P n) :
    Measurable (fun p : (P×Ω)×ℝ =>
      MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (Z.observations p.1.1) (p.2.toNNReal,p.1.2)) := by
  have hp : Measurable (fun p : (P×Ω)×ℝ => (p.2.toNNReal,p.1.2)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst.snd
  have hf := (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp hp
  have hg := (S.second_coefficient.mono (predictable_le_product 𝓕)).measurable.comp hp
  have hr : Measurable (fun p : (P×Ω)×ℝ => (p.2.toNNReal:ℝ)) :=
    measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_snd)
  have hm := JointNativeDefect.measurable_comp hell Λ
    (σ := fun p : (P×Ω)×ℝ => fun i => (Z.observations p.1.1 i).stop)
    (T := fun p : (P×Ω)×ℝ => fun i => (Z.observations p.1.1 i).target)
    (x := fun p : (P×Ω)×ℝ => fun i => (Z.observations p.1.1 i).center)
    (fun i => (Z.stop_measurable i).comp measurable_fst.fst)
    (fun i => (Z.target_measurable i).comp measurable_fst.fst)
    (fun i => (Z.center_measurable i).comp measurable_fst.fst) hf hg hr
  exact hm

/-- Actual terminal-time integrability of the retained first-defect
mark for the mixed pair. Original stops may extend beyond this window;
only stop>=right and heat target>=right are used. -/
theorem action_intervalIntegrable (hΛ : 0≤Λ) {n : ℕ} (Z : Fin n→WordRecursion.Observation)
    {q s : ℝ} (hq : 0≤q) (hqs : q≤s)
    (hstop : ∀ i,s≤(Z i).stop) (htarget : ∀ i,s≤(Z i).target) (ω : Ω)
    {A : ℝ→(WordRecursion.State n→L[ℝ]WordRecursion.State n→L[ℝ]ℝ)} (hA : Measurable A)
    {B : ℝ} (hB : 0≤B) (hbound : ∀ r ∈ Icc q s,‖A r‖≤B) :
    IntervalIntegrable (fun r => covarianceAction
      (MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z
        (r.toNNReal,ω)) (A r)) volume q s := by
  have hp : Measurable (fun r : ℝ => (r.toNNReal,ω)) :=
    measurable_real_toNNReal.prodMk measurable_const
  have hf := (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp hp
  have hg := (S.second_coefficient.mono (predictable_le_product 𝓕)).measurable.comp hp
  have hi := JointDefectAction.action_intervalIntegrable hell hΛ
    (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center)
    hf hg hqs hstop htarget hA hB hbound
  apply hi.congr_uIoo
  intro r hr
  rw [uIoo_of_le hqs] at hr
  dsimp only [Function.comp_apply]
  rw [defect_eq_matrix,Real.coe_toNNReal r (hq.trans hr.1.le)]

end SHE.MixedJointDefectFields
