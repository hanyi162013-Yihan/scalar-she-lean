/-
Copyright (c) 2026. Released under Apache 2.0 license.

The joint-law/Fubini proof follows Raphael Coelho's
MathFin.Foundations.SimpleDoleansExponential (Apache 2.0), generalized
from the real exponential to integrable Banach-valued kernels.
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalFreezing
open MeasureTheory ProbabilityTheory

variable {Ω A B E : Type*} {mΩ : MeasurableSpace Ω}
  [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A past-measurable parameter can be frozen inside an integrable kernel of
an independent random variable. The conclusion holds for the entire
given past sigma algebra; no regular conditional distribution is used. -/
theorem condExp_kernel_of_integrable (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → A} (hX : Measurable[m] X)
    {Z : Ω → B} (hZ : @Measurable Ω B mΩ ‹MeasurableSpace B› Z)
    (hindep : @Indep Ω (MeasurableSpace.comap Z ‹MeasurableSpace B›) m mΩ μ)
    {Ψ : A × B → E} (hΨ : StronglyMeasurable Ψ)
    (hint : letI : MeasurableSpace Ω := mΩ
      Integrable (fun ω ↦ Ψ (X ω, Z ω)) μ) :
    letI : MeasurableSpace Ω := mΩ
    μ[fun ω ↦ Ψ (X ω, Z ω) | m] =ᵐ[μ]
      (fun ω ↦ ∫ z, Ψ (X ω, z) ∂μ.map Z) := by
  letI : MeasurableSpace Ω := mΩ
  classical
  have hXm : Measurable X := hX.mono hm le_rfl
  let q : A → E := fun a ↦ ∫ z, Ψ (a, z) ∂μ.map Z
  have hq : StronglyMeasurable q := hΨ.integral_prod_right'
  have hiXZ : IndepFun X Z μ :=
    Indep.symm (indep_of_indep_of_le_right hindep hX.comap_le)
  have hjXZ : μ.map (fun ω ↦ (X ω, Z ω)) = (μ.map X).prod (μ.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hZ.aemeasurable).mp hiXZ
  have hf : Integrable (fun ω ↦ Ψ (X ω, Z ω)) μ := hint
  have hp : Integrable Ψ ((μ.map X).prod (μ.map Z)) := by
    rw [← hjXZ, integrable_map_measure hΨ.aestronglyMeasurable
      (hXm.prodMk hZ).aemeasurable]
    exact hint
  have hqi : Integrable (fun ω ↦ q (X ω)) μ :=
    (integrable_map_measure hq.aestronglyMeasurable hXm.aemeasurable).mp
      hp.integral_prod_left
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ ↦ hqi.integrableOn) (fun S hS _ ↦ ?_)
    (hq.comp_measurable hX).aestronglyMeasurable).symm
  have hSm : MeasurableSet S := hm S hS
  let Y : Ω → A × ℝ := fun ω ↦ (X ω, S.indicator (fun _ ↦ (1 : ℝ)) ω)
  let F : (A × ℝ) × B → E := fun p ↦ p.1.2 • Ψ (p.1.1, p.2)
  have hYm : Measurable Y := hXm.prodMk (measurable_const.indicator hSm)
  have hY : Measurable[m] Y := hX.prodMk (measurable_const.indicator hS)
  have hF : StronglyMeasurable F :=
    (measurable_fst.snd.stronglyMeasurable).smul
      (hΨ.comp_measurable (measurable_fst.fst.prodMk measurable_snd))
  have hi : IndepFun Y Z μ :=
    Indep.symm (indep_of_indep_of_le_right hindep hY.comap_le)
  have hjoint : μ.map (fun ω ↦ (Y ω, Z ω)) = (μ.map Y).prod (μ.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hZ.aemeasurable).mp hi
  have hYZ : AEMeasurable (fun ω ↦ (Y ω, Z ω)) μ := (hYm.prodMk hZ).aemeasurable
  have hFi : Integrable (fun ω ↦ F (Y ω, Z ω)) μ := by
    convert hf.indicator hSm using 1
    funext ω
    by_cases hω : ω ∈ S <;> simp [F, Y, hω]
  have hFp : Integrable F ((μ.map Y).prod (μ.map Z)) := by
    rw [← hjoint, integrable_map_measure hF.aestronglyMeasurable hYZ]
    exact hFi
  have hinner (y : A × ℝ) : ∫ z, F (y, z) ∂μ.map Z = y.2 • q y.1 := by
    exact integral_smul y.2 (fun z ↦ Ψ (y.1, z))
  have hqY : StronglyMeasurable (fun y : A × ℝ ↦ y.2 • q y.1) :=
    measurable_snd.stronglyMeasurable.smul (hq.comp_measurable measurable_fst)
  rw [← integral_indicator hSm, ← integral_indicator hSm]
  have hL : S.indicator (fun ω ↦ q (X ω)) = (fun ω ↦ (Y ω).2 • q (Y ω).1) := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [Y, hω]
  have hR : S.indicator (fun ω ↦ Ψ (X ω, Z ω)) = (fun ω ↦ F (Y ω, Z ω)) := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [F, Y, hω]
  rw [hL, hR, ← integral_map hYZ hF.aestronglyMeasurable, hjoint, integral_prod F hFp]
  rw [← integral_map hYm.aemeasurable hqY.aestronglyMeasurable]
  exact (integral_congr_ae (Filter.Eventually.of_forall hinner)).symm

/-- Bounded kernels are integrable automatically. -/
theorem condExp_kernel (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → A} (hX : Measurable[m] X)
    {Z : Ω → B} (hZ : @Measurable Ω B mΩ ‹MeasurableSpace B› Z)
    (hindep : @Indep Ω (MeasurableSpace.comap Z ‹MeasurableSpace B›) m mΩ μ)
    {Ψ : A × B → E} (hΨ : StronglyMeasurable Ψ)
    {K : ℝ} (_hK : 0 ≤ K) (hbound : ∀ p, ‖Ψ p‖ ≤ K) :
    letI : MeasurableSpace Ω := mΩ
    μ[fun ω ↦ Ψ (X ω, Z ω) | m] =ᵐ[μ]
      (fun ω ↦ ∫ z, Ψ (X ω, z) ∂μ.map Z) := by
  letI : MeasurableSpace Ω := mΩ
  exact condExp_kernel_of_integrable m hm hX hZ hindep hΨ
    ((integrable_const K).mono'
      (hΨ.comp_measurable ((hX.mono hm le_rfl).prodMk hZ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ hbound (X ω, Z ω)))

end SHEStochastic.ConditionalFreezing
