module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.TailIntegralUniformity
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Tail energy is controlled by an integral of tail probabilities.
The factor two allows a simple positive-part comparison and avoids any
regularity assumption on the distribution of f. -/
theorem tail_bound (f : Ω → ℝ) (hf : Measurable f) (R : ℝ) (hR : 0≤R) :
    (∫⁻ ω in {ω | R≤f ω},ENNReal.ofReal (f ω) ∂μ)≤
      2*(∫⁻ t in Ioi (R/2),μ {ω | t≤f ω}) := by
  let F := fun (ω : Ω) (t : ℝ) => (Ioc (R/2) (f ω)).indicator (fun _ => (1 : ℝ≥0∞)) t
  have hF : Measurable (fun z : Ω×ℝ => F z.1 z.2) := by
    have hs : MeasurableSet {z : Ω×ℝ | R/2<z.2 ∧ z.2≤f z.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (hf.comp measurable_fst))
    change Measurable ({z : Ω×ℝ | R/2<z.2 ∧ z.2≤f z.1}.indicator (fun _ => (1 : ℝ≥0∞)))
    exact measurable_const.indicator hs
  have hinner (ω : Ω) : (∫⁻ t,F ω t)=ENNReal.ofReal (f ω-R/2) := by
    rw [show (fun t => F ω t)=(Ioc (R/2) (f ω)).indicator (fun _ => (1 : ℝ≥0∞)) from rfl,
      lintegral_indicator measurableSet_Ioc,lintegral_const,one_mul,Measure.restrict_apply_univ,Real.volume_Ioc]
  have hrow (t : ℝ) : (∫⁻ ω,F ω t ∂μ)=if R/2<t then μ {ω | t≤f ω} else 0 := by
    by_cases ht : R/2<t
    · rw [if_pos ht]
      have he : (fun ω => F ω t)={ω | t≤f ω}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        simp only [F,Set.indicator_apply,Set.mem_Ioc,ht,true_and,Set.mem_setOf_eq]
      rw [he,lintegral_indicator (measurableSet_le measurable_const hf),lintegral_const,one_mul,Measure.restrict_apply_univ]
    · simp only [F,Set.indicator_apply,Set.mem_Ioc,ht,false_and,ite_false,lintegral_zero]
  rw [←lintegral_indicator (measurableSet_le measurable_const hf)]
  calc
    _ ≤ ∫⁻ ω,2*ENNReal.ofReal (f ω-R/2) ∂μ := by
      apply lintegral_mono
      intro ω
      by_cases h : R≤f ω
      · simp only [Set.indicator_apply,Set.mem_setOf_eq,h,ite_true]
        exact (ENNReal.ofReal_le_ofReal (by linarith : f ω≤2*(f ω-R/2))).trans_eq
          (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat])
      · simp only [Set.indicator_apply,Set.mem_setOf_eq,h,ite_false]
        exact bot_le
    _ = 2*(∫⁻ ω,ENNReal.ofReal (f ω-R/2) ∂μ) :=
      lintegral_const_mul'' _ (hf.sub_const _).ennreal_ofReal.aemeasurable
    _ = 2*(∫⁻ ω,∫⁻ t,F ω t ∂volume ∂μ) := by simp only [hinner]
    _ = 2*(∫⁻ t,∫⁻ ω,F ω t ∂μ ∂volume) := congrArg (fun z : ℝ≥0∞ => 2*z)
      (lintegral_lintegral_swap hF.aemeasurable)
    _ = _ := by
      congr 1
      rw [←lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        change (∫⁻ ω,F ω t ∂μ)=(Ioi (R/2)).indicator (fun t => μ {ω | t≤f ω}) t
        rw [hrow t]
        simp only [Set.indicator_apply,Set.mem_Ioi]

/-- A single integrable bound on scalar tail probabilities gives
uniformly vanishing tail energies, even across different probability
spaces. This is the uniform-integrability step needed for weak limits. -/
theorem uniform_tails {Ξ : ℕ → Type*} [∀ m,MeasurableSpace (Ξ m)]
    (P : ∀ m,Measure (Ξ m)) [∀ m,IsFiniteMeasure (P m)]
    (f : ∀ m,Ξ m → ℝ) (hf : ∀ m,Measurable (f m))
    (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) (hψfin : (∫⁻ t,ψ t)≠⊤)
    (htail : ∀ m t,0<t → (P m) {ω | t≤f m ω}≤ψ t) :
    Tendsto (fun N : ℕ => ⨆ m,∫⁻ ω in {ω | (N : ℝ)≤f m ω},ENNReal.ofReal (f m ω) ∂P m)
      atTop (𝓝 0) := by
  let F := fun (N : ℕ) => (Ioi ((N : ℝ)/2)).indicator ψ
  have hm (N : ℕ) : Measurable (F N) := hψ.indicator measurableSet_Ioi
  have hb (N : ℕ) : F N≤ψ := by
    intro t
    by_cases ht : (N : ℝ)/2<t
    · simp only [F,Set.indicator_apply,Set.mem_Ioi,ht,ite_true,le_refl]
    · simp only [F,Set.indicator_apply,Set.mem_Ioi,ht,ite_false]
      exact bot_le
  have hp (t : ℝ) : Tendsto (fun N => F N t) atTop (𝓝 0) := by
    obtain ⟨K,hK⟩ := exists_nat_gt (2*t)
    have he : (fun N => F N t)=ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
      apply eventually_atTop.mpr
      refine ⟨K,fun N hN => ?_⟩
      have hKN : (K : ℝ)≤N := by exact_mod_cast hN
      have ht : ¬(N : ℝ)/2<t := by linarith
      simp only [F,Set.indicator_apply,Set.mem_Ioi,ht,ite_false]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have hi : Tendsto (fun N => ∫⁻ t,F N t) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence ψ hm
      (fun N => Filter.Eventually.of_forall (hb N)) hψfin (Filter.Eventually.of_forall hp)
  have hi2 : Tendsto (fun N => 2*(∫⁻ t,F N t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hi (Or.inr (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi2 (fun _ => bot_le)
  intro N
  apply iSup_le
  intro m
  apply (tail_bound (P m) (f m) (hf m) (N : ℝ) (Nat.cast_nonneg N)).trans
  change 2*(∫⁻ t in Ioi ((N : ℝ)/2),(P m) {ω | t≤f m ω})≤2*(∫⁻ t,F N t)
  rw [show (∫⁻ t,F N t)=∫⁻ t in Ioi ((N : ℝ)/2),ψ t from lintegral_indicator measurableSet_Ioi ψ]
  apply mul_le_mul_right _ 2
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact htail m t (lt_of_le_of_lt (by positivity : (0 : ℝ)≤(N : ℝ)/2) ht)

end SHEStochastic.TailIntegralUniformity
