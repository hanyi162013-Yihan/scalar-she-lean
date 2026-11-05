module

public import SHEStochastic.CompactUniformIntegral
public import SHEStochastic.CompactUniformComposition
public import SHEStochastic.UniformEnergyBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.WeakLimitUniformEnergy
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E]

/-- Moving continuous tests of at most linear energy growth pass to
weak limits when the continuous nonnegative energy has uniformly
vanishing tails. Only first energy moments are used. -/
theorem integral_tendsto (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : Tendsto P atTop (𝓝 Q))
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (energy : E → ℝ) (he : Continuous energy) (hpos : ∀ x,0≤energy x)
    (hUI : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤energy x},
      ENNReal.ofReal (energy x) ∂(P m).toMeasure) atTop (𝓝 0))
    (f : ℕ → E → ℝ) (hf : ∀ m,Continuous (f m)) (g : E → ℝ) (hg : Continuous g)
    (hlim : ∀ K : Set E,IsCompact K → TendstoUniformlyOn f g atTop K)
    (C : ℝ) (hC : 0≤C) (hfgrowth : ∀ m x,|f m x|≤C*(1+energy x))
    (hggrowth : ∀ x,|g x|≤C*(1+energy x)) :
    (∀ m,Integrable (f m) (P m).toMeasure) ∧ Integrable g Q.toMeasure ∧
      Tendsto (fun m => ∫ x,f m x ∂(P m).toMeasure) atTop (𝓝 (∫ x,g x ∂Q.toMeasure)) := by
  obtain ⟨D,hD,hEnergy⟩ := UniformEnergyBound.exists_bound (fun m => (P m).toMeasure)
    (fun _ => energy) (fun _ => he.measurable) (fun _ => hpos) hUI
  have hQE := (WeakLimitMomentTests.nonnegative_bound P Q hP energy he hpos D
    (fun m => (hEnergy m).1) (fun m => (hEnergy m).2)).1
  have hi (m : ℕ) : Integrable (f m) (P m).toMeasure :=
    (((integrable_const (1 : ℝ)).add (hEnergy m).1).const_mul C).mono'
      (hf m).aestronglyMeasurable (Filter.Eventually.of_forall (hfgrowth m))
  have hgi : Integrable g Q.toMeasure :=
    (((integrable_const (1 : ℝ)).add hQE).const_mul C).mono'
      hg.aestronglyMeasurable (Filter.Eventually.of_forall hggrowth)
  refine ⟨hi,hgi,Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  have hε3 : 0<ε/3 := by positivity
  have hsource : Tendsto (fun R : ℕ => ENNReal.ofReal (2*C)*
      (⨆ m,∫⁻ x in {x | (R : ℝ)≤energy x},ENNReal.ofReal (energy x) ∂(P m).toMeasure))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2*C)) hUI
      (Or.inr ENNReal.ofReal_ne_top)
  have htarget : Tendsto (fun R : ℕ => ENNReal.ofReal (2*C)*
      (∫⁻ x in {x | (R : ℝ)≤energy x},ENNReal.ofReal (energy x) ∂Q.toMeasure)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2*C))
      (EnergyClipping.tails_tendsto Q.toMeasure energy he.measurable hQE) (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨R,hRsource,hRtarget,hR⟩ :=
    ((hsource.eventually_lt_const (ENNReal.ofReal_pos.mpr hε3)).and
      ((htarget.eventually_lt_const (ENNReal.ofReal_pos.mpr hε3)).and (eventually_ge_atTop (1 : ℕ)))).exists
  have hRr : (1 : ℝ)≤R := by exact_mod_cast hR
  let L : ℝ := C*(1+(R : ℝ))
  have hL : 0≤L := by dsimp only [L];positivity
  let cf := fun m => WeakLimitMomentTests.clip (f m) (hf m) L hL
  let cg := WeakLimitMomentTests.clip g hg L hL
  have hcliplim (K : Set E) (hK : IsCompact K) :
      TendstoUniformlyOn (fun m x => cf m x) cg atTop K := by
    simpa only [cf,cg,WeakLimitMomentTests.clip,BoundedContinuousFunction.coe_ofNormedAddCommGroup,
      Function.comp_def] using CompactUniformComposition.postcompose hK hf hg (hlim K hK)
        (fun x : ℝ => max (-L) (min L x)) (continuous_const.max (continuous_const.min continuous_id))
  have hclip := CompactUniformIntegral.tendsto P Q hP hTight cf cg L hL
    (fun m x => EnergyClipping.clip_norm (f m) (hf m) L hL x)
    (EnergyClipping.clip_norm g hg L hL) hcliplim
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hclip (ε/3) hε3
  refine ⟨N,fun m hm => ?_⟩
  have h1 : ‖(∫ x,f m x ∂(P m).toMeasure)-(∫ x,cf m x ∂(P m).toMeasure)‖<ε/3 := by
    apply (ENNReal.ofReal_lt_ofReal_iff hε3).mp
    apply (EnergyClipping.integral_bound (P m).toMeasure (f m) (hf m) (hi m) energy
      he.measurable C R hC hRr (hfgrowth m)).trans_lt
    exact (mul_le_mul_right (le_iSup (fun j => ∫⁻ x in {x | (R : ℝ)≤energy x},
      ENNReal.ofReal (energy x) ∂(P j).toMeasure) m) _).trans_lt hRsource
  have h2 : ‖(∫ x,g x ∂Q.toMeasure)-(∫ x,cg x ∂Q.toMeasure)‖<ε/3 := by
    apply (ENNReal.ofReal_lt_ofReal_iff hε3).mp
    exact (EnergyClipping.integral_bound Q.toMeasure g hg hgi energy he.measurable
      C R hC hRr hggrowth).trans_lt hRtarget
  have h3 := hN m hm
  have ht := dist_triangle (∫ x,f m x ∂(P m).toMeasure)
    (∫ x,cf m x ∂(P m).toMeasure) (∫ x,g x ∂Q.toMeasure)
  have ht' := dist_triangle (∫ x,cf m x ∂(P m).toMeasure)
    (∫ x,cg x ∂Q.toMeasure) (∫ x,g x ∂Q.toMeasure)
  rw [dist_comm (∫ x,cg x ∂Q.toMeasure) (∫ x,g x ∂Q.toMeasure)] at ht'
  simp only [dist_eq_norm] at ht ht' h3 ⊢
  linarith

end SHEStochastic.WeakLimitUniformEnergy
