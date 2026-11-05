module

public import SHEStochastic.ScalarStoppedMeasureLimit
public import SHE.StandardTerminalLevy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedBrownianLimit
open MeasureTheory ProbabilityTheory Filter Set SHE
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (Qn : ℕ → Measure Ω)
  [∀ k,IsProbabilityMeasure (Qn k)]
  (good : ℕ → Set Ω) (hg : ∀ k,MeasurableSet (good k)) (hmon : Monotone good)
  (hExhaust : (⋃ k,good k)=univ)
  (hSame : ∀ k,(Qn k).restrict (good k)=Q.restrict (good k))

include hg hmon hExhaust hSame in
private theorem event {E : Type*} [MeasurableSpace E]
    (f : Ω → E) (fn : ℕ → Ω → E) (hfn : ∀ k,Measurable (fn k))
    (he : ∀ k,∀ᵐ ω ∂Q,ω∈good k → f ω=fn k ω)
    (A : Set E) (hA : MeasurableSet A) (B : Set Ω) (hB : MeasurableSet B) :
    Tendsto (fun k => (Qn k).real ((fn k) ⁻¹' A ∩ B)) atTop (𝓝 (Q.real (f ⁻¹' A ∩ B))) := by
  apply ScalarStoppedMeasureLimit.event_tendsto Q Qn good hg hmon hExhaust hSame
  · exact fun k => (hfn k hA).inter hB
  · intro k
    filter_upwards [he k] with ω hω hg
    change (f ω ∈ A ∧ ω ∈ B) ↔ (fn k ω ∈ A ∧ ω ∈ B)
    rw [hω hg]

include hg hmon hExhaust hSame in
private theorem real_eq {E : Type*} [MeasurableSpace E]
    (f : Ω → E) (fn : ℕ → Ω → E) (hfn : ∀ k,Measurable (fn k))
    (he : ∀ k,∀ᵐ ω ∂Q,ω∈good k → f ω=fn k ω)
    (A : Set E) (hA : MeasurableSet A) :
    Tendsto (fun k => (Qn k).real ((fn k) ⁻¹' A)) atTop (𝓝 (Q.real (f ⁻¹' A))) := by
  simpa only [inter_univ] using event Q Qn good hg hmon hExhaust hSame f fn hfn he A hA univ MeasurableSet.univ

private theorem of_real_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) [IsFiniteMeasure m] [IsFiniteMeasure ν]
    {A : Set X} {B : Set Y} (h : m.real A=ν.real B) : m A=ν B := by
  simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using congrArg ENNReal.ofReal h

include hg hmon hExhaust hSame in
/-- Exact finite Brownian laws and full-past increment independence
pass from the stopped changed measures to the uncapped changed law. -/
theorem finite_law {n : ℕ} (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → ℝ≥0 → Ω → ℝ) (Xn : ℕ → Fin n → ℝ≥0 → Ω → ℝ)
    (hm : ∀ i t,Measurable (X i t)) (hmn : ∀ k i t,Measurable (Xn k i t))
    (he : ∀ k i t,∀ᵐ ω ∂Q,ω∈good k → X i t ω=Xn k i t ω)
    (hLaw : ∀ k,FiniteBrownianLawOn F (Qn k) H (Xn k) G) :
    FiniteBrownianLawOn F Q H X G := by
  constructor
  · intro t ht
    let f (ω : Ω) : WordRecursion.State n := WithLp.toLp 2 (fun i => X i (t i) ω)
    let fn (k : ℕ) (ω : Ω) : WordRecursion.State n := WithLp.toLp 2 (fun i => Xn k i (t i) ω)
    let γ := multivariateGaussian (0 : WordRecursion.State n)
      (fun i j => (min (t i) (t j) : ℝ≥0) * G i j)
    have hf : Measurable f := (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval (fun i => hm i (t i)))
    have hfn (k : ℕ) : Measurable (fn k) :=
      (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval (fun i => hmn k i (t i)))
    have hfg (k : ℕ) : ∀ᵐ ω ∂Q,ω∈good k → f ω=fn k ω := by
      filter_upwards [ae_all_iff.mpr (fun i => he k i (t i))] with ω hω hgood
      exact congrArg (WithLp.toLp 2) (funext fun i => hω i hgood)
    refine ⟨hf.aemeasurable,?_⟩
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply hf hA]
    have hmap (k : ℕ) : (Qn k) ((fn k) ⁻¹' A)=γ A := by
      have h := ((hLaw k).1 t ht).map_eq
      change (Qn k).map (fn k)=γ at h
      simpa only [Measure.map_apply (hfn k) hA] using congrArg (fun m : Measure (WordRecursion.State n) => m A) h
    have hl := real_eq Q Qn good hg hmon hExhaust hSame f fn hfn hfg A hA
    simp only [Measure.real,hmap] at hl
    exact of_real_eq Q γ (tendsto_nhds_unique hl tendsto_const_nhds)
  · intro s t hst ht
    let f (ω : Ω) : WordRecursion.State n := WithLp.toLp 2 (fun i => X i t ω-X i s ω)
    let fn (k : ℕ) (ω : Ω) : WordRecursion.State n := WithLp.toLp 2 (fun i => Xn k i t ω-Xn k i s ω)
    have hf : Measurable f := (WithLp.measurable_toLp 2 _).comp
      (Measurable.of_eval (fun i => (hm i t).sub (hm i s)))
    have hfn (k : ℕ) : Measurable (fn k) := (WithLp.measurable_toLp 2 _).comp
      (Measurable.of_eval (fun i => (hmn k i t).sub (hmn k i s)))
    have hfg (k : ℕ) : ∀ᵐ ω ∂Q,ω∈good k → f ω=fn k ω := by
      filter_upwards [ae_all_iff.mpr (fun i => he k i t),ae_all_iff.mpr (fun i => he k i s)] with ω ht hs hgood
      exact congrArg (WithLp.toLp 2) (funext fun i => congrArg₂ (·-·) (ht i hgood) (hs i hgood))
    apply (indep_iff_forall_indepSet Q).mpr
    intro A B hA hB
    change MeasurableSet[(inferInstance : MeasurableSpace (WordRecursion.State n)).comap f] A at hA
    obtain ⟨A',hA',hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
    rw [←hpre]
    have hB' := F.le s B hB
    apply (indepSet_iff_measure_inter_eq_mul (hf hA') hB' Q).mpr
    have hI := event Q Qn good hg hmon hExhaust hSame f fn hfn hfg A' hA' B hB'
    have hA₁ := real_eq Q Qn good hg hmon hExhaust hSame f fn hfn hfg A' hA'
    have hB₁ : Tendsto (fun k => (Qn k).real B) atTop (𝓝 (Q.real B)) :=
      ScalarStoppedMeasureLimit.event_tendsto Q Qn good hg hmon hExhaust hSame B (fun _ => B)
        (fun _ => hB') (fun _ => Filter.Eventually.of_forall fun _ _ => Iff.rfl)
    have hFn (k : ℕ) : (Qn k).real ((fn k) ⁻¹' A'∩B)=(Qn k).real ((fn k) ⁻¹' A')*(Qn k).real B := by
      have h := (hLaw k).2 s t hst ht
      have hi : IndepSet ((fn k) ⁻¹' A') B (Qn k) :=
        h.indepSet_of_measurableSet (MeasurableSpace.measurableSet_comap.mpr ⟨A',hA',rfl⟩) hB
      simpa only [Measure.real,ENNReal.toReal_mul] using congrArg ENNReal.toReal hi.measure_inter_eq_mul
    have hl : Q.real (f ⁻¹' A'∩B)=Q.real (f ⁻¹' A')*Q.real B :=
      tendsto_nhds_unique hI (by simpa only [←hFn] using hA₁.mul hB₁)
    simpa only [Measure.real,ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] using congrArg ENNReal.ofReal hl

end SHEStochastic.ScalarStoppedBrownianLimit
