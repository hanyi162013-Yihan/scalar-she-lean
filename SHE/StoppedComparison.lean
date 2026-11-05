module

public import SHE.ChangeMeasure

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory
open scoped BoundedContinuousFunction

/-- Markov's exit bound on an actual exceptional event. -/
theorem exit_probability_le_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {R : Ω → ℝ} {B : Set Ω}
    (hB : MeasurableSet B) (hR : Integrable R μ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hexit : ∀ ω ∈ B, 1 ≤ R ω) : μ.real B ≤ ∫ ω, R ω ∂μ := by
  calc
    _ = ∫ ω, B.indicator (fun _ => (1:ℝ)) ω ∂μ :=
      (integral_indicator_one hB).symm
    _ ≤ _ := by
      apply integral_mono ((integrable_const (1:ℝ)).indicator hB) hR
      intro ω
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]
        exact hexit ω hω
      · rw [Set.indicator_of_notMem hω]
        exact hR0 ω

/-- The logarithm of the actual stopped exponential has the exact
reverse-entropy expectation. The martingale's mean-zero property is
the standard stochastic-calculus input. -/
theorem exponential_entropy_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {W V : Ω → ℝ}
    (hW : Integrable W μ) (hV : Integrable V μ) (hWmean : (∫ ω, W ω ∂μ)=0) :
    Integrable (fun ω => Real.log (Real.exp (-W ω-V ω/2))) μ ∧
    -(∫ ω, Real.log (Real.exp (-W ω-V ω/2)) ∂μ) = (∫ ω, V ω ∂μ)/2 := by
  have hi : Integrable (fun ω => -W ω-V ω/2) μ := hW.neg.sub (hV.div_const 2)
  constructor
  · simpa only [Real.log_exp] using hi
  · simp only [Real.log_exp]
    rw [integral_sub (f:=fun ω => -W ω) (g:=fun ω => V ω/2) hW.neg (hV.div_const 2),
      integral_neg, integral_div, hWmean]
    ring

section Laws
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Convert a genuine stopped-exponential witness and canonical
continuation into the bounded-test estimate used in law identification.
No measure-distance bound is assumed. -/
theorem stopped_exponential_law_comparison
    (controlled canonical : Ω → E) (P ν : ProbabilityMeasure E)
    {W V R : Ω → ℝ} {B : Set Ω}
    (hcontrolled : Measurable controlled) (hcanonical : Measurable canonical)
    (hP : (P : Measure E) = Measure.map controlled μ)
    (hν : (ν : Measure E) = Measure.map canonical
      (μ.withDensity (fun ω => ENNReal.ofReal (Real.exp (-W ω-V ω/2)))))
    (hW : Integrable W μ) (hV : Integrable V μ) (hR : Integrable R μ)
    (hWmean : (∫ ω, W ω ∂μ)=0)
    (hNovikov : (∫ ω, Real.exp (-W ω-V ω/2) ∂μ)=1)
    (hR0 : ∀ ω, 0 ≤ R ω) (hVR : ∀ ω, V ω ≤ R ω)
    (hB : MeasurableSet B) (hexit : ∀ ω ∈ B, 1 ≤ R ω)
    (hagree : ∀ ω ∉ B, controlled ω = canonical ω)
    (f : E →ᵇ ℝ) :
    |(∫ x, f x ∂P) - (∫ x, f x ∂ν)| ≤
      2 * ‖f‖ * (Real.sqrt (∫ ω, R ω ∂μ) + ∫ ω, R ω ∂μ) := by
  let Z : Ω → ℝ := fun ω => Real.exp (-W ω-V ω/2)
  have hZpos : ∀ ω, 0 < Z ω := fun ω => Real.exp_pos _
  have hZi : Integrable Z μ := by
    by_contra hnot
    have hz := integral_undef hnot
    rw [hNovikov] at hz
    norm_num at hz
  obtain ⟨hlog,hentropy⟩ := exponential_entropy_identity μ hW hV hWmean
  have hcost0 : 0 ≤ ∫ ω, R ω ∂μ := integral_nonneg hR0
  have hcost : -(∫ ω, Real.log (Z ω) ∂μ) ≤ (∫ ω, R ω ∂μ)/2 := by
    rw [hentropy]
    exact div_le_div_of_nonneg_right (integral_mono hV hR hVR) (by norm_num)
  have hfc : AEStronglyMeasurable (fun ω => f (controlled ω)) μ :=
    (f.continuous.measurable.comp hcontrolled).aestronglyMeasurable
  have hfn : AEStronglyMeasurable (fun ω => f (canonical ω)) μ :=
    (f.continuous.measurable.comp hcanonical).aestronglyMeasurable
  have hbf : ∀ x, |f x| ≤ ‖f‖ := fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hh := stopped_measure_comparison μ hZpos hZi hNovikov hlog hcost0 hcost hB
    (exit_probability_le_energy μ hB hR hR0 hexit) hfc hfn (norm_nonneg f)
    (fun ω => hbf _) (fun ω => hbf _) (fun ω hω => congrArg f (hagree ω hω))
  have hmapP : (∫ x, f x ∂P) = ∫ ω, f (controlled ω) ∂μ := by
    rw [hP]
    exact integral_map hcontrolled.aemeasurable f.continuous.aestronglyMeasurable
  have hmapν : (∫ x, f x ∂ν) = ∫ ω, f (canonical ω) ∂(μ.withDensity (fun ω => ENNReal.ofReal (Z ω))) := by
    rw [hν]
    exact integral_map hcanonical.aemeasurable f.continuous.aestronglyMeasurable
  rw [hmapP,hmapν]
  exact hh

end Laws
end SHE
