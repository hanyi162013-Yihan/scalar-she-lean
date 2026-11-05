module

public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.BDGKolmogorov
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The natural-number norm moments produced by native BDG satisfy the
public Kolmogorov-Chentsov interface. Heat-row moment bounds remain an
explicit analytic obligation, separate from this interface conversion. -/
theorem of_nat_moments {Ω T E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (X : T → Ω → E) (hX : ∀ t, Measurable (X t))
    (m : ℕ) (hm : 0 < m) (q : ℝ) (hq : 0 < q) (M : ℝ≥0)
    (hMoment : ∀ s t, (∫⁻ ω, ENNReal.ofReal (‖X s ω - X t ω‖ ^ m) ∂μ) ≤
      (M : ℝ≥0∞) * edist s t ^ q) :
    IsKolmogorovProcess X μ m q M := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology hX
  · intro s t
    convert hMoment s t using 1
    apply lintegral_congr
    intro ω
    rw [edist_dist, dist_eq_norm, ENNReal.rpow_natCast, ENNReal.ofReal_pow (norm_nonneg _)]
  · exact_mod_cast hm
  · exact hq

end SHEStochastic.BDGKolmogorov
