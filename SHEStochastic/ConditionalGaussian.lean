module

public import SHEStochastic.ConditionalFreezing
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalFreezing
open MeasureTheory ProbabilityTheory Matrix

variable {Ω C : Type*} {mΩ : MeasurableSpace Ω}
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Conditional characteristic functions with a random past-measurable
frequency. The frequency need not be bounded. -/
theorem condExp_charFun (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X Z : Ω → C} (hX : Measurable[m] X) (hZ : @Measurable Ω C mΩ _ Z)
    (hi : @Indep Ω (MeasurableSpace.comap Z ‹MeasurableSpace C›) m mΩ μ) :
    letI : MeasurableSpace Ω := mΩ
    μ[fun ω ↦ Complex.exp ((inner ℝ (Z ω) (X ω) : ℂ) * Complex.I) | m] =ᵐ[μ]
      (fun ω ↦ charFun (μ.map Z) (X ω)) := by
  letI : MeasurableSpace Ω := mΩ
  exact condExp_kernel m hm hX hZ hi
    (Ψ := fun p : C × C ↦ Complex.exp ((inner ℝ p.2 p.1 : ℂ) * Complex.I))
    (by fun_prop) (K := 1) (by norm_num)
    (fun p ↦ by simp only [Complex.norm_exp_ofReal_mul_I, le_refl])

/-- A centered finite-dimensional Gaussian increment can be frozen
against an arbitrary random vector known at the left endpoint. -/
theorem condExp_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X Z : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable[m] X) (hZ : @Measurable Ω (EuclideanSpace ℝ ι) mΩ _ Z)
    (hi : @Indep Ω (MeasurableSpace.comap Z inferInstance) m mΩ μ)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hlaw : HasLaw Z (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) μ) :
    letI : MeasurableSpace Ω := mΩ
    μ[fun ω ↦ Complex.exp ((inner ℝ (Z ω) (X ω) : ℂ) * Complex.I) | m] =ᵐ[μ]
      (fun ω ↦ Complex.exp (-((X ω ⬝ᵥ S *ᵥ X ω : ℝ) : ℂ) / 2)) := by
  letI : MeasurableSpace Ω := mΩ
  simpa only [hlaw.map_eq, charFun_multivariateGaussian hS, inner_zero_right,
    Complex.ofReal_zero, zero_mul, zero_sub, neg_div] using condExp_charFun m hm hX hZ hi

end SHEStochastic.ConditionalFreezing
