module

public import SHE.HaarCovariance
public import SHE.BesselSynthesis
public import SHE.CircleMultiplier
public import SHE.SynthesisEquivalence

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar

open Finset Matrix MeasureTheory AddCircle CircleHeat
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev HaarInput := lp (fun _ : HaarNode => ℂ) 2

theorem elliptic_upper_nonneg (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) : 0 ≤ U := by
  have hh := localAverage_bounds_ae 0 f m U hfbound ()
  exact hm.le.trans (hh.1.trans hh.2)

def factorAnalysis (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) : CircleL2 →L[ℂ] HaarInput :=
  BesselSynthesis.analysis (fun q => globalHaarColumn q f)
    (fun v => (globalHaarColumn_bessel f m U hm hfreal hfbound v).1)
    U (elliptic_upper_nonneg f m U hm hfbound)
    (fun v => (globalHaarColumn_bessel f m U hm hfreal hfbound v).2)

/-- The genuine bounded infinite weighted-Haar factor, synthesized from
the actual physical countable columns. -/
def factor (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) : HaarInput →L[ℂ] CircleL2 :=
  (factorAnalysis f m U hm hfreal hfbound).adjoint

@[simp] theorem factorAnalysis_apply (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) (q : HaarNode) :
    factorAnalysis f m U hm hfreal hfbound v q = inner ℂ (globalHaarColumn q f) v := rfl

@[simp] theorem factor_single (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (q : HaarNode) :
    factor f m U hm hfreal hfbound (lp.single 2 q 1) = globalHaarColumn q f := by
  apply ext_inner_right ℂ
  intro v
  rw [factor, ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left]
  simp [RCLike.inner_apply]

@[simp] theorem factor_adjoint (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    (factor f m U hm hfreal hfbound).adjoint = factorAnalysis f m U hm hfreal hfbound := by
  simp [factor]

theorem factorAnalysis_norm_sq (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    ‖factorAnalysis f m U hm hfreal hfbound v‖ ^ 2 =
      ∑' q : HaarNode, ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2 :=
  BesselSynthesis.analysis_norm_sq _ _ _ _ _ v

theorem factorAnalysis_complexStep_norm_sq (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (k : ℕ) (a b : Grid k → ℝ) :
    ‖factorAnalysis f m U hm hfreal hfbound (DyadicApproximation.complexGridStep k a b)‖ ^ 2 =
      (inner ℂ (CircleMultiplier.operator f U (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound)
        (DyadicApproximation.complexGridStep k a b)) (DyadicApproximation.complexGridStep k a b)).re := by
  rw [factorAnalysis_norm_sq,
    globalHaarColumn_complexStep_covariance_energy f m U hm hfreal hfbound k a b,
    CircleMultiplier.operator_complexStep_quadratic]

/-- Exact covariance energy for every complex circle `L²` test. -/
theorem factorAnalysis_covariance_energy (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    ‖factorAnalysis f m U hm hfreal hfbound v‖ ^ 2 =
      (inner ℂ (CircleMultiplier.operator f U (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound) v) v).re := by
  let M := CircleMultiplier.operator f U (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound)
  have hv := DyadicApproximation.complexAverage_tendsto v
  have hleft := ((factorAnalysis f m U hm hfreal hfbound).continuous.tendsto v |>.comp hv).norm.pow 2
  have hinner : Filter.Tendsto
      (fun N => inner ℂ (M (DyadicApproximation.complexAverage N v)) (DyadicApproximation.complexAverage N v))
      Filter.atTop (nhds (inner ℂ (M v) v)) :=
    ((M.continuous.tendsto v).comp hv).inner hv
  have hright := (Complex.continuous_re.tendsto _).comp hinner
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall (fun N =>
    (factorAnalysis_complexStep_norm_sq f m U hm hfreal hfbound N _ _).symm)

/-- Literal operator covariance: the constructed infinite factor times its
Hilbert adjoint is actual pointwise multiplication by the coefficient. -/
theorem factor_covariance (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    (factor f m U hm hfreal hfbound).comp (factor f m U hm hfreal hfbound).adjoint =
      CircleMultiplier.operator f U (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound) := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map _ _).mp
  intro v
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, factor_adjoint,
    factor, ContinuousLinearMap.adjoint_inner_left]
  apply Complex.ext
  · change RCLike.re (inner ℂ (factorAnalysis f m U hm hfreal hfbound v)
      (factorAnalysis f m U hm hfreal hfbound v)) = _
    rw [← InnerProductSpace.norm_sq_eq_re_inner]
    exact factorAnalysis_covariance_energy f m U hm hfreal hfbound v
  · change RCLike.im (inner ℂ (factorAnalysis f m U hm hfreal hfbound v)
      (factorAnalysis f m U hm hfreal hfbound v)) = _
    rw [inner_self_im]
    exact (CircleMultiplier.operator_self_inner_im f U _ hfreal v).symm

end SHE.FiniteHaar
