module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section
set_option autoImplicit false

/-! Measurable real-parameter derivatives of jointly measurable Lipschitz families.
Encoding the parameter curves in the actual compact-open continuous-map space
avoids assuming continuity in the auxiliary measurable parameter. -/
noncomputable section
namespace SHE.MeasuredRealCurves
open Set MeasureTheory Filter
open scoped Topology NNReal

variable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]

def curve (F : X → ℝ → E) (hF : ∀ x, Continuous (F x)) (x : X) : C(ℝ, E) :=
  ⟨F x, hF x⟩

theorem curve_measurable {F : X → ℝ → E} (hF : ∀ x, Continuous (F x))
    (hm : Measurable F.uncurry) : Measurable (curve F hF) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro θ
  exact hm.comp (measurable_id.prodMk measurable_const)

/-- The ordinary real-parameter derivative is jointly measurable even though the
auxiliary variable is merely measurable. -/
theorem derivative_measurable {F : X → ℝ → E} (hF : ∀ x, Continuous (F x))
    (hm : Measurable F.uncurry) :
    Measurable (fun p : X × ℝ => deriv (F p.1) p.2) := by
  have he : Continuous (fun p : C(ℝ, E) × ℝ => p.1 p.2) := by fun_prop
  have hd := measurable_deriv_with_param he
  exact hd.comp ((curve_measurable hF hm).prodMap measurable_id)

/-- The differentiability locus is jointly measurable without spatial
continuity. This is the point needed for honest Fubini of Rademacher's theorem. -/
theorem differentiability_measurableSet {F : X → ℝ → E}
    (hF : ∀ x, Continuous (F x)) (hm : Measurable F.uncurry) :
    MeasurableSet {p : X × ℝ | DifferentiableAt ℝ (F p.1) p.2} := by
  have he : Continuous (fun p : C(ℝ, E) × ℝ => p.1 p.2) := by fun_prop
  exact (measurableSet_of_differentiableAt_with_param ℝ he).preimage
    ((curve_measurable hF hm).prodMap measurable_id)

/-- Finite-dimensional Rademacher and genuine Fubini produce a simultaneous a.e. parameter
statement for the actual derivative field. -/
theorem ae_ae_hasDerivAt [FiniteDimensional ℝ E] (μ : Measure X) [SFinite μ]
    {F : X → ℝ → E} {K : X → ℝ≥0}
    (hm : Measurable F.uncurry) (hlip : ∀ x, LipschitzWith (K x) (F x)) :
    ∀ᵐ θ ∂volume, ∀ᵐ x ∂μ, HasDerivAt (F x) (deriv (F x) θ) θ := by
  have hset := differentiability_measurableSet (fun x => (hlip x).continuous) hm
  have hx : ∀ᵐ x ∂μ, ∀ᵐ θ ∂volume, DifferentiableAt ℝ (F x) θ :=
    ae_of_all _ (fun x => (hlip x).ae_differentiableAt_real)
  filter_upwards [(Measure.ae_ae_comm hset).mp hx] with θ hθ
  exact hθ.mono (fun _ hx => hx.hasDerivAt)

omit [MeasurableSpace X] in
/-- The Lipschitz constant bounds the actual vector derivative at every
parameter, including the zero derivative convention at exceptional points. -/
theorem derivative_norm_bound {F : X → ℝ → E} {K : X → ℝ≥0}
    (hlip : ∀ x, LipschitzWith (K x) (F x)) (x : X) (θ : ℝ) :
    ‖deriv (F x) θ‖ ≤ K x :=
  norm_deriv_le_of_lipschitz (hlip x)

omit [MeasurableSpace X] in
/-- Scalar compatibility with the original absolute-value interface. -/
theorem derivative_bound {F : X → ℝ → ℝ} {K : X → ℝ≥0}
    (hlip : ∀ x, LipschitzWith (K x) (F x)) (x : X) (θ : ℝ) :
    |deriv (F x) θ| ≤ K x := by
  simpa only [Real.norm_eq_abs] using derivative_norm_bound hlip x θ

end SHE.MeasuredRealCurves
