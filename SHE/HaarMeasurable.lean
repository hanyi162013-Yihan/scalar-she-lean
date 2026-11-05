module

public import SHE.HaarUnitary
public import SHE.StrongOperator
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar

open Finset MeasureTheory AddCircle CircleHeat
open scoped ENNReal NNReal
local instance haarMeasurable_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance haarMeasurable_exponentFinite : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance haarMeasurable_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarMeasurable_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarMeasurable_inputSigma : MeasurableSpace HaarInput := borel HaarInput
local instance haarMeasurable_inputBorel : BorelSpace HaarInput := ⟨rfl⟩

/-- Actual real uniformly elliptic coefficient fields, with their inherited
circle `L²` topology and Borel structure. -/
abbrev EllipticField (m U : ℝ) := {f : CircleL2 //
  (∀ᵐ y ∂haarAddCircle, (f y).im = 0) ∧
    (∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)}

def fieldFactor (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) : HaarInput →L[ℂ] CircleL2 :=
  factor f.1 m U hm f.2.1 f.2.2

def fieldFactorEquivalence (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) : HaarInput ≃L[ℂ] CircleL2 :=
  factorEquivalence f.1 m U hm f.2.1 f.2.2

theorem factor_operator_norm_le (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    ‖factor f m U hm hfreal hfbound‖ ≤ Real.sqrt U := by
  calc
    _ = ‖factorAnalysis f m U hm hfreal hfbound‖ := ContinuousLinearMap.adjoint.norm_map _
    _ ≤ _ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg U)
      intro v
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg U) (norm_nonneg v))).mp
      rw [mul_pow, Real.sq_sqrt (elliptic_upper_nonneg f m U hm hfbound), factorAnalysis_norm_sq]
      exact (globalHaarColumn_bessel f m U hm hfreal hfbound v).2

theorem fieldFactor_bound (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) (x : HaarInput) :
    ‖fieldFactor m U hm f x‖ ≤ Real.sqrt U * ‖x‖ := by
  exact ((fieldFactor m U hm f).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (factor_operator_norm_le f.1 m U hm f.2.1 f.2.2) (norm_nonneg _))

theorem continuous_fieldColumn (m U : ℝ) (hm : 0 < m) (q : HaarNode) :
    Continuous (fun f : EllipticField m U => globalHaarColumn q f.1) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  exact (continuousAt_globalHaarColumn q f.1 m U hm f.2.2).comp continuous_subtype_val.continuousAt

/-- Strong continuity of the actual infinite factor, proved from its
physical columns and a uniform operator bound. -/
theorem continuous_fieldFactor_action (m U : ℝ) (hm : 0 < m) (x : HaarInput) :
    Continuous (fun f : EllipticField m U => fieldFactor m U hm f x) := by
  let P : ℕ → HaarInput := fun N => ∑ q ∈ nodesBelow N, lp.single 2 q (x q)
  have hp : Filter.Tendsto P Filter.atTop (nhds x) :=
    (lp.hasSum_single ENNReal.ofNat_ne_top x).comp nodesBelow_tendsto
  apply StrongOperator.continuous_action_of_approximation (fieldFactor m U hm)
    (Real.sqrt U) (Real.sqrt_nonneg U) (fieldFactor_bound m U hm) x P hp
  intro N
  have he : (fun f : EllipticField m U => fieldFactor m U hm f (P N)) =
      fun f => ∑ q ∈ nodesBelow N, (x q) • globalHaarColumn q f.1 := by
    funext f
    simp only [P, fieldFactor, map_sum, factor_single_value]
  rw [he]
  apply continuous_finsetSum
  intro q hq
  have hc : Continuous (fun v : CircleL2 => (x q) • v) := continuous_const_smul (x q)
  exact hc.comp (continuous_fieldColumn m U hm q)

theorem continuous_fieldFactor_joint (m U : ℝ) (hm : 0 < m) :
    Continuous (fun p : EllipticField m U × HaarInput => fieldFactor m U hm p.1 p.2) :=
  StrongOperator.continuous_joint_action (fieldFactor m U hm) (Real.sqrt U) (Real.sqrt_nonneg U)
    (fieldFactor_bound m U hm) (continuous_fieldFactor_action m U hm)

theorem continuous_fieldInverse_action (m U : ℝ) (hm : 0 < m) (v : CircleL2) :
    Continuous (fun f : EllipticField m U => (fieldFactorEquivalence m U hm f).symm v) := by
  apply StrongOperator.continuous_inverse_action (fieldFactorEquivalence m U hm) (Real.sqrt m)⁻¹
  · intro f y
    exact factorEquivalence_inverse_bound f.1 m U hm f.2.1 f.2.2 y
  · exact continuous_fieldFactor_action m U hm

theorem continuous_fieldInverse_joint (m U : ℝ) (hm : 0 < m) :
    Continuous (fun p : EllipticField m U × CircleL2 => (fieldFactorEquivalence m U hm p.1).symm p.2) := by
  apply StrongOperator.continuous_joint_action
    (fun f : EllipticField m U => (fieldFactorEquivalence m U hm f).symm.toContinuousLinearMap)
    (Real.sqrt m)⁻¹ (by positivity)
  · intro f y
    exact factorEquivalence_inverse_bound f.1 m U hm f.2.1 f.2.2 y
  · exact continuous_fieldInverse_action m U hm

theorem measurable_fieldFactor_joint (m U : ℝ) (hm : 0 < m) :
    Measurable (fun p : EllipticField m U × HaarInput => fieldFactor m U hm p.1 p.2) :=
  (continuous_fieldFactor_joint m U hm).measurable

theorem measurable_fieldInverse_joint (m U : ℝ) (hm : 0 < m) :
    Measurable (fun p : EllipticField m U × CircleL2 => (fieldFactorEquivalence m U hm p.1).symm p.2) :=
  (continuous_fieldInverse_joint m U hm).measurable

/-- The input sigma algebra is arbitrary; in particular these actions
preserve predictable measurability when that sigma algebra is supplied. -/
theorem measurable_fieldFactor_process {X : Type*} [MeasurableSpace X]
    (m U : ℝ) (hm : 0 < m) (f : X → EllipticField m U) (hf : Measurable f)
    (x : X → HaarInput) (hx : Measurable x) :
    Measurable (fun p => fieldFactor m U hm (f p) (x p)) := by
  let g : X → EllipticField m U × HaarInput := fun p => (f p, x p)
  have hg : Measurable g := hf.prodMk hx
  change Measurable ((fun p : EllipticField m U × HaarInput => fieldFactor m U hm p.1 p.2) ∘ g)
  exact (measurable_fieldFactor_joint m U hm).comp hg

theorem measurable_fieldInverse_process {X : Type*} [MeasurableSpace X]
    (m U : ℝ) (hm : 0 < m) (f : X → EllipticField m U) (hf : Measurable f)
    (v : X → CircleL2) (hv : Measurable v) :
    Measurable (fun p => (fieldFactorEquivalence m U hm (f p)).symm (v p)) := by
  let g : X → EllipticField m U × CircleL2 := fun p => (f p, v p)
  have hg : Measurable g := hf.prodMk hv
  change Measurable ((fun p : EllipticField m U × CircleL2 => (fieldFactorEquivalence m U hm p.1).symm p.2) ∘ g)
  exact (measurable_fieldInverse_joint m U hm).comp hg

end SHE.FiniteHaar
