module

public import SHEStochastic.NativeUniformStoppedFourier
public import SHEStochastic.NativeContinuationFourierInput
public import SHEStochastic.PastedLinearHeatIntegrability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativeUniformFourierPrefix
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting
open UnboundedJointCanonicalPathMartingale PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)


theorem path_value (a : ℂ →L[ℝ] ℝ) (n : ℤ) (ω : Ω) (t : Time (min H 1)) :
    value (min H 1) (row (ι := ι) a n) ((n : ℝ)^2) (path F μ H W P hcW ω) t =
      NativeUniformStoppedFourier.coordinate W a n t.val.toNNReal ω := by
  change Real.exp ((n : ℝ)^2*t.val)*NativeFourierHeatCoordinate.coordinate a n (W t.val.toNNReal ω)-
      NativeFourierHeatCoordinate.coordinate a n (W (0 : ℝ).toNNReal ω) = _
  simp only [NativeUniformStoppedFourier.coordinate, Real.coe_toNNReal _ t.property.1,
    Real.toNNReal_zero, mul_comm]

theorem stopped_value (R : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (ω : Ω) (t : Time (min H 1)) :
    stoppedProcess (NativeUniformStoppedFourier.coordinate W a n)
      (fun ω ↦ (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R ω) : WithTop ℝ≥0))
      (AdaptedCanonicalPathTests.toNN (min H 1) t) ω =
    value (min H 1) (row (ι := ι) a n) ((n : ℝ)^2) (path F μ H W P hcW ω)
      (pastTime (min H 1) (uniformExit H W hcW R ω) t) := by
  rw [path_value]
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_min, AdaptedCanonicalPathTests.toNN, pastTime]
  rw [Real.coe_toNNReal _ (le_min t.property.1 (uniformExit H W hcW R ω).property.1)]
  exact NNReal.coe_min _ _

include hH hnull hEquation hM hu₀ in
/-- The integrating-factor mode has a deterministic bound on the actual
uniformly stopped source prefix, including the exit time. -/
theorem bound (R : ℕ) (hR : M ≤ R) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∀ᵐ ω ∂μ, ∀ t : Time (min H 1), t ≤ uniformExit H W hcW R ω →
      ‖value (min H 1) (row (ι := ι) a n) ((n : ℝ)^2) (path F μ H W P hcW ω) t‖ ≤
        Real.exp ((n : ℝ)^2*(min H 1 : ℝ≥0))*‖NativeFourierHeatCoordinate.coordinate a n‖*R+
          ‖NativeFourierHeatCoordinate.coordinate a n‖*R := by
  filter_upwards [NativeUniformStoppedFourier.state_bound F μ H W hW hG hβ hβ1 P e u₀
    hH hcW hnull hEquation M hM hu₀ R hR] with ω hω t ht
  have h0 := hω (origin (min H 1)) (uniformExit H W hcW R ω).property.1
  have hExp : Real.exp ((n : ℝ)^2*t.val) ≤ Real.exp ((n : ℝ)^2*(min H 1 : ℝ≥0)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 (sq_nonneg _))
  change ‖Real.exp ((n : ℝ)^2*t.val)*NativeFourierHeatCoordinate.coordinate a n
      (NativeContinuousPath.path (min H 1) W hcW ω t)-
        NativeFourierHeatCoordinate.coordinate a n
          (NativeContinuousPath.path (min H 1) W hcW ω (origin (min H 1)))‖ ≤ _
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply add_le_add
  · simpa only [mul_assoc] using mul_le_mul hExp
      ((NativeFourierHeatCoordinate.coordinate a n).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (hω t ht) (norm_nonneg _))) (norm_nonneg _) (Real.exp_pos _).le
  · exact (NativeFourierHeatCoordinate.coordinate a n).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))

include hH hnull hEquation hM hu₀ in
theorem stopped_identity (R : ℕ) (hR : M ≤ R) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (s t : Time (min H 1)) (hst : s.val ≤ t.val)
    (test : BoundedContinuousFunction (Path (min H 1) (JointStateDriverPath.State RealL2 ι)) ℝ)
    (htest : PastedPastTests.UsesPast (min H 1) s test) :
    (∫ ω, test (path F μ H W P hcW ω)*
      (value (min H 1) (row (ι := ι) a n) ((n : ℝ)^2) (path F μ H W P hcW ω)
        (pastTime (min H 1) (uniformExit H W hcW R ω) t)-
      value (min H 1) (row (ι := ι) a n) ((n : ℝ)^2) (path F μ H W P hcW ω)
        (pastTime (min H 1) (uniformExit H W hcW R ω) s)) ∂μ) = 0 := by
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _
    (NativeUniformStoppedFourier.martingale F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation M hM hu₀ R hR a n)
    (AdaptedCanonicalPathTests.toNN (min H 1) s) (AdaptedCanonicalPathTests.toNN (min H 1) t) hst
    (fun ω ↦ test (path F μ H W P hcW ω))
    (AdaptedCanonicalPathTests.past_test_measurable (min H 1) F _
      (adapted_path F μ H W hW P hcW) s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  simpa only [stopped_value F μ H W P hcW] using hh

end SHEStochastic.NativeUniformFourierPrefix
