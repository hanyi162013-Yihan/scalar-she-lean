module

public import SHEStochastic.CanonicalFourierFluctuation
public import SHEStochastic.NativeFourierCompensatorValue
public import SHEStochastic.NativePathGeneratorFunctional
public import SHE.CanonicalStateDriverPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.CanonicalFourierCompensator
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar
open StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)
  (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction E ℝ)

def value (t : ℝ≥0) (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) : ℝ :=
  PathIntegratedCovariance.value H (PathIntegratedCovariance.exponential H rate hrate) b x.1 (clock H t)

theorem continuous (t : ℝ≥0) : Continuous (value (ι := ι) H rate hrate b t) :=
  ((PathIntegratedCovariance.functional H (PathIntegratedCovariance.exponential H rate hrate) b
    (clock H t)).continuous).comp continuous_fst

def functional (t : ℝ≥0) : BoundedContinuousFunction (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) ℝ :=
  (PathIntegratedCovariance.functional H (PathIntegratedCovariance.exponential H rate hrate) b (clock H t)).compContinuous
    ⟨Prod.fst, continuous_fst⟩

theorem norm_bound (t : ℝ≥0) (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    ‖value H rate hrate b t x‖ ≤ ‖PathIntegratedCovariance.exponential H rate hrate‖*‖b‖*H :=
  PathIntegratedCovariance.norm_bound H _ b x.1 (clock H t)

theorem difference_norm (c : BoundedContinuousFunction E ℝ) (t : ℝ≥0) :
    ‖functional (ι := ι) H rate hrate b t-functional H rate hrate c t‖ ≤
      ‖PathIntegratedCovariance.exponential H rate hrate‖*‖b-c‖*H := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  exact PathIntegratedCovariance.difference_bound H _ b c x.1 (clock H t)

theorem uniform_limit (bn : ℕ → BoundedContinuousFunction E ℝ)
    (hb : Filter.Tendsto (fun k ↦ ‖b-bn k‖) Filter.atTop (𝓝 0)) (t : ℝ≥0) :
    Filter.Tendsto (fun k ↦ ‖functional (ι := ι) H rate hrate b t-
      functional H rate hrate (bn k) t‖) Filter.atTop (𝓝 0) := by
  have hz : Filter.Tendsto
      (fun k ↦ ‖PathIntegratedCovariance.exponential H rate hrate‖*‖b-bn k‖*(H : ℝ))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hb).mul tendsto_const_nhds
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun k ↦ difference_norm H rate hrate b (bn k) t) hz

theorem adapted : StronglyAdapted (CanonicalStateDriverFiltration.filtration H)
    (value (ι := ι) H rate hrate b) := by
  intro t
  let F := CanonicalStateDriverFiltration.filtration (E := E) (ι := ι) H
  have hpath (q : Time H) : Measurable[F (toNN H q)]
      (fun x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H ↦ x.1 q) :=
    (JointCanonicalCylinderRecognition.adapted H q).fst
  have hh := past_test_measurable H F Prod.fst hpath (clock H t)
    (PathIntegratedCovariance.functional H (PathIntegratedCovariance.exponential H rate hrate) b (clock H t))
    (PathIntegratedCovariance.usesPast H _ b (clock H t))
  exact hh.mono (F.mono (show toNN H (clock H t) ≤ t from min_le_left _ _))

theorem source_value {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ≥0 → Ω → E) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (sample : Ω) (t : ℝ≥0) :
    PathIntegratedCovariance.value H (PathIntegratedCovariance.exponential H rate hrate) b
      (NativeContinuousPath.path H W hcW sample) (clock H t) =
      ∫ s in (0 : ℝ)..(min t H : ℝ≥0), Real.exp (s*rate)*b (W s.toNNReal sample) := by
  apply intervalIntegral.integral_congr_Ioo_of_le (clock H t).property.1
  intro s hs
  have hsH : s ∈ Set.Icc (0 : ℝ) (H : ℝ) :=
    ⟨hs.1.le, hs.2.le.trans (clock H t).property.2⟩
  change PathIntegratedCovariance.exponential H rate hrate s *
    b (PastedGeneratorFunctional.read H (NativeContinuousPath.path H W hcW sample) s) =
      Real.exp (s*rate)*b (W s.toNNReal sample)
  rw [PathIntegratedCovariance.exponential_apply H rate hrate s hsH,
    NativePathGeneratorFunctional.read_eq H W hcW sample s hsH]

theorem comp_bundle {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : FiniteScalarIto.Family F μ H ι) (W : ℝ≥0 → Ω → E)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (t : ℝ≥0) (sample : Ω) :
    value H rate hrate b t (CanonicalNativeBrownian.bundle F μ H P W hcW sample) =
      ∫ s in (0 : ℝ)..(min t H : ℝ≥0), Real.exp (s*rate)*b (W s.toNNReal sample) := by
  have he : (CanonicalNativeBrownian.bundle F μ H P W hcW sample).1 =
      NativeContinuousPath.path H W hcW sample := by
    apply ContinuousMap.ext
    intro q
    change W (0+q.val.toNNReal) sample = W q.val.toNNReal sample
    rw [zero_add]
  unfold value
  rw [he]
  exact source_value H rate hrate b W hcW sample t

/-- The same time functional evaluated on the canonical state itself.
This connects the weak-limit compensators to its native input energy. -/
theorem canonical_value (t : ℝ≥0) (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    value H rate hrate b t x = ∫ s in (0 : ℝ)..(min t H : ℝ≥0),
      Real.exp (s*rate)*b (CanonicalStateDriverFiltration.state H s.toNNReal x) := by
  let U := CanonicalStateDriverFiltration.state (E := E) (ι := ι) H
  have hpath : NativeContinuousPath.path H U (CanonicalStateDriverFiltration.state_continuous H) x = x.1 := by
    apply ContinuousMap.ext
    intro q
    change x.1 (CanonicalStateDriverFiltration.clock H q.val.toNNReal) = x.1 q
    congr 1
    apply Subtype.ext
    change min (q.val.toNNReal : ℝ) (H : ℝ) = q.val
    rw [Real.coe_toNNReal q.val q.property.1, min_eq_left q.property.2]
  unfold value
  rw [← hpath]
  exact source_value H rate hrate b U (CanonicalStateDriverFiltration.state_continuous H) x t

end SHEStochastic.CanonicalFourierCompensator
