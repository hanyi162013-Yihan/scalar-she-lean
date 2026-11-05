module

public import SHEStochastic.PastedCharacteristicFunctional
public import SHEStochastic.StoppedContinuationMeasure
public import SHEStochastic.KernelMartingalePasting
public import SHEStochastic.ComplexPastTesting
public import SHEStochastic.AdaptedCanonicalPathTests
public import Mathlib.Topology.Metrizable.Uniformity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PastedCharacteristicMartingale
open MeasureTheory ProbabilityTheory StoppedPathPasting PastedPastTests
open PastedCharacteristicFunctional
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (c : ℝ)

/-- Characteristic martingales tested against the full state-driver past. -/
def Identity (ν : Measure (Path H E)) : Prop :=
  ∀ s t : Time H, s.val ≤ t.val →
    ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
      (∫ x, test x • (value H ell c x t - value H ell c x s) ∂ν) = 0

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → Path H E) (r : Ω → Time H) (hX : Measurable X) (hr : Measurable r)
  (κ : Kernel E (Path H E)) [IsMarkovKernel κ]

/-- A bounded characteristic martingale survives actual random-time
kernel pasting. The driver increments do not require initial matching. -/
theorem joint_identity (hc : 0 ≤ c)
    (hfuture : ∀ᵐ ω ∂μ, Identity H ell c (κ (StoppedContinuationMeasure.state H X r ω)))
    (s t : Time H) (hst : s.val ≤ t.val)
    (test : BoundedContinuousFunction (Path H E) ℝ) (htest : UsesPast H s test)
    (horiginal : (∫ ω, test (X ω) •
      (value H ell c (X ω) (pastTime H (r ω) t) -
        value H ell c (X ω) (pastTime H (r ω) s)) ∂μ) = 0) :
    (∫ z, test (StoppedContinuationMeasure.value H X r z) •
      (value H ell c (StoppedContinuationMeasure.value H X r z) t -
        value H ell c (StoppedContinuationMeasure.value H X r z) s)
      ∂StoppedContinuationMeasure.joint H X r hX hr μ κ) = 0 := by
  let ν := StoppedContinuationMeasure.joint H X r hX hr μ κ
  let K := StoppedContinuationMeasure.continuation H X r hX hr κ
  let T : Ω × Path H E → ℝ := fun z ↦ test (StoppedContinuationMeasure.value H X r z)
  let pre : Ω → ℂ := fun ω ↦ value H ell c (X ω) (pastTime H (r ω) t) -
    value H ell c (X ω) (pastTime H (r ω) s)
  let delta : Ω × Path H E → ℂ := fun z ↦ value H ell c z.2 (futureTime H (r z.1) t) -
    value H ell c z.2 (futureTime H (r z.1) s)
  let factor : Ω × Path H E → ℂ := fun z ↦ value H ell c (X z.1) (r z.1)
  let post := fun z ↦ factor z * delta z
  let B := Real.exp (c * H)
  have hT : Measurable T := test.continuous.measurable.comp
    (StoppedContinuationMeasure.measurable_value H X r hX hr)
  have hB : ∀ z : Ω × Path H E, ‖T z‖ ≤ ‖test‖ := fun z ↦ test.norm_coe_le_norm _
  have hv := (continuous_value H ell c).measurable
  have hf : Measurable factor := hv.comp ((hX.comp measurable_fst).prodMk (hr.comp measurable_fst))
  have hd : Measurable delta := by
    apply (hv.comp (measurable_snd.prodMk ?_)).sub (hv.comp (measurable_snd.prodMk ?_))
    all_goals exact (continuous_futureTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)
  have hipre : Integrable (fun z : Ω × Path H E ↦ T z • pre z.1) ν := by
    apply weighted_increment_integrable H ell c ν hc T ‖test‖ hT hB
      (fun z ↦ X z.1) (hX.comp measurable_fst)
      (fun z ↦ pastTime H (r z.1) s) (fun z ↦ pastTime H (r z.1) t)
    all_goals exact (continuous_pastTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)
  have hipost : Integrable (fun z ↦ T z • post z) ν := by
    apply (integrable_const (‖test‖ * (B * (B+B)))).mono'
      (hT.smul (hf.mul hd)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z ↦ by
      change ‖T z • (factor z * delta z)‖ ≤ ‖test‖ * (B * (B+B))
      rw [norm_smul, norm_mul]
      exact mul_le_mul (hB z)
        (mul_le_mul (norm_value_le H ell c hc (X z.1) (r z.1))
          ((norm_sub_le _ _).trans (add_le_add
            (norm_value_le H ell c hc z.2 (futureTime H (r z.1) t))
            (norm_value_le H ell c hc z.2 (futureTime H (r z.1) s))))
          (norm_nonneg _) (Real.exp_pos _).le)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg test)
  apply KernelMartingalePasting.cylinder_identity_smul_of_split μ K
    (fun z ↦ value H ell c (StoppedContinuationMeasure.value H X r z) t -
      value H ell c (StoppedContinuationMeasure.value H X r z) s)
    T post pre (fun ω ↦ test (X ω))
  · exact Filter.Eventually.of_forall fun z ↦ increment_paste H ell c (r z.1) s t (X z.1) z.2
  · intro z hz
    exact test_of_pre_nonzero H ell c s t (r z.1) hst test htest (X z.1) z.2 hz
  · exact hipre
  · exact hipost
  · exact horiginal
  · filter_upwards [hfuture] with ω hω
    let ψ := test.compContinuous
      ⟨fun y ↦ paste H (r ω) (X ω) y,
        (continuous_paste H).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))⟩
    have hh := hω (futureTime H (r ω) s) (futureTime H (r ω) t)
      (max_le_max_right _ (sub_le_sub_right hst _)) ψ
      (shifted_test H s (r ω) test htest (X ω))
    have he (y : Path H E) : T (ω,y) • post (ω,y) =
        value H ell c (X ω) (r ω) * (ψ y • delta (ω,y)) := by
      change (T (ω,y) : ℂ) * (factor (ω,y) * delta (ω,y)) =
        factor (ω,y) * ((T (ω,y) : ℂ) * delta (ω,y))
      ring
    simp_rw [he]
    change (∫ y, ψ y • delta (ω,y) ∂K ω) = 0 at hh
    rw [integral_const_mul, hh, mul_zero]

/-- The pasted path law inherits the characteristic identity under
the full canonical past, rather than only the driver's own past. -/
theorem law_identity (hc : 0 ≤ c)
    (hfuture : ∀ᵐ ω ∂μ, Identity H ell c (κ (StoppedContinuationMeasure.state H X r ω)))
    (horiginal : ∀ s t : Time H, s.val ≤ t.val →
      ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
        (∫ ω, test (X ω) • (value H ell c (X ω) (pastTime H (r ω) t) -
          value H ell c (X ω) (pastTime H (r ω) s)) ∂μ) = 0) :
    Identity H ell c (StoppedContinuationMeasure.law H X r hX hr μ κ) := by
  intro s t hst test htest
  have hv (q : Time H) : Continuous (fun x : Path H E ↦ value H ell c x q) :=
    (continuous_value H ell c).comp (continuous_id.prodMk continuous_const)
  change (∫ x, test x • (value H ell c x t - value H ell c x s)
    ∂(StoppedContinuationMeasure.joint H X r hX hr μ κ).map
      (StoppedContinuationMeasure.value H X r)) = 0
  calc
    _ = ∫ z, test (StoppedContinuationMeasure.value H X r z) •
        (value H ell c (StoppedContinuationMeasure.value H X r z) t -
          value H ell c (StoppedContinuationMeasure.value H X r z) s)
        ∂StoppedContinuationMeasure.joint H X r hX hr μ κ :=
      integral_map_of_stronglyMeasurable
        (StoppedContinuationMeasure.measurable_value H X r hX hr)
        (test.continuous.smul ((hv t).sub (hv s))).stronglyMeasurable
    _ = 0 := joint_identity H ell c μ X r hX hr κ hc hfuture s t hst test htest
      (horiginal s t hst test htest)

section Recognition
variable [TopologicalSpace.MetrizableSpace (Path H E)]

/-- Bounded continuous tests determine the characteristic martingale
in every adapted filtration generated by the full stopped trajectory. -/
theorem martingale (ν : Measure (Path H E)) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Path H E))) (hc : 0 ≤ c)
    (hadapt : ∀ t : Time H, Measurable[F (AdaptedCanonicalPathTests.toNN H t)]
      (fun x : Path H E ↦ x t))
    (hF : ∀ q, F q ≤ MeasurableSpace.comap
      (stopped H (AdaptedCanonicalPathTests.clock H q)) inferInstance)
    (hId : Identity H ell c ν) :
    Martingale (fun q x ↦ value H ell c x (AdaptedCanonicalPathTests.clock H q)) F ν := by
  letI : MetricSpace (Path H E) := TopologicalSpace.metrizableSpaceMetric _
  let M := fun q x ↦ value H ell c x (AdaptedCanonicalPathTests.clock H q)
  have ha : StronglyAdapted F M := by
    intro q
    have hq := (hadapt (AdaptedCanonicalPathTests.clock H q)).mono
      (F.mono (show AdaptedCanonicalPathTests.toNN H (AdaptedCanonicalPathTests.clock H q) ≤ q from
        min_le_left _ _)) le_rfl
    have hzero := (hadapt (origin H)).mono
      (F.mono (show AdaptedCanonicalPathTests.toNN H (origin H) ≤ q from zero_le)) le_rfl
    have hz := ell.continuous.measurable.comp (hq.sub hzero)
    exact ((Complex.continuous_exp.measurable.comp
      (((Complex.continuous_ofReal.measurable.comp hz).mul measurable_const).add
        measurable_const))).stronglyMeasurable
  apply ComplexPastTesting.martingale ν
    (F := F) (past := fun q ↦ stopped H (AdaptedCanonicalPathTests.clock H q))
    (fun q ↦ (continuous_stopped H).measurable.comp (measurable_const.prodMk measurable_id))
    hF M ha
  · intro q
    exact MemLp.of_bound ((ha q).mono (F.le q)).aestronglyMeasurable
      (Real.exp (c*H)) (Filter.Eventually.of_forall fun x ↦ norm_value_le H ell c hc x _)
  · intro s t hst f
    let ψ := f.compContinuous ⟨stopped H (AdaptedCanonicalPathTests.clock H s),
      (continuous_stopped H).comp (continuous_const.prodMk continuous_id)⟩
    apply hId (AdaptedCanonicalPathTests.clock H s) (AdaptedCanonicalPathTests.clock H t)
      (min_le_min_right _ (by exact_mod_cast hst)) ψ
    intro x y hxy
    apply congrArg f
    apply ContinuousMap.ext
    intro q
    exact hxy (pastTime H (AdaptedCanonicalPathTests.clock H s) q) (min_le_right _ _)

end Recognition
end SHEStochastic.PastedCharacteristicMartingale
