module

public import SHEStochastic.PastedPastTests
public import SHEStochastic.StoppedContinuationMeasure
public import SHEStochastic.KernelMartingalePasting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.PastedCylinderMartingale
open MeasureTheory ProbabilityTheory StoppedPathPasting PastedPastTests
open PastedGeneratorFunctional
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (H : ℝ≥0)

/-- Canonical martingale test identities for one bounded cylinder test
and its bounded generator value. The test of the past is arbitrary
bounded continuous; no Markov property of the original solution enters. -/
def Identity (f b : BoundedContinuousFunction E ℝ) (μ : Measure (Path H E)) : Prop :=
  ∀ s t : Time H, s.val ≤ t.val →
    ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
      (∫ x, test x * (value H f b x t - value H f b x s) ∂μ) = 0

/-- Continuous changes of the state commute with the path-law cylinder
identity. The future driver translation is an instance of this rule. -/
theorem Identity.map_state (φ : C(E, E)) (f b : BoundedContinuousFunction E ℝ)
    (ν : Measure (Path H E))
    (h : Identity H (f.compContinuous φ) (b.compContinuous φ) ν) :
    Identity H f b (ν.map (fun x ↦ φ.comp x)) := by
  let T : C(Path H E, Path H E) := ⟨fun x ↦ φ.comp x, ContinuousMap.continuous_postcomp φ⟩
  have hm : Measurable T := ContinuousMap.measurable_iff_eval.mpr fun t ↦
    φ.continuous.measurable.comp (ContinuousMap.measurable_eval t)
  intro s t hst test htest
  have hc : Continuous (fun x : Path H E ↦ test x * (value H f b x t-value H f b x s)) :=
    test.continuous.mul
      (((continuous_value H f b f.continuous b.continuous).comp (continuous_id.prodMk continuous_const)).sub
        ((continuous_value H f b f.continuous b.continuous).comp (continuous_id.prodMk continuous_const)))
  change (∫ x, test x*(value H f b x t-value H f b x s) ∂ν.map T) = 0
  rw [integral_map hm.aemeasurable hc.stronglyMeasurable.aestronglyMeasurable]
  apply h s t hst (test.compContinuous T)
  intro x y hxy
  exact htest (T x) (T y) fun q hq ↦ congrArg φ (hxy q hq)

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → Path H E) (r : Ω → Time H) (hX : Measurable X) (hr : Measurable r)
  (κ : Kernel E (Path H E)) [IsMarkovKernel κ]
  (f b : BoundedContinuousFunction E ℝ)

/-- Actual random-time pasting of the canonical martingale identity.
The premises are the original stopped identity and the continuation
kernel's ordinary identity. This proves their combination by Fubini;
instantiating those premises for the SPDE remains separate. -/
theorem joint_identity_of_ae
    (hinitial : ∀ᵐ sample ∂μ, ∀ᵐ y ∂κ (StoppedContinuationMeasure.state H X r sample),
      y (origin H) = StoppedContinuationMeasure.state H X r sample)
    (hfuture : ∀ᵐ sample ∂μ, Identity H f b (κ (StoppedContinuationMeasure.state H X r sample)))
    (s t : Time H) (hst : s.val ≤ t.val)
    (test : BoundedContinuousFunction (Path H E) ℝ) (htest : UsesPast H s test)
    (horiginal : (∫ ω, test (X ω) *
      (value H f b (X ω) (pastTime H (r ω) t) -
        value H f b (X ω) (pastTime H (r ω) s)) ∂μ) = 0) :
    (∫ z, test (StoppedContinuationMeasure.value H X r z) *
      (value H f b (StoppedContinuationMeasure.value H X r z) t -
        value H f b (StoppedContinuationMeasure.value H X r z) s)
      ∂StoppedContinuationMeasure.joint H X r hX hr μ κ) = 0 := by
  let ν := StoppedContinuationMeasure.joint H X r hX hr μ κ
  let K := StoppedContinuationMeasure.continuation H X r hX hr κ
  let T : Ω × Path H E → ℝ := fun z ↦ test (StoppedContinuationMeasure.value H X r z)
  let pre : Ω → ℝ := fun ω ↦ value H f b (X ω) (pastTime H (r ω) t) -
    value H f b (X ω) (pastTime H (r ω) s)
  let post : Ω × Path H E → ℝ := fun z ↦ value H f b z.2 (futureTime H (r z.1) t) -
    value H f b z.2 (futureTime H (r z.1) s)
  have hT : Measurable T := test.continuous.measurable.comp
    (StoppedContinuationMeasure.measurable_value H X r hX hr)
  have hB : ∀ z : Ω × Path H E, ‖T z‖ ≤ ‖test‖ := fun z ↦ test.norm_coe_le_norm _
  have hpre : Integrable (fun z : Ω × Path H E ↦ T z * pre z.1) ν := by
    apply weighted_increment_integrable H ν f b T ‖test‖ hT hB
      (fun z ↦ X z.1) (hX.comp measurable_fst)
      (fun z ↦ pastTime H (r z.1) s) (fun z ↦ pastTime H (r z.1) t)
    all_goals exact (continuous_pastTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)
  have hpost : Integrable (fun z ↦ T z * post z) ν := by
    apply weighted_increment_integrable H ν f b T ‖test‖ hT hB Prod.snd measurable_snd
      (fun z ↦ futureTime H (r z.1) s) (fun z ↦ futureTime H (r z.1) t)
    all_goals exact (continuous_futureTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)
  apply KernelMartingalePasting.cylinder_identity_of_split μ K
    (fun z ↦ value H f b (StoppedContinuationMeasure.value H X r z) t -
      value H f b (StoppedContinuationMeasure.value H X r z) s)
    T post pre (fun ω ↦ test (X ω))
  · exact (StoppedContinuationMeasure.matching_initial_of_ae H X r hX hr μ κ hinitial).mono
      fun z hz ↦ increment_paste H f b b.continuous (r z.1) s t (X z.1) z.2 hz
  · intro z hz
    exact test_of_pre_nonzero H f b s t (r z.1) hst test htest (X z.1) z.2 hz
  · exact hpre
  · exact hpost
  · exact horiginal
  · filter_upwards [hfuture] with ω hω
    let ψ := test.compContinuous
      ⟨fun y ↦ paste H (r ω) (X ω) y,
        (continuous_paste H).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))⟩
    exact hω
      (futureTime H (r ω) s) (futureTime H (r ω) t)
      (max_le_max_right _ (sub_le_sub_right hst _)) ψ
      (shifted_test H s (r ω) test htest (X ω))

/-- The constructed path law satisfies the canonical identities once
the given solution's stopped identities and the kernel identities are
available. Measurability and integrability are proved above. -/
theorem law_identity_of_ae
    (hinitial : ∀ᵐ sample ∂μ, ∀ᵐ y ∂κ (StoppedContinuationMeasure.state H X r sample),
      y (origin H) = StoppedContinuationMeasure.state H X r sample)
    (hfuture : ∀ᵐ sample ∂μ, Identity H f b (κ (StoppedContinuationMeasure.state H X r sample)))
    (horiginal : ∀ s t : Time H, s.val ≤ t.val →
      ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
        (∫ ω, test (X ω) * (value H f b (X ω) (pastTime H (r ω) t) -
          value H f b (X ω) (pastTime H (r ω) s)) ∂μ) = 0) :
    Identity H f b (StoppedContinuationMeasure.law H X r hX hr μ κ) := by
  intro s t hst test htest
  have hv (q : Time H) : Continuous (fun x : Path H E ↦ value H f b x q) :=
    (continuous_value H f b f.continuous b.continuous).comp
      (continuous_id.prodMk continuous_const)
  change (∫ x, test x * (value H f b x t - value H f b x s)
    ∂(StoppedContinuationMeasure.joint H X r hX hr μ κ).map
      (StoppedContinuationMeasure.value H X r)) = 0
  calc
    _ = ∫ z, test (StoppedContinuationMeasure.value H X r z) *
        (value H f b (StoppedContinuationMeasure.value H X r z) t -
          value H f b (StoppedContinuationMeasure.value H X r z) s)
        ∂StoppedContinuationMeasure.joint H X r hX hr μ κ :=
      integral_map_of_stronglyMeasurable
        (StoppedContinuationMeasure.measurable_value H X r hX hr)
        (test.continuous.mul ((hv t).sub (hv s))).stronglyMeasurable
    _ = 0 := joint_identity_of_ae H μ X r hX hr κ f b hinitial hfuture s t hst test htest
      (horiginal s t hst test htest)

/-- The all-initial-states version is a special case of the theorem
requiring the kernel only at actually reached exit states. -/
theorem law_identity
    (hinitial : ∀ z : E, ∀ᵐ y ∂κ z, y (origin H) = z)
    (hfuture : ∀ z : E, Identity H f b (κ z))
    (horiginal : ∀ s t : Time H, s.val ≤ t.val →
      ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
        (∫ sample, test (X sample) *
          (value H f b (X sample) (pastTime H (r sample) t) -
            value H f b (X sample) (pastTime H (r sample) s)) ∂μ) = 0) :
    Identity H f b (StoppedContinuationMeasure.law H X r hX hr μ κ) :=
  law_identity_of_ae H μ X r hX hr κ f b
    (Filter.Eventually.of_forall fun sample ↦ hinitial (StoppedContinuationMeasure.state H X r sample))
    (Filter.Eventually.of_forall fun sample ↦ hfuture (StoppedContinuationMeasure.state H X r sample))
    horiginal

end SHEStochastic.PastedCylinderMartingale
