module

public import SHEStochastic.PastedLinearHeatFunctional
public import SHEStochastic.StoppedContinuationMeasure
public import SHEStochastic.AdaptedCanonicalPathTests
public import SHEStochastic.KernelMartingalePasting
public import SHEStochastic.BCFPastTesting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.PastedLinearHeatMartingale
open MeasureTheory ProbabilityTheory StoppedPathPasting PastedPastTests AdaptedCanonicalPathTests
open PastedLinearHeatFunctional
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (lam : ℝ)

def Identity (ν : Measure (Path H E)) : Prop :=
  ∀ s t : Time H, s.val ≤ t.val →
    ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
      (∫ x, test x*(value H ell lam x t-value H ell lam x s) ∂ν) = 0

theorem source_identity {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Path H E) (hX : Measurable X)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hM : Martingale (fun q ω ↦ value H ell lam (X ω) (clock H q)) F μ) :
    Identity H ell lam (μ.map X) := by
  intro s t hst test htest
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hM (toNN H s) (toNN H t) hst
    (fun ω ↦ test (X ω)) (past_test_measurable H F X hadapt s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  simp only [clock_toNN] at hh
  have hv (q : Time H) : Continuous (fun x : Path H E ↦ value H ell lam x q) :=
    (continuous_value H ell lam).comp (continuous_id.prodMk continuous_const)
  calc
    _ = ∫ ω, test (X ω)*(value H ell lam (X ω) t-value H ell lam (X ω) s) ∂μ :=
      integral_map_of_stronglyMeasurable hX (test.continuous.mul ((hv t).sub (hv s))).stronglyMeasurable
    _ = 0 := hh

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → Path H E) (exit : Ω → Time H) (hX : Measurable X) (hr : Measurable exit)
  (κ : Kernel E (Path H E)) [IsMarkovKernel κ]

/-- Actual random-time kernel pasting of a linear heat mode. Its
integrability premises are explicit; continuation moment bounds discharge
them when this reusable Fubini theorem is applied to the SPDE. -/
theorem joint_identity
    (hinitial : ∀ᵐ ω ∂μ, ∀ᵐ y ∂κ (StoppedContinuationMeasure.state H X exit ω),
      y (origin H) = StoppedContinuationMeasure.state H X exit ω)
    (hfuture : ∀ᵐ ω ∂μ, Identity H ell lam (κ (StoppedContinuationMeasure.state H X exit ω)))
    (s t : Time H) (hst : s.val ≤ t.val)
    (test : BoundedContinuousFunction (Path H E) ℝ) (htest : UsesPast H s test)
    (hipre : Integrable (fun z : Ω × Path H E ↦ test (StoppedContinuationMeasure.value H X exit z)*
      (value H ell lam (X z.1) (pastTime H (exit z.1) t)-
        value H ell lam (X z.1) (pastTime H (exit z.1) s)))
      (StoppedContinuationMeasure.joint H X exit hX hr μ κ))
    (hipost : Integrable (fun z : Ω × Path H E ↦ test (StoppedContinuationMeasure.value H X exit z)*
      (Real.exp (lam*(exit z.1).val)*(value H ell lam z.2 (futureTime H (exit z.1) t)-
        value H ell lam z.2 (futureTime H (exit z.1) s))))
      (StoppedContinuationMeasure.joint H X exit hX hr μ κ))
    (horiginal : (∫ ω, test (X ω)*(value H ell lam (X ω) (pastTime H (exit ω) t)-
      value H ell lam (X ω) (pastTime H (exit ω) s)) ∂μ) = 0) :
    (∫ z, test (StoppedContinuationMeasure.value H X exit z)*
      (value H ell lam (StoppedContinuationMeasure.value H X exit z) t-
        value H ell lam (StoppedContinuationMeasure.value H X exit z) s)
      ∂StoppedContinuationMeasure.joint H X exit hX hr μ κ) = 0 := by
  let K := StoppedContinuationMeasure.continuation H X exit hX hr κ
  let T := fun z : Ω × Path H E ↦ test (StoppedContinuationMeasure.value H X exit z)
  let pre := fun ω ↦ value H ell lam (X ω) (pastTime H (exit ω) t)-
    value H ell lam (X ω) (pastTime H (exit ω) s)
  let delta := fun z : Ω × Path H E ↦ value H ell lam z.2 (futureTime H (exit z.1) t)-
    value H ell lam z.2 (futureTime H (exit z.1) s)
  let post := fun z : Ω × Path H E ↦ Real.exp (lam*(exit z.1).val)*delta z
  apply KernelMartingalePasting.cylinder_identity_of_split μ K _ T post pre (fun ω ↦ test (X ω))
  · exact (StoppedContinuationMeasure.matching_initial_of_ae H X exit hX hr μ κ hinitial).mono
      fun z hz ↦ increment_paste H ell lam (exit z.1) s t (X z.1) z.2 hz
  · intro z hz
    exact test_of_pre_nonzero H ell lam s t (exit z.1) hst test htest (X z.1) z.2 hz
  · exact hipre
  · exact hipost
  · exact horiginal
  · filter_upwards [hfuture] with ω hω
    let ψ := test.compContinuous ⟨fun y ↦ paste H (exit ω) (X ω) y,
      (continuous_paste H).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))⟩
    have hh := hω (futureTime H (exit ω) s) (futureTime H (exit ω) t)
      (max_le_max_right _ (sub_le_sub_right hst _)) ψ (shifted_test H s (exit ω) test htest (X ω))
    have he (y : Path H E) : T (ω,y)*post (ω,y) = Real.exp (lam*(exit ω).val)*(ψ y*delta (ω,y)) := by
      change T (ω,y)*(Real.exp (lam*(exit ω).val)*delta (ω,y)) =
        Real.exp (lam*(exit ω).val)*(T (ω,y)*delta (ω,y))
      ring
    simp_rw [he]
    change (∫ y, ψ y*delta (ω,y) ∂K ω) = 0 at hh
    rw [integral_const_mul, hh, mul_zero]

section Recognition
variable [TopologicalSpace.MetrizableSpace (Path H E)]

/-- Full-past test identities and the derived path moment give the
ordinary Fourier martingale in the full canonical filtration. -/
theorem martingale (ν : Measure (Path H E)) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Path H E)))
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun x : Path H E ↦ x t))
    (hF : ∀ q, F q ≤ MeasurableSpace.comap (stopped H (clock H q)) inferInstance)
    (hId : Identity H ell lam ν) (hMom : MemLp (envelope H ell lam) 2 ν) :
    Martingale (fun q x ↦ value H ell lam x (clock H q)) F ν := by
  letI : MetricSpace (Path H E) := TopologicalSpace.metrizableSpaceMetric _
  let M := fun q x ↦ value H ell lam x (clock H q)
  have ha : StronglyAdapted F M := by
    intro q
    have hq := (hadapt (clock H q)).mono (F.mono (show toNN H (clock H q) ≤ q from min_le_left _ _)) le_rfl
    have h0 := (hadapt (origin H)).mono (F.mono (show toNN H (origin H) ≤ q from zero_le)) le_rfl
    exact (stronglyMeasurable_const.mul (ell.continuous.measurable.comp hq).stronglyMeasurable).sub
      (ell.continuous.measurable.comp h0).stronglyMeasurable
  apply BCFPastTesting.martingale ν (F := F) (past := fun q ↦ stopped H (clock H q))
    (fun q ↦ (continuous_stopped H).measurable.comp (measurable_const.prodMk measurable_id)) hF M ha
  · intro q
    exact hMom.mono' ((ha q).mono (F.le q)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ value_bound H ell lam x _)
  · intro s t hst f
    let ψ := f.compContinuous ⟨stopped H (clock H s),
      (continuous_stopped H).comp (continuous_const.prodMk continuous_id)⟩
    apply hId (clock H s) (clock H t) (min_le_min_right _ (by exact_mod_cast hst)) ψ
    intro x y hxy
    apply congrArg f
    apply ContinuousMap.ext
    intro q
    exact hxy (pastTime H (clock H s) q) (min_le_right _ _)

end Recognition
end SHEStochastic.PastedLinearHeatMartingale
