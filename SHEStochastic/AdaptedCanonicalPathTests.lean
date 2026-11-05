module

public import SHEStochastic.PastedCylinderMartingale
public import SHEStochastic.ContinuousStoppedMartingaleTests
public import SHEStochastic.BoundedLocalMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.AdaptedCanonicalPathTests
open MeasureTheory ProbabilityTheory StoppedPathPasting PastedPastTests
open PastedGeneratorFunctional
open scoped NNReal

def toNN (H : ℝ≥0) (t : Time H) : ℝ≥0 := ⟨t.val, t.property.1⟩

def clock (H : ℝ≥0) (q : ℝ≥0) : Time H :=
  ⟨min (q : ℝ) (H : ℝ), le_min q.property H.property, min_le_right _ _⟩

theorem continuous_clock (H : ℝ≥0) : Continuous (clock H) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _

@[simp] theorem clock_toNN (H : ℝ≥0) (t : Time H) : clock H (toNN H t) = t :=
  Subtype.ext (min_eq_left t.property.2)

@[simp] theorem toNN_clock (H : ℝ≥0) (q : ℝ≥0) : toNN H (clock H q) = min q H :=
  NNReal.eq (NNReal.coe_min q H).symm

theorem clock_min (H : ℝ≥0) (r t : Time H) :
    clock H (min (toNN H t) (toNN H r)) = pastTime H r t := by
  apply Subtype.ext
  change min (min t.val r.val) (H : ℝ) = min t.val r.val
  exact min_eq_left ((min_le_left _ _).trans t.property.2)

theorem clock_min_native (H : ℝ≥0) (r : Time H) (q : ℝ≥0) :
    clock H (min q (toNN H r)) = pastTime H r (clock H q) := by
  apply Subtype.ext
  change min (min (q : ℝ) r.val) (H : ℝ) = min (min (q : ℝ) (H : ℝ)) r.val
  rw [min_assoc, min_assoc, min_eq_left r.property.2, min_eq_right r.property.2]

/-- Reading a finite stopped native clock is the same operation as
reading the corresponding stopped compact-interval trajectory. -/
theorem stopped_clock (H : ℝ≥0) (r : Time H) (q : ℝ≥0) :
    (min (q : WithTop ℝ≥0) (toNN H r : WithTop ℝ≥0)).untopA =
      toNN H (pastTime H r (clock H q)) := by
  simp only [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [← clock_min_native, toNN_clock]
  exact (min_eq_left ((min_le_right q (toNN H r)).trans r.property.2)).symm

variable {Ω E : Type*} [MeasurableSpace Ω]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : Ω → Path H E)

/-- Adapted coordinate evaluations give an adapted stopped path. This
is measurability on the original filtration, without completion or a
new random-path version. -/
theorem measurable_stopped (hadapt : ∀ t : Time H,
    Measurable[F (toNN H t)] (fun ω ↦ X ω t)) (s : Time H) :
    Measurable[F (toNN H s)] (fun ω ↦ stopped H s (X ω)) := by
  letI : MeasurableSpace Ω := F (toNN H s)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (hadapt (pastTime H s t)).mono
    (F.mono (show toNN H (pastTime H s t) ≤ toNN H s from min_le_right _ _)) le_rfl

/-- Every continuous test depending on the past through s is measurable
at s, by evaluation on the already measurable stopped trajectory. -/
theorem continuous_past_test_measurable (hadapt : ∀ t : Time H,
    Measurable[F (toNN H t)] (fun ω ↦ X ω t)) (s : Time H)
    (test : C(Path H E,ℝ)) (htest : UsesPast H s test) :
    StronglyMeasurable[F (toNN H s)] (fun ω ↦ test (X ω)) := by
  have he : (fun ω ↦ test (X ω)) = fun ω ↦ test (stopped H s (X ω)) := by
    funext ω
    apply htest
    intro t ht
    change X ω t = X ω (pastTime H s t)
    rw [show pastTime H s t = t from Subtype.ext (min_eq_left ht)]
  rw [he]
  exact (test.continuous.measurable.comp (measurable_stopped H F X hadapt s)).stronglyMeasurable

/-- The bounded-test interface is retained for the existing martingale
and continuation arguments. -/
theorem past_test_measurable (hadapt : ∀ t : Time H,
    Measurable[F (toNN H t)] (fun ω ↦ X ω t)) (s : Time H)
    (test : BoundedContinuousFunction (Path H E) ℝ) (htest : UsesPast H s test) :
    StronglyMeasurable[F (toNN H s)] (fun ω ↦ test (X ω)) :=
  continuous_past_test_measurable H F X hadapt s test.toContinuousMap htest

def martingale (f b : E → ℝ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  value H f b (X ω) (clock H q)

@[simp] theorem martingale_zero (f b : E → ℝ) (sample : Ω) : martingale H X f b 0 sample = 0 := by
  have hc : clock H 0 = origin H := Subtype.ext (min_eq_left H.property)
  unfold martingale
  rw [hc]
  simp [value, origin]

theorem martingale_adapted (f b : BoundedContinuousFunction E ℝ)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t)) :
    StronglyAdapted F (martingale H X f b) := by
  intro q
  let test : BoundedContinuousFunction (Path H E) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ value H f b x (clock H q))
      ((continuous_value H f b f.continuous b.continuous).comp (continuous_id.prodMk continuous_const))
      (2 * ‖f‖ + ‖b‖ * H) (fun x ↦ norm_value_bound H f b x (clock H q))
  have hm := past_test_measurable H F X hadapt (clock H q) test (value_usesPast H f b (clock H q))
  exact hm.mono (F.mono (show toNN H (clock H q) ≤ q from min_le_left _ _))

theorem martingale_continuous (f b : E → ℝ) (hf : Continuous f) (hb : Continuous b) (ω : Ω) :
    Continuous (fun q ↦ martingale H X f b q ω) :=
  (continuous_value H f b hf hb).comp (continuous_const.prodMk (continuous_clock H))

/-- A bounded canonical cylinder expression is an ordinary martingale
once it is a martingale along an actual localizing sequence. The bound
uses only the test and generator, not a moment bound on the state. -/
theorem martingale_of_stopped (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction E ℝ)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun sample ↦ X sample t))
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : IsLocalizingSequence F σ μ)
    (hM : ∀ N, Martingale (stoppedProcess (martingale H X f b) (σ N)) F μ) :
    Martingale (martingale H X f b) F μ := by
  have ha := martingale_adapted H F X f b hadapt
  have hl := BoundedLocalMartingale.locally_of_stopped μ F (martingale H X f b)
    (martingale_zero H X f b) σ hσ hM
  exact BoundedLocalMartingale.martingale μ F _ ha hl (2 * ‖f‖ + ‖b‖ * H)
    (fun q sample ↦ norm_value_bound H f b (X sample) (clock H q))

theorem stopped_martingale (f b : E → ℝ) (r : Ω → Time H) (q : Time H) (ω : Ω) :
    stoppedProcess (martingale H X f b) (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0))
      (toNN H q) ω = value H f b (X ω) (pastTime H (r ω) q) := by
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  exact congrArg (value H f b (X ω)) (clock_min H (r ω) q)

theorem stopped_martingale_native (f b : E → ℝ) (r : Ω → Time H) (q : ℝ≥0) (ω : Ω) :
    stoppedProcess (martingale H X f b) (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)) q ω =
      value H f b (X ω) (pastTime H (r ω) (clock H q)) := by
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  exact congrArg (value H f b (X ω)) (clock_min_native H (r ω) q)

/-- Exact replacement of the original generator by the cutoff generator
inside the stopped canonical expression. The original drift c may be
unbounded and no comparison outside the exit interval is required. -/
theorem stopped_generator_congr (f b c : E → ℝ) (r : Ω → Time H)
    (hbc : ∀ ω s, s.val < (r ω).val → b (X ω s) = c (X ω s)) :
    stoppedProcess (martingale H X f b) (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)) =
      stoppedProcess (martingale H X f c) (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)) := by
  funext q ω
  rw [stopped_martingale_native, stopped_martingale_native]
  exact value_congr_before H f b c (r ω) (clock H q) (X ω) (hbc ω)

/-- Generator replacement before an actual exit preserves the local
martingale property. This works on general joint state/driver path
spaces and discharges the repeated stopping and initial-time details. -/
theorem local_of_generator_agreement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction E ℝ) (c : E → ℝ) (hc : Continuous c)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun sample ↦ X sample t))
    (r : Ω → Time H) (hrstop : IsStoppingTime F (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0)))
    (hbc : ∀ᵐ sample ∂μ, ∀ t : Time H, t.val < (r sample).val → b (X sample t) = c (X sample t))
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : IsLocalizingSequence F σ μ)
    (hM : ∀ N, Martingale (stoppedProcess (martingale H X f c) (σ N)) F μ) :
    StronglyAdapted F (stoppedProcess (martingale H X f b) (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0))) ∧
      Locally (fun M ↦ Martingale M F μ) F
        (stoppedProcess (martingale H X f b) (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0))) μ := by
  let τ : Ω → WithTop ℝ≥0 := fun sample ↦ toNN H (r sample)
  let B := martingale H X f b
  let O := martingale H X f c
  have hBc := martingale_continuous H X f b f.continuous b.continuous
  have hOc := martingale_continuous H X f c f.continuous hc
  have ha := (martingale_adapted H F X f b hadapt).stoppedProcess hBc hrstop
  have hCont (sample : Ω) : Continuous (fun t ↦ stoppedProcess B τ t sample) := (hBc sample).stoppedProcess τ
  have heq : ∀ᵐ sample ∂μ, ∀ q, stoppedProcess B τ q sample = stoppedProcess O τ q sample := by
    filter_upwards [hbc] with sample hh q
    change stoppedProcess (martingale H X f b) (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0)) q sample =
      stoppedProcess (martingale H X f c) (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0)) q sample
    rw [stopped_martingale_native, stopped_martingale_native]
    exact value_congr_before H f b c (r sample) (clock H q) (X sample) hh
  have hStopped (N : ℕ) : Martingale (stoppedProcess (stoppedProcess B τ) (σ N)) F μ := by
    have hm := (hM N).stoppedProcess
      (fun sample t ↦ ((hOc sample).stoppedProcess (σ N)).continuousAt.continuousWithinAt) hrstop
    have hComm : stoppedProcess (stoppedProcess O τ) (σ N) = stoppedProcess (stoppedProcess O (σ N)) τ := by
      simp only [stoppedProcess_stoppedProcess']
      congr 1
      funext sample
      exact min_comm _ _
    rw [← hComm] at hm
    have hEqN := stoppedProcess_congr (τ := σ N) heq
    exact hm.congr (ha.stoppedProcess hCont (hσ.isStoppingTime N))
      (fun t ↦ hEqN.mono fun sample hh ↦ (hh t).symm)
  have hzero (sample : Ω) : stoppedProcess B τ 0 sample = 0 := by
    rw [stoppedProcess_eq_of_le (show (0 : WithTop ℝ≥0) ≤ τ sample from by
      exact WithTop.coe_le_coe.mpr zero_le)]
    exact martingale_zero H X f b sample
  exact ⟨ha, BoundedLocalMartingale.locally_of_stopped μ F _ hzero σ hσ hStopped⟩

/-- The stopped identity required by continuation follows from the
given canonical martingale and stopping-time property. The bounded
past-test and all random-time evaluation steps are discharged here. -/
theorem stopped_identity (μ : Measure Ω) [IsFiniteMeasure μ]
    (f b : BoundedContinuousFunction E ℝ)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hM : Martingale (martingale H X f b) F μ)
    (r : Ω → Time H) (hr : IsStoppingTime F (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)))
    (s t : Time H) (hst : s.val ≤ t.val)
    (test : BoundedContinuousFunction (Path H E) ℝ) (htest : UsesPast H s test) :
    (∫ ω, test (X ω) * (value H f b (X ω) (pastTime H (r ω) t) -
      value H f b (X ω) (pastTime H (r ω) s)) ∂μ) = 0 := by
  have hh := ContinuousStoppedMartingaleTests.stopped_weighted_increment μ F
    (martingale H X f b) hM (martingale_continuous H X f b f.continuous b.continuous)
    (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)) hr (toNN H s) (toNN H t) hst
    (fun ω ↦ test (X ω)) (past_test_measurable H F X hadapt s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  simpa only [stopped_martingale H X f b r] using hh

/-- An actual adapted canonical martingale gives all bounded past-test
identities under the law of its original continuous path. -/
theorem law_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction E ℝ) (hX : Measurable X)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun sample ↦ X sample t))
    (hM : Martingale (martingale H X f b) F μ) :
    PastedCylinderMartingale.Identity H f b (μ.map X) := by
  intro s t hst test htest
  have hψ : Continuous (fun x : Path H E ↦ test x * (value H f b x t - value H f b x s)) :=
    test.continuous.mul
      (((continuous_value H f b f.continuous b.continuous).comp (continuous_id.prodMk continuous_const)).sub
        ((continuous_value H f b f.continuous b.continuous).comp (continuous_id.prodMk continuous_const)))
  rw [integral_map hX.aemeasurable hψ.stronglyMeasurable.aestronglyMeasurable]
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hM
    (toNN H s) (toNN H t) hst (fun sample ↦ test (X sample))
    (past_test_measurable H F X hadapt s test htest) ‖test‖ (fun sample ↦ test.norm_coe_le_norm _)
  simpa only [martingale, clock_toNN] using hh

theorem continuation_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction E ℝ)
    (hX : Measurable X) (r : Ω → Time H) (hr : Measurable r)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hM : Martingale (martingale H X f b) F μ)
    (hrstop : IsStoppingTime F (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)))
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ]
    (hinitial : ∀ z : E, ∀ᵐ y ∂κ z, y (origin H) = z)
    (hfuture : ∀ z : E, PastedCylinderMartingale.Identity H f b (κ z)) :
    PastedCylinderMartingale.Identity H f b (StoppedContinuationMeasure.law H X r hX hr μ κ) :=
  PastedCylinderMartingale.law_identity H μ X r hX hr κ f b hinitial hfuture
    (fun s t hst test htest ↦ stopped_identity H F X μ f b hadapt hM r hrstop s t hst test htest)

/-- The unbounded-equation route needs the truncated generator only
locally up to its exit. Its stopped canonical expression is uniformly
bounded, so the local martingale upgrades to a genuine martingale before
the continuation theorem is applied. No global truncated equation for
the original unbounded solution is assumed. -/
theorem continuation_identity_of_local (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction E ℝ)
    (hX : Measurable X) (r : Ω → Time H) (hr : Measurable r)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hrstop : IsStoppingTime F (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)))
    (hlocal : Locally (fun M ↦ Martingale M F μ) F
      (stoppedProcess (martingale H X f b) (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0))) μ)
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ]
    (hinitial : ∀ᵐ sample ∂μ, ∀ᵐ y ∂κ (StoppedContinuationMeasure.state H X r sample),
      y (origin H) = StoppedContinuationMeasure.state H X r sample)
    (hfuture : ∀ᵐ sample ∂μ, PastedCylinderMartingale.Identity H f b
      (κ (StoppedContinuationMeasure.state H X r sample))) :
    PastedCylinderMartingale.Identity H f b (StoppedContinuationMeasure.law H X r hX hr μ κ) := by
  let τ : Ω → WithTop ℝ≥0 := fun ω ↦ toNN H (r ω)
  have hMc := martingale_continuous H X f b f.continuous b.continuous
  have hM : Martingale (stoppedProcess (martingale H X f b) τ) F μ :=
    BoundedLocalMartingale.martingale μ F _
      ((martingale_adapted H F X f b hadapt).stoppedProcess hMc hrstop)
      hlocal (2 * ‖f‖ + ‖b‖ * H)
      (fun q ω ↦ norm_value_bound H f b (X ω)
        (clock H (min (q : WithTop ℝ≥0) (τ ω)).untopA))
  apply PastedCylinderMartingale.law_identity_of_ae H μ X r hX hr κ f b hinitial hfuture
  intro s t hst test htest
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hM
    (toNN H s) (toNN H t) hst (fun ω ↦ test (X ω))
    (past_test_measurable H F X hadapt s test htest) ‖test‖ (fun ω ↦ test.norm_coe_le_norm _)
  simpa only [τ, stopped_martingale H X f b r] using hh

theorem continuation_identity_of_generator_agreement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction E ℝ) (c : E → ℝ)
    (hX : Measurable X) (r : Ω → Time H) (hr : Measurable r)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hrstop : IsStoppingTime F (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0)))
    (hbc : ∀ ω s, s.val < (r ω).val → b (X ω s) = c (X ω s))
    (hlocal : Locally (fun M ↦ Martingale M F μ) F
      (stoppedProcess (martingale H X f c) (fun ω ↦ (toNN H (r ω) : WithTop ℝ≥0))) μ)
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ]
    (hinitial : ∀ z : E, ∀ᵐ y ∂κ z, y (origin H) = z)
    (hfuture : ∀ z : E, PastedCylinderMartingale.Identity H f b (κ z)) :
    PastedCylinderMartingale.Identity H f b (StoppedContinuationMeasure.law H X r hX hr μ κ) := by
  apply continuation_identity_of_local H F X μ f b hX r hr hadapt hrstop ?_ κ
    (Filter.Eventually.of_forall fun sample ↦ hinitial (StoppedContinuationMeasure.state H X r sample))
    (Filter.Eventually.of_forall fun sample ↦ hfuture (StoppedContinuationMeasure.state H X r sample))
  rw [stopped_generator_congr H X f b c r hbc]
  exact hlocal

end SHEStochastic.AdaptedCanonicalPathTests
