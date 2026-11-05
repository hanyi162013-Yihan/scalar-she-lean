module

public import SHEStochastic.ScalarLipschitzItoMoment
public import SHE.DampedContinuousVersion
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.ScalarLipschitzContinuousVersion
open MeasureTheory Set Filter SHE SHE.PredictableL2
open ScalarLipschitzItoMoment
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

omit [IsProbabilityMeasure μ] in
/-- Lift a fixed-time stochastic family on a general positive horizon
to continuous predictable paths. The time normalization is deterministic. -/
theorem exists_version (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (V : ∀ t : ℝ≥0, t≤H → Lp E 2 μ)
    (hV : ∀ t (ht : t≤H), StronglyMeasurable[F t] (V t ht : Ω → E))
    (K : ℝ) (hK : 0≤K)
    (hinc : ∀ s t (hs : s≤H) (ht : t≤H),
      moment 16 (fun ω => V s hs ω-V t ht ω) μ ≤ ENNReal.ofReal (K*((s : ℝ)-(t : ℝ))^2)) :
    ∃ Z : ℝ≥0 → Ω → E,
      (∀ ω, Continuous (fun t => Z t ω)) ∧ StronglyAdapted F Z ∧
      ∀ t (ht : t≤H), Z t=ᵐ[μ] V t ht := by
  let X (r : ℝ) (ω : Ω) : E :=
    V (DampedUnitTimeMoments.clock H r) (DampedUnitTimeMoments.clock_bound H r) ω
  have hXm (r : ℝ) : Measurable (X r) := (Lp.stronglyMeasurable _).measurable
  have hM {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      moment 16 (fun ω => X s ω-X t ω) μ≤ENNReal.ofReal (K*(H : ℝ)^2*|s-t|^2) := by
    have hh := hinc (DampedUnitTimeMoments.clock H s) (DampedUnitTimeMoments.clock H t)
      (DampedUnitTimeMoments.clock_bound H s) (DampedUnitTimeMoments.clock_bound H t)
    apply hh.trans_eq
    rw [DampedUnitTimeMoments.clock_coe H hs,DampedUnitTimeMoments.clock_coe H ht,←mul_sub,mul_pow,sq_abs]
    congr 1
    ring
  let Z (t : ℝ≥0) (ω : Ω) : E :=
    KolmogorovModification.modification X (DampedContinuousVersion.normalizedTime H t) ω
  have hZc (ω : Ω) : Continuous (fun t => Z t ω) :=
    (KolmogorovModification.continuousOn_modification X ω).comp_continuous
      (DampedContinuousVersion.continuous_normalizedTime H)
      (DampedContinuousVersion.normalizedTime_mem hH)
  have hZ (t : ℝ≥0) : Z t=ᵐ[μ] V (min t H) (min_le_right _ _) := by
    have he := KolmogorovModification.modification_ae μ X (fun r _ => hXm r)
      (mul_nonneg hK (sq_nonneg (H : ℝ))) (fun _ hs _ ht => hM hs ht)
      (DampedContinuousVersion.normalizedTime_mem hH t)
    change Z t=ᵐ[μ] V (DampedUnitTimeMoments.clock H
      (DampedContinuousVersion.normalizedTime H t)) _ at he
    simpa only [DampedContinuousVersion.clock_normalizedTime hH] using he
  refine ⟨Z,hZc,?_,?_⟩
  · intro t
    exact NullCompleteFiltration.stronglyMeasurable_congr F μ hn t
      ((hV (min t H) (min_le_right _ _)).mono (F.mono (min_le_left _ _))) (hZ t)
  · intro t ht
    simpa only [min_eq_left ht] using hZ t

end SHEStochastic.ScalarLipschitzContinuousVersion
