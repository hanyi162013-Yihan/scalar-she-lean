module

public import SHEStochastic.CanonicalApproximationCompactness
public import SHEStochastic.WeakLimitProbabilityTools
public import SHE.CanonicalStateDriverPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.CanonicalInitialLaw
open MeasureTheory ProbabilityTheory Filter SHE
open StoppedPathPasting
open scoped NNReal ENNReal Topology

variable {E ι : Type*} [Countable ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual initial state and every retained Brownian coordinate. -/
def initial (H : ℝ≥0) (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    E × (ι → ℝ) := (x.1 (origin H), fun i => x.2 i (origin H))

theorem continuous_initial (H : ℝ≥0) : Continuous (initial (E := E) (ι := ι) H) :=
  ((continuous_eval_const _).comp continuous_fst).prodMk
    (continuous_pi fun i => (continuous_eval_const _).comp ((continuous_apply i).comp continuous_snd))

/-- A deterministic initial joint law gives the usual almost-sure
initial condition for the actual canonical state process. -/
theorem initial_of_dirac [DecidableEq ι] (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H)) (u : E)
    (h : Q.map (initial H)=Measure.dirac (u,fun _ : ι => (0 : ℝ))) :
    CanonicalStateDriverFiltration.state H 0 =ᵐ[Q] fun _ => u := by
  have hh : ProbabilityTheory.HasLaw (initial H) (Measure.dirac (u,fun _ : ι => (0 : ℝ))) Q :=
    ⟨(continuous_initial H).measurable.aemeasurable,h⟩
  filter_upwards [hh.ae_eq_of_dirac] with x hx
  have he := congrArg Prod.fst hx
  change x.1 (origin H)=u at he
  change x.1 (CanonicalStateDriverFiltration.clock H 0)=u
  have hc : CanonicalStateDriverFiltration.clock H 0=origin H := by
    apply Subtype.ext
    change min (0 : ℝ) (H : ℝ)=0
    exact min_eq_left H.coe_nonneg
  rw [hc]
  exact he

variable {Ω : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℕ → ℝ≥0 → Ω → E)
  (hcW : ∀ k sample, Continuous (fun t ↦ W k t sample))
  (hW : ∀ k, StronglyMeasurable[F.predictable] (Function.uncurry (W k)))
  (P : ℕ → FiniteScalarIto.Family F μ H ι)

include hW in
/-- The actual joint weak limit keeps the given random initial state
law and starts every centered driver at zero. -/
theorem preserved (ξ : Ω → E) (hξ : Measurable ξ)
    (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H))
    (φ : ℕ → ℕ)
    (hlim : Tendsto ((CanonicalApproximationCompactness.varyingLaws F μ H W hcW P) ∘ φ) atTop (𝓝 Q)) :
    (Q : Measure _).map (initial H) = μ.map (fun sample ↦ (ξ sample, fun _ : ι ↦ (0 : ℝ))) := by
  letI : MetricSpace (ι → ℝ) := TopologicalSpace.metrizableSpaceMetric _
  let Z : Ω → E × (ι → ℝ) := fun sample ↦ (ξ sample, fun _ ↦ 0)
  have hZ : Measurable Z := hξ.prodMk measurable_const
  apply (WeakLimitProbabilityTools.hasLaw
    ((CanonicalApproximationCompactness.varyingLaws F μ H W hcW P) ∘ φ) Q hlim
    (initial H) (continuous_initial _) (μ.map Z) ?_).map_eq
  intro k
  let R := P (φ k)
  have ha (t : ℝ≥0) : Measurable[F t] (W (φ k) t) :=
    ((show IsStronglyPredictable F (W (φ k)) from hW (φ k)).stronglyAdapted t).measurable
  refine ⟨(continuous_initial _).measurable.aemeasurable, ?_⟩
  change (μ.map (CanonicalNativeBrownian.bundle F μ H R (W (φ k)) (hcW (φ k)))).map
    (initial H) = μ.map Z
  rw [Measure.map_map (continuous_initial _).measurable
    (CanonicalNativeBrownian.measurable_bundle F μ H R (W (φ k)) (hcW (φ k)) ha)]
  apply Measure.map_congr
  filter_upwards [hInitial (φ k)] with sample hs
  change (W (φ k) (0+(origin H).val.toNNReal) sample,
      fun i ↦ (P (φ k)).W i (0+(origin H).val.toNNReal) sample - (P (φ k)).W i 0 sample) =
    (ξ sample, fun _ : ι ↦ 0)
  simp only [origin, Real.toNNReal_zero, zero_add, hs, sub_self]


end SHEStochastic.CanonicalInitialLaw
