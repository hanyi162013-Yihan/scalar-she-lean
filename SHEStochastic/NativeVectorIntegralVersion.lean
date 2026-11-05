module

public import SHEStochastic.NativeMartingaleVersion
public import SHE.StandardFiniteIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.NativeVectorIntegralVersion
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- Finite vectors of arbitrary native L2 integrals have one continuous
predictable version. This reuses ordinary native martingale versions,
without imposing a singular endpoint bound or another BDG hypothesis. -/
theorem exists_version {n : ℕ} (N : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (R : Fin n → Process (E := C) F μ H) :
    ∃ Y : ℝ≥0 × Ω → WordRecursion.State n,
      StronglyMeasurable[F.predictable] Y ∧
      (∀ ω, Continuous (fun t => Y (t,ω))) ∧
      ∀ t, (fun ω => Y (t,ω)) =ᵐ[μ]
        StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto N.toCoordinates e) 0 R t := by
  choose Y hc _ hp _ hr using fun i => NativeMartingaleVersion.exists_version N e hnull (R i)
  refine ⟨fun p => WithLp.toLp 2 (fun i => Y i p.1 p.2),?_,?_,?_⟩
  · letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
      (measurable_pi_iff.mpr (fun i => (hp i).measurable))).stronglyMeasurable
  · intro ω
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_pi (fun i => hc i ω))
  · intro t
    filter_upwards [ae_all_iff.mpr (fun i => hr i t)] with ω hω
    apply PiLp.ext
    intro i
    simpa only [StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,PiLp.zero_apply,zero_add] using hω i

end SHEStochastic.NativeVectorIntegralVersion
