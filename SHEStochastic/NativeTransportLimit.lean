module

public import SHEStochastic.SimultaneousSimpleApproximation
public import SHEStochastic.NativeCrossContinuity
public import MathFin.Foundations.GirsanovPredictableTheta

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeTransportLimit
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure η] {H : ℝ≥0}
local notation "νμ" => FiniteScalarIto.inputMeasure F μ H
local notation "νη" => FiniteScalarIto.inputMeasure F η H

/-- A common simple approximation passes an elementary transport identity
to every row lying in both L² spaces. Only one-way absolute continuity is
needed: the original integral and ordinary drift converge first under μ. -/
theorem of_simple (P : FiniteScalarIto.Coordinates F μ H ι)
    (R : FiniteScalarIto.Coordinates F η H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νμ) (hac : η ≪ μ)
    (hsimple : ∀ V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H),
      FiniteCylindricalIto.rawIntegral R e (FiniteCylindricalIto.simpleEmbedding (μ := η) e V) =ᵐ[η]
        (fun ω ↦ FiniteCylindricalIto.rawIntegral P e (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V) ω +
          NativeCrossEnergy.cross (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V) u ω))
    (f : Lp C 2 νμ) (g : Lp C 2 νη) (he : f =ᵐ[νμ] g) :
    FiniteCylindricalIto.rawIntegral R e g =ᵐ[η]
      (fun ω ↦ FiniteCylindricalIto.rawIntegral P e f ω + NativeCrossEnergy.cross f u ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨V, hVμ, hVη⟩ := SimultaneousSimpleApproximation.exists_sequence e f g hac he
  have hI := tendstoInMeasure_of_tendsto_Lp
    ((FiniteCylindricalIto.rawIntegral P e).continuous.tendsto f |>.comp hVμ)
  have hC := NativeCrossContinuity.tendstoInMeasure hVμ u
  obtain ⟨ns, hns, hIa, hCa⟩ := MathFin.exists_subseq_tendsto_ae₂ hI hC id Filter.tendsto_id
  have hK := tendstoInMeasure_of_tendsto_Lp
    (((FiniteCylindricalIto.rawIntegral R e).continuous.tendsto g |>.comp hVη).comp hns.tendsto_atTop)
  obtain ⟨ms, hms, hKa⟩ := hK.exists_seq_tendsto_ae
  have hsteps : ∀ᵐ ω ∂η, ∀ k : ℕ,
      FiniteCylindricalIto.rawIntegral R e (FiniteCylindricalIto.simpleEmbedding (μ := η) e (V (ns (ms k)))) ω =
        FiniteCylindricalIto.rawIntegral P e (FiniteCylindricalIto.simpleEmbedding (μ := μ) e (V (ns (ms k)))) ω +
          NativeCrossEnergy.cross (FiniteCylindricalIto.simpleEmbedding (μ := μ) e (V (ns (ms k)))) u ω :=
    ae_all_iff.mpr (fun k ↦ hsimple (V (ns (ms k))))
  filter_upwards [hKa, hIa.filter_mono hac.ae_le, hCa.filter_mono hac.ae_le, hsteps]
    with ω hKω hIω hCω hsω
  have hlim := (hIω.comp hms.tendsto_atTop).add (hCω.comp hms.tendsto_atTop)
  have heq : (fun k ↦ FiniteCylindricalIto.rawIntegral R e
      (FiniteCylindricalIto.simpleEmbedding (μ := η) e (V (ns (ms k)))) ω) =
      (fun k ↦ FiniteCylindricalIto.rawIntegral P e
        (FiniteCylindricalIto.simpleEmbedding (μ := μ) e (V (ns (ms k)))) ω +
          NativeCrossEnergy.cross (FiniteCylindricalIto.simpleEmbedding (μ := μ) e (V (ns (ms k)))) u ω) :=
    funext hsω
  exact tendsto_nhds_unique hKω (by simpa only [id_eq, Function.comp_apply, heq] using hlim)

end SHEStochastic.NativeTransportLimit
