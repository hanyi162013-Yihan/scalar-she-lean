module

public import SHEStochastic.ScalarLipschitzCanonicalDriver
public import SHEStochastic.NativeIntegralUniqueness
public import SHEStochastic.FiniteCylindricalLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzClampedDriver
open MeasureTheory Filter SHE SHE.PredictableL2 ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω I C : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H I)

def value (i : I) (t : ℝ≥0) (ω : Ω) : ℝ := P.W i (min t H) ω-P.W i 0 ω

omit [Countable I] in
theorem value_ae (i : I) (t : ℝ≥0) (ht : t≤H) : value P i t=ᵐ[μ] P.W i t := by
  filter_upwards [FiniteScalarIto.zero_ae P.toCoordinates i] with ω hω
  rw [value,min_eq_left ht,hω,sub_zero]

def family : FiniteScalarIto.Family F μ H I where
  W := value P
  continuous i ω :=
    ((P.continuous i ω).comp (continuous_id.min continuous_const)).sub continuous_const
  adapted i t := ((P.adapted i (min t H)).mono (F.mono (min_le_left _ _)) le_rfl).sub
    ((P.adapted i 0).mono (F.mono (show (0 : ℝ≥0)≤t from zero_le)) le_rfl)
  law n a := by
    constructor
    · intro t ht
      apply ((P.law n a).1 t ht).congr
      filter_upwards [ae_all_iff.mpr (fun i => value_ae P (a i) (t i) (ht i))] with ω hω
      apply PiLp.ext
      intro i
      exact hω i
    · intro s t hst ht
      have he : (fun ω => (WithLp.toLp 2 (fun i : Fin n => value P (a i) t ω-value P (a i) s ω)
          : WordRecursion.State n)) =
          (fun ω => (WithLp.toLp 2 (fun i : Fin n => P.W (a i) t ω-P.W (a i) s ω)
          : WordRecursion.State n)) := by
        funext ω
        apply PiLp.ext
        intro i
        change value P (a i) t ω-value P (a i) s ω=P.W (a i) t ω-P.W (a i) s ω
        rw [value,value,min_eq_left ht,min_eq_left (hst.trans ht)]
        ring
      change Indep (MeasurableSpace.comap (fun ω => (WithLp.toLp 2
        (fun i : Fin n => value P (a i) t ω-value P (a i) s ω) : WordRecursion.State n)) _)
        (F s) μ
      rw [he]
      exact (P.law n a).2 s t hst ht

/-- Centering and clamping retain every native stochastic integral
over the prescribed horizon. -/
theorem integral_eq (e : HilbertBasis I ℝ C) (u : Process (E := C) F μ H) :
    (FiniteCylindricalIto.terminalIto (family P).toCoordinates e).integral u =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u := by
  symm
  apply NativeIntegralUniqueness.integral (family P) e
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
  intro i t ht
  exact (FiniteCylindricalIto.coordinate_integral P e i t ht).trans (value_ae P i t ht).symm

end SHEStochastic.ScalarLipschitzClampedDriver
