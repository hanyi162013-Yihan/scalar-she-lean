module

public import SHEStochastic.NativeTerminalGirsanovLaw
public import SHEStochastic.NativeBrownianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.NativeChangedCoordinates
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def changedMeasure (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) : Measure Ω :=
  ExponentialChangeMeasure.measure μ (fun ω ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω)
    (StochasticExponential.bracket F μ H u)

theorem shift_adapted (R u : Process (E := C) F μ H) (X : ℝ≥0 → Ω → ℝ)
    (hX : StronglyAdapted F X) (t : ℝ≥0) :
    StronglyMeasurable[F t] (girsanovShift u R X t) := by
  have hq : StronglyMeasurable[F.predictable] (fun p ↦ inner ℝ (R p) (u p)) :=
    (Lp.stronglyMeasurable R).inner (Lp.stronglyMeasurable u)
  have hp := PredictableBracket.stronglyMeasurable_primitive (F := F) (timeMeasure H)
    (fun p ↦ inner ℝ (R p) (u p)) hq (min t H)
  have he : (fun ω ↦ ∫ r, (Set.Iio (min t H)).indicator
      (fun r ↦ inner ℝ (R (r, ω)) (u (r, ω))) r ∂timeMeasure H) =
      (fun ω ↦ ∫ r, inner ℝ (R (r, ω)) (u (r, ω)) ∂timeMeasure (min t H)) := by
    funext ω
    rw [timeMeasure_eq, timeMeasure_eq, NativeClockIntegral.before H (min t H) (min_le_right _ _)]
  rw [he] at hp
  exact (hX t).add (hp.mono (F.mono (min_le_left t H)))

/-- Actual drift-shifted coordinates under the original exponential
measure. Terminal integration only needs these adapted finite laws;
everywhere path continuity is not imposed as an extra assumption. -/
def coordinates (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H)
    (hu : ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H u ω ≤ 1) :
    FiniteScalarIto.Coordinates F (changedMeasure P e u) H ι where
  W i := girsanovShift u (RawCylindricalCoordinates.row F μ H (e : ι → C) i) (P.W i)
  adapted i t := (shift_adapted _ u (P.W i) (fun t ↦ (P.adapted i t).stronglyMeasurable) t).measurable
  law n a := by
    apply NativeTerminalGirsanovLaw.standardTerminalGirsanovLaw P e u hu n
      (fun i ↦ RawCylindricalCoordinates.row F μ H (e : ι → C) (a i))
      (fun i ↦ P.W (a i)) (fun i j ↦ if a i = a j then 1 else 0)
    · intro i
      exact StronglyAdapted.isStronglyPredictable_of_leftContinuous
        (fun t ↦ (P.adapted (a i) t).stronglyMeasurable)
        (fun ω t ↦ (P.continuous (a i) ω).continuousWithinAt)
    · intro i ω
      exact P.continuous (a i) ω
    · intro t htH
      exact ae_all_iff.mpr (fun i ↦ (FiniteCylindricalIto.coordinate_integral P e (a i) t htH).symm)
    · filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦
        RotatedCylindricalCoordinates.constant_ae F μ H (e (a i)))] with p hp i j
      change inner ℝ (RotatedCylindricalCoordinates.constant F μ H (e (a i)) p)
        (RotatedCylindricalCoordinates.constant F μ H (e (a j)) p) = _
      rw [hp i, hp j]
      exact orthonormal_iff_ite.mp e.orthonormal (a i) (a j)

def changedIto (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H)
    (hu : ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H u ω ≤ 1) :
    StandardTerminalIto (C := C) (E := ℝ) F (changedMeasure P e u) H := by
  letI : IsProbabilityMeasure (changedMeasure P e u) :=
    NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
  exact FiniteCylindricalIto.terminalIto (coordinates P e u hu) e

end SHEStochastic.NativeChangedCoordinates
