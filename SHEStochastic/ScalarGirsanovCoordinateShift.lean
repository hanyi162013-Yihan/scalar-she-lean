module

public import SHEStochastic.NativeSimpleTransport
public import SHEStochastic.ScalarEnergyCapGirsanovLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovCoordinateShift
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (u : Process (E := C) F μ H)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "U" => FiniteCylindricalIto.processTransport u
local notation "Q" => NativeChangedCoordinates.changedMeasure P e u

/-- This is the literal shift before imposing any energy cap. -/
def shift (i : ι) (t : ℝ≥0) : Ω → ℝ :=
  girsanovShift u (RawCylindricalCoordinates.row F μ H (e : ι → C) i) (P.W i) t

omit [Countable ι] in
theorem adapted (i : ι) (t : ℝ≥0) : Measurable[F t] (shift P e u i t) :=
  (NativeChangedCoordinates.shift_adapted _ u (P.W i) (fun s => (P.adapted i s).stronglyMeasurable) t).measurable

/-- The ordinary primitive of the control uses one null set for every
time on the original horizon. -/
theorem primitive (i : ι) : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t≤H →
    shift P e u i t ω = P.W i t ω +
      ∫ r, (Set.Iio t).indicator (fun r => inner ℝ (e i) (U (r,ω))) r ∂νt := by
  have he : (fun p => inner ℝ (RawCylindricalCoordinates.row F μ H (e : ι → C) i p) (u p)) =ᵐ[νin]
      (fun p => inner ℝ (e i) (U p)) := by
    filter_upwards [FiniteCylindricalIto.constantRow_trim_ae e i,
      FiniteCylindricalIto.processTransport_ae u] with p hr ht
    rw [hr,ht]
  filter_upwards [NativeSimpleTransport.path_ae _ _ he] with ω hω
  intro t htH
  change P.W i t ω + (∫ r, inner ℝ
    (RawCylindricalCoordinates.row F μ H (e : ι → C) i (r,ω)) (u (r,ω))
      ∂timeMeasure (min t H)) = _
  rw [min_eq_left htH,timeMeasure_eq,←NativeClockIntegral.before H t htH]
  congr 1
  apply integral_congr_ae
  filter_upwards [hω] with r hr
  by_cases ht : r<t <;> simp only [Set.indicator_apply,Set.mem_Iio,ht,ite_true,ite_false]
  exact hr

/-- Under any deterministic energy cap the shifted coordinates are
Brownian with their full past and exact joint covariance. -/
theorem finite_cap (K : ℝ) (hK : 0≤K)
    (hu : ∀ᵐ ω ∂μ,StochasticExponential.bracket F μ H u ω≤K)
    (n : ℕ) (a : Fin n → ι) :
    FiniteBrownianLawOn F Q H (fun i => shift P e u (a i))
      (fun i j => if a i=a j then 1 else 0) := by
  apply ScalarEnergyCapGirsanovLaw.law P e K hK u hu n
    (fun i => RawCylindricalCoordinates.row F μ H (e : ι → C) (a i))
    (fun i => P.W (a i)) (fun i j => if a i=a j then 1 else 0)
  · intro i
    exact StronglyAdapted.isStronglyPredictable_of_leftContinuous
      (fun t => (P.adapted (a i) t).stronglyMeasurable)
      (fun ω t => (P.continuous (a i) ω).continuousWithinAt)
  · intro i ω
    exact P.continuous (a i) ω
  · intro t htH
    exact ae_all_iff.mpr (fun i => (FiniteCylindricalIto.coordinate_integral P e (a i) t htH).symm)
  · filter_upwards [ae_all_iff.mpr (fun i : Fin n =>
      RotatedCylindricalCoordinates.constant_ae F μ H (e (a i)))] with p hp i j
    change inner ℝ (RotatedCylindricalCoordinates.constant F μ H (e (a i)) p)
      (RotatedCylindricalCoordinates.constant F μ H (e (a j)) p) = _
    rw [hp i,hp j]
    exact orthonormal_iff_ite.mp e.orthonormal (a i) (a j)

/-- A shifted simple scalar integral has the expected signed ordinary
drift on the original sample path. The coordinates may have been built
under any absolutely continuous probability. -/
theorem scalar_simple {η : Measure Ω} [IsProbabilityMeasure η]
    (R : FiniteScalarIto.Coordinates F η H ι)
    (hR : ∀ i t,t≤H → R.W i t =ᵐ[μ] shift P e u i t)
    (i : ι) (V : FiniteScalarIto.Simple F H) :
    let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    FiniteScalarIto.simpleValue R i V =ᵐ[μ]
      (fun ω => FiniteScalarIto.simpleValue P.toCoordinates i V ω +
        NativeCrossEnergy.cross
          (L2HilbertSum.lift νin (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V)) U ω) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have he (p : V.val.value.support) : ∀ᵐ ω ∂μ,
      R.W i p.val.2 ω=shift P e u i p.val.2 ω ∧
      R.W i p.val.1 ω=shift P e u i p.val.1 ω := by
    filter_upwards [hR i p.val.2 (V.property p.val p.property),
      hR i p.val.1 ((V.val.le_of_mem_support_value p.val p.property).trans (V.property p.val p.property))]
      with ω ht hs
    exact ⟨ht,hs⟩
  filter_upwards [primitive P e u i,NativeSimpleTransport.cross_basis_simple e u i V,
    ae_all_iff.mpr he] with ω hc hd he
  change (∑ p ∈ V.val.value.support, V.val.value p ω * (R.W i p.2 ω - R.W i p.1 ω)) =
    (∑ p ∈ V.val.value.support, V.val.value p ω * (P.W i p.2 ω - P.W i p.1 ω)) + _
  rw [hd,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(he ⟨p,hp⟩).1,(he ⟨p,hp⟩).2,
    hc p.2 (V.property p hp),hc p.1 ((V.val.le_of_mem_support_value p hp).trans (V.property p hp))]
  ring

end SHEStochastic.ScalarGirsanovCoordinateShift
