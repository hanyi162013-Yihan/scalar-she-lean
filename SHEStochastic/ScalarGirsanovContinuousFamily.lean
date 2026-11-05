module

public import SHEStochastic.ScalarGirsanovUncappedLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovContinuousFamily
open MeasureTheory SHE SHE.PredictableL2 ProbabilityTheory Filter Set
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure η] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (u : Process (E := C) F μ H)

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "U" => FiniteCylindricalIto.processTransport u
local notation "S" => ScalarGirsanovCoordinateShift.shift P e u

private theorem shift_continuous (i : ι) : ∀ᵐ ω ∂μ,Continuous (fun t => S i t ω) := by
  have he : ∀ᵐ ω ∂μ,∀ t : ℝ≥0,
      S i t ω=P.W i t ω+TimeEnergyCap.primitive (H := H)
        (fun r => inner ℝ (e i) (U (r,ω))) (min t H) := by
    filter_upwards [ScalarGirsanovCoordinateShift.primitive P e u i] with ω hω t
    have h := hω (min t H) (min_le_right _ _)
    change P.W i (min t H) ω +
      (∫ r, inner ℝ (RawCylindricalCoordinates.row F μ H (e : ι → C) i (r,ω)) (u (r,ω))
        ∂timeMeasure (min (min t H) H)) =
      P.W i (min t H) ω+TimeEnergyCap.primitive (H := H)
        (fun r => inner ℝ (e i) (U (r,ω))) (min t H) at h
    rw [min_eq_left (min_le_right t H)] at h
    exact congrArg (fun y : ℝ => P.W i t ω+y) (add_left_cancel h)
  have hi := ((NativeEnergy.product_memLp U).integrable (by norm_num)).prod_left_ae
  filter_upwards [he,hi] with ω hω hi
  have hcont := (TimeEnergyCap.continuous_primitive (H := H) (hi.const_inner (e i))).comp
    (continuous_id.min (continuous_const (y := H)))
  have hEq : (fun t => S i t ω) = fun t => P.W i t ω+TimeEnergyCap.primitive (H := H)
      (fun r => inner ℝ (e i) (U (r,ω))) (min t H) := funext hω
  rw [hEq]
  exact (P.continuous i ω).add hcont

/-- An actual continuous cylindrical family can be chosen for the
shift, on the same null-complete space and under the changed law. -/
theorem exists_family (hac : η ≪ μ) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hLaw : ∀ (n : ℕ) (a : Fin n → ι),
      FiniteBrownianLawOn F η H (fun i => S (a i)) (fun i j => if a i=a j then 1 else 0)) :
    ∃ R : FiniteScalarIto.Family F η H ι,
      ∀ i,∀ᵐ ω ∂μ,∀ t,R.W i t ω=S i t ω := by
  classical
  let W (i : ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if Continuous (fun t => S i t ω) then S i t ω else 0
  have hW (i : ι) : ∀ᵐ ω ∂μ,∀ t,W i t ω=S i t ω := by
    filter_upwards [shift_continuous P e u i] with ω hω t
    exact ite_eq_left hω
  have hc (i : ι) (ω : Ω) : Continuous (fun t => W i t ω) := by
    by_cases h : Continuous (fun t => S i t ω)
    · simp only [W,h,ite_true]
    · simp only [W,h,ite_false,continuous_const]
  have ha (i : ι) : StronglyAdapted F (W i) :=
    NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull (W i) (fun t =>
      ⟨S i t,(ScalarGirsanovCoordinateShift.adapted P e u i t).stronglyMeasurable,
        (hW i).mono (fun _ hω => hω t)⟩)
  refine ⟨⟨⟨W,fun i t => (ha i t).measurable,?_⟩,hc⟩,hW⟩
  intro n a
  have he : ∀ᵐ ω ∂η,∀ i : Fin n,∀ t,W (a i) t ω=S (a i) t ω :=
    (ae_all_iff.mpr (fun i => hW (a i))).filter_mono hac.ae_le
  constructor
  · intro t ht
    apply ((hLaw n a).1 t ht).congr
    filter_upwards [he] with ω hω
    exact congrArg (WithLp.toLp 2) (funext fun i => hω i (t i))
  · intro s t hst ht
    have hEq : (fun ω => WithLp.toLp 2 (fun i => W (a i) t ω-W (a i) s ω)) =ᵐ[η]
        (fun ω => WithLp.toLp 2 (fun i => S (a i) t ω-S (a i) s ω)) := by
      filter_upwards [he] with ω hω
      exact congrArg (WithLp.toLp 2) (funext fun i => congrArg₂ (·-·) (hω i t) (hω i s))
    have hold := (hLaw n a).2 s t hst ht
    rw [BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin n))] at hold
    have hi := ConditionalCharacteristic.indep_comap_congr (F s) hEq hold
    rwa [←BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin n))] at hi

end SHEStochastic.ScalarGirsanovContinuousFamily
