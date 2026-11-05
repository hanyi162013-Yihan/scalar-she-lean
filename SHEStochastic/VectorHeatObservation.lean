module

public import SHEStochastic.VectorHeatMean
public import SHEStochastic.MatrixDeterministicObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.VectorHeatObservation
open MeasureTheory SHE SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

def component (i : d) : Physical (d := d) →L[ℝ] DyadicApproximation.RealL2 :=
  (PiLp.proj 2 (fun _ : d => DyadicApproximation.RealL2) i).comp
    VectorHeat.coordinates.toContinuousLinearEquiv.toContinuousLinearMap

/-- A vector heat observation is a concrete bounded linear map on
the actual spatial Hilbert state. -/
def observation (ε : ℝ) (x : HeatCircle) : Physical (d := d) →L[ℝ] EuclideanSpace ℝ d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (NativeHeatObservation.functional ε x).comp (component i)))

theorem apply_component (ε : ℝ) (x : HeatCircle) (u : Physical (d := d)) (i : d) :
    observation ε x u i=NativeHeatObservation.functional ε x (VectorHeat.coordinates u i) := rfl

theorem mean {ε : ℝ} (hε : 0 < ε) (x : HeatCircle) (u : Physical (d := d)) :
    observation ε x u=VectorHeatMean.mean u (ε,x) := by
  apply PiLp.ext
  intro i
  exact NativeHeatObservation.functional_physical hε x _

/-- Exact componentwise propagation through the native unit-circle
heat semigroup, retaining the analytic time-scale constant. -/
theorem propagate {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (x : HeatCircle) (u : Physical (d := d)) :
    observation ε x (VectorHeat.heat t u)=
      observation (ε+NativeHeatObservation.timeScale*t) x u := by
  apply PiLp.ext
  intro i
  rw [apply_component,apply_component,VectorHeat.coordinate_heat]
  have htime : NativeHeatObservation.timeScale*t/NativeHeatObservation.timeScale=t := by
    field_simp [NativeHeatObservation.timeScale_pos.ne']
  have hh := NativeHeatObservation.functional_heat hε
    (mul_nonneg NativeHeatObservation.timeScale_pos.le ht) x (VectorHeat.coordinates u i)
  simpa only [NativeHeatObservation.heat,htime] using hh

def test (ε : ℝ) (x : HeatCircle) (i : d) : Physical (d := d) :=
  (InnerProductSpace.toDual ℝ (Physical (d := d))).symm
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (observation ε x))

theorem test_pairing (ε : ℝ) (x : HeatCircle) (i : d) (u : Physical (d := d)) :
    inner ℝ (test ε x i) u=observation ε x u i := by
  have he := (InnerProductSpace.toDual ℝ (Physical (d := d))).apply_symm_apply
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (observation ε x))
  exact congrArg (fun L : Physical (d := d) →L[ℝ] ℝ => L u) he

section Native
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (N : FiniteScalarIto.Family F μ H ((Fin n) × FiniteHaar.HaarNode))
  (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 → Profile (Fin n)) (hUpper : ∀ r, (Q r).upper ≤ U)
  (hQ : Measurable (fun p : ℝ≥0 × AddCircle (1 : ℝ) => (Q p.1).value p.2))

/-- Every finite list of actual vector heat-observation components of
the deterministic matrix convolution has its genuine joint Gaussian law.
All times, centers, component indices and repeated observations remain. -/
theorem joint_gaussian {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ H)
    (ε : Fin k → ℝ) (x : Fin k → HeatCircle) (a : Fin k → Fin n) :
    ProbabilityTheory.HasLaw
      (fun ω => (WithLp.toLp 2 (fun i => observation (ε i) (x i)
        (NativeMatrixConvolution.value N U hU (fun p => Q p.1) (fun p => hUpper p.1)
          (MatrixDeterministicObservations.predictable_field F Q hQ) (t i) (ht i) ω) (a i)) :
        EuclideanSpace ℝ (Fin k)))
      (ProbabilityTheory.multivariateGaussian 0
        (Matrix.gram ℝ (fun i => MatrixDeterministicObservations.source F μ H U hU Q hUpper hQ
          (t i) (ht i) (test (ε i) (x i) (a i))))) μ := by
  have he := MatrixDeterministicObservations.vector_gaussian F μ H U hU Q hUpper hQ N t ht
    (fun i => test (ε i) (x i) (a i))
  have hfun : MatrixDeterministicObservations.vector F μ H U hU Q hUpper hQ N t ht
      (fun i => test (ε i) (x i) (a i)) =
      (fun ω => (WithLp.toLp 2 (fun i => observation (ε i) (x i)
        (NativeMatrixConvolution.value N U hU (fun p => Q p.1) (fun p => hUpper p.1)
          (MatrixDeterministicObservations.predictable_field F Q hQ) (t i) (ht i) ω) (a i)) :
        EuclideanSpace ℝ (Fin k))) := by
    funext ω
    apply PiLp.ext
    intro i
    exact test_pairing (ε i) (x i) (a i) _
  rw [hfun] at he
  exact he

end Native
end SHEStochastic.VectorHeatObservation
