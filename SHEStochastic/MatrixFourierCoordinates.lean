module

public import SHEStochastic.NativeFourierHeatCoordinate
public import SHEStochastic.NativeFourierStateSeparation
public import SHEStochastic.VectorAnalyticHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFourierCoordinates
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation MatrixInfiniteHaar AddCircle
open scoped NNReal ENNReal
local instance matrixFourier_unitPeriod : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance matrixFourier_heatPeriod : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))

def weight (a : ℂ →L[ℝ] ℝ) (n : ℤ) : C(AddCircle (1 : ℝ),ℝ) :=
  ⟨fun x => a (fourier (-n) x),a.continuous.comp (fourier (-n)).continuous⟩

/-- A real Fourier coordinate of one actual vector component. -/
def coordinate (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Physical (d := d) →L[ℝ] ℝ :=
  (NativeFourierHeatCoordinate.coordinate a n).comp (VectorHeatObservation.component i)

/-- The original scalar Fourier convention is exactly the normalized
unit-circle weighted integral. No clock or spatial normalization is lost. -/
theorem scalar_integral (a : ℂ →L[ℝ] ℝ) (n : ℤ) (v : RealL2) :
    NativeFourierHeatCoordinate.coordinate a n v=∫ x : AddCircle (1 : ℝ),weight a n x*v x ∂ν := by
  change a (NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed v))=_
  rw [NativeMultiplierFourierIntegral.coefficient_apply,NativeHeatObservation.embed_apply,
    CircleNormalization.fourierCoeff_push]
  unfold fourierCoeff
  change a (∫ x : AddCircle (1 : ℝ),fourier (-n) x*(realEmbed v) x ∂ν)=_
  have hi : Integrable (fun x : AddCircle (1 : ℝ) => fourier (-n) x*(realEmbed v) x) ν :=
    ((Lp.memLp (realEmbed v)).integrable one_le_two).bdd_mul
      (fourier (-n)).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => show ‖fourier (-n) x‖ ≤ (1 : ℝ) by simp [fourier_apply])
  rw [← a.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [realEmbed_ae v] with x hx
  rw [hx]
  change a (fourier (-n) x*(v x : ℂ))=a (fourier (-n) x)*v x
  rw [mul_comm]
  change a (v x • fourier (-n) x)=a (fourier (-n) x)*v x
  rw [map_smul]
  exact mul_comm _ _

theorem coordinate_integral (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (u : Physical (d := d)) :
    coordinate i a n u=∫ x : AddCircle (1 : ℝ),weight a n x*u x i ∂ν := by
  rw [coordinate,ContinuousLinearMap.comp_apply,scalar_integral]
  apply integral_congr_ae
  filter_upwards [L2EuclideanCoordinates.coordinates_ae ν u] with x hx
  exact congrArg (fun z : ℝ => weight a n x*z) (hx i)

/-- The vector Fourier coordinates have precisely the same heat decay
as the scalar proof, in the paper's analytic clock. -/
theorem coordinate_heat (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    {t : ℝ} (ht : 0 ≤ t) (u : Physical (d := d)) :
    coordinate i a n (VectorAnalyticHeat.heat t u)=
      Real.exp (-t*(n : ℝ)^2)*coordinate i a n u := by
  change NativeFourierHeatCoordinate.coordinate a n
    (VectorHeat.coordinates (VectorHeat.heat (t/NativeHeatObservation.timeScale) u) i)=_
  rw [VectorHeat.coordinate_heat]
  exact NativeFourierHeatCoordinate.coordinate_heat a n ht (VectorHeat.coordinates u i)

/-- The actual spatial test vector, rather than an abstract dual symbol. -/
def test (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Physical (d := d) :=
  ContinuousMap.toLp 2 ν ℝ
    ⟨fun x => weight a n x • EuclideanSpace.single i (1 : ℝ),
      (weight a n).continuous.smul continuous_const⟩

theorem test_ae (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    test i a n =ᵐ[ν] fun x => weight a n x • EuclideanSpace.single i (1 : ℝ) :=
  ContinuousMap.coeFn_toLp ν _

theorem test_pairing (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (u : Physical (d := d)) :
    inner ℝ (test i a n) u=coordinate i a n u := by
  rw [L2.inner_def,coordinate_integral]
  apply integral_congr_ae
  filter_upwards [test_ae i a n] with x hx
  rw [hx]
  simp only [real_inner_smul_left,EuclideanSpace.inner_single_left,conj_trivial,one_mul]

theorem adjoint_heat (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    (VectorAnalyticHeat.heat t).adjoint (test i a n)=
      Real.exp (-t*(n : ℝ)^2) • test i a n := by
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,test_pairing,coordinate_heat i a n ht,
    real_inner_smul_left,test_pairing]

/-- Countably many real and imaginary component Fourier coordinates
determine the entire original vector L2 state. -/
theorem ext {u v : Physical (d := d)}
    (hre : ∀ i n,coordinate i Complex.reCLM n u=coordinate i Complex.reCLM n v)
    (him : ∀ i n,coordinate i Complex.imCLM n u=coordinate i Complex.imCLM n v) : u=v := by
  apply VectorHeat.coordinates.injective
  apply PiLp.ext
  intro i
  exact NativeFourierStateSeparation.ext (hre i) (him i)

theorem ae_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (u v : Ω → Physical (d := d))
    (hre : ∀ i n,(fun ω => coordinate i Complex.reCLM n (u ω)) =ᵐ[μ]
      fun ω => coordinate i Complex.reCLM n (v ω))
    (him : ∀ i n,(fun ω => coordinate i Complex.imCLM n (u ω)) =ᵐ[μ]
      fun ω => coordinate i Complex.imCLM n (v ω)) : u =ᵐ[μ] v := by
  have hr := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun n => hre i n))
  have hi := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun n => him i n))
  filter_upwards [hr,hi] with ω hr hi
  exact ext hr hi

end SHEStochastic.MatrixFourierCoordinates
