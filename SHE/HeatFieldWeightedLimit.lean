module

public import SHE.HeatFieldApproximation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.HeatFieldWeightedLimit
open Set MeasureTheory AddCircle StoppedFourier NativeHeatObservation Filter Topology
open DyadicApproximation HeatFieldApproximation
local instance heatFieldWeightedLimit_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance heatFieldWeightedLimit_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance heatFieldWeightedLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatFieldWeightedLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatFieldWeightedLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

variable {P : Type*} [MeasurableSpace P] (U : P → RealL2) (hU : Measurable U)
variable (A : ℝ → ℝ) (hA : Measurable A) (D : P × HeatCircle → ℝ) (hD : Measurable D)

def difference (ε : ℝ) (p : P × HeatCircle) : ℝ :=
  A (PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε,p.2))-
    A (PredictableScalarField.nativeField U p)

include hU hA in
theorem difference_measurable (ε : ℝ) : Measurable (difference U A ε) := by
  have hp : Measurable (fun p : P × HeatCircle => (embed (U p.1),(ε,p.2))) :=
    (((embed.continuous.measurable.comp hU).comp measurable_fst).prodMk
      ((measurable_const (a := ε)).prodMk measurable_snd))
  have hm := PhysicalProfile.physicalHeatMean_joint_measurable.comp hp
  exact (hA.comp hm).sub (hA.comp (PredictableScalarField.nativeField_measurable hU))

def mass (ε : ℝ) (p : P) : ℝ :=
  ∫ x : HeatCircle,|difference U A ε (p,x)*D (p,x)| ∂haarAddCircle

include hU hA hD in
theorem mass_measurable (ε : ℝ) : Measurable (mass U A D ε) :=
  (((difference_measurable U hU A hA ε).mul hD).norm.stronglyMeasurable.integral_prod_right').measurable

theorem mass_nonneg (ε : ℝ) (p : P) : 0 ≤ mass U A D ε p := integral_nonneg (fun _ => abs_nonneg _)

theorem mass_bound {M C : ℝ} (hM : ∀ z,|A z| ≤ M) (hC : 0 ≤ C)
    (hDb : ∀ p,|D p| ≤ C) (ε : ℝ) (p : P) : mass U A D ε p ≤ 2*M*C := by
  have hh := norm_integral_le_of_norm_le_const (μ := haarAddCircle)
    (f := fun x : HeatCircle => |difference U A ε (p,x)*D (p,x)|)
    (C := 2*M*C) (Filter.Eventually.of_forall (fun x => by
      change abs (abs (difference U A ε (p,x)*D (p,x))) ≤ 2*M*C
      rw [abs_abs,abs_mul]
      apply mul_le_mul _ (hDb _) (abs_nonneg _) (by have hh:=hM 0; nlinarith [abs_nonneg (A 0)])
      exact (abs_sub _ _).trans ((add_le_add (hM _) (hM _)).trans_eq (by ring))))
  change ‖mass U A D ε p‖ ≤ (2*M*C)*haarAddCircle.real univ at hh
  simpa [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg U A D ε p)] using hh

include hU hA in
theorem mass_le_error {M C : ℝ} (hM : ∀ z,|A z| ≤ M) (hC : 0 ≤ C)
    (hDb : ∀ p,|D p| ≤ C) (ε : ℝ) (p : P) :
    mass U A D ε p ≤ C*HeatFieldApproximation.error U p A ε := by
  have hd := (difference_measurable U hU A hA ε).comp ((measurable_const (a := p)).prodMk measurable_id)
  have hi : Integrable (fun x : HeatCircle => |difference U A ε (p,x)|) haarAddCircle := by
    apply (integrable_const (2*M)).mono' hd.norm.aestronglyMeasurable
    filter_upwards with x
    change abs (abs (difference U A ε (p,x))) ≤ 2*M
    rw [abs_abs]
    exact (abs_sub _ _).trans ((add_le_add (hM _) (hM _)).trans_eq (by ring))
  have hh := norm_integral_le_of_norm_le (hi.const_mul C)
    (f := fun x : HeatCircle => |difference U A ε (p,x)*D (p,x)|)
    (Filter.Eventually.of_forall (fun x => by
      change abs (abs (difference U A ε (p,x)*D (p,x))) ≤ C*|difference U A ε (p,x)|
      rw [abs_abs,abs_mul]
      exact (mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)).trans_eq (by ring)))
  rw [integral_const_mul] at hh
  change ‖mass U A D ε p‖ ≤ C*HeatFieldApproximation.error U p A ε at hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg U A D ε p)] using hh

include hU hA in
theorem mass_tendsto_zero {M C L : ℝ} (hM : ∀ z,|A z| ≤ M) (hC : 0 ≤ C)
    (hDb : ∀ p,|D p| ≤ C) (hL : 0 ≤ L) (hLip : ∀ z w,|A z-A w| ≤ L*|z-w|) (p : P) :
    Tendsto (fun ε => mass U A D ε p) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have he := (tendsto_const_nhds (x := C)).mul (error_tendsto_zero U p hM hL hLip)
  simp only [mul_zero] at he
  exact squeeze_zero' (Filter.Eventually.of_forall (fun ε => mass_nonneg U A D ε p))
    (Filter.Eventually.of_forall (fun ε => mass_le_error U hU A hA D hM hC hDb ε p)) he

include hU hA hD in
/-- A true integrated spatial regularization limit for any fixed bounded
Borel weight and any finite parameter measure. No finite-energy bound
on the state is required, because the coefficient itself is bounded. -/
theorem integrated_mass_tendsto_zero (ν : Measure P) [IsFiniteMeasure ν]
    {M C L : ℝ} (hM : ∀ z,|A z| ≤ M) (hC : 0 ≤ C) (hDb : ∀ p,|D p| ≤ C)
    (hL : 0 ≤ L) (hLip : ∀ z w,|A z-A w| ≤ L*|z-w|) :
    Tendsto (fun ε => ∫ p,mass U A D ε p ∂ν) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := ν) (fun _ : P => 2*M*C)
    (Filter.Eventually.of_forall (fun ε => (mass_measurable U hU A hA D hD ε).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg U A D ε p)]
      exact mass_bound U A D hM hC hDb ε p))) (integrable_const _)
    (Filter.Eventually.of_forall (fun p => mass_tendsto_zero U hU A hA D hM hC hDb hL hLip p))
  simpa only [integral_zero] using ht

end SHE.HeatFieldWeightedLimit
