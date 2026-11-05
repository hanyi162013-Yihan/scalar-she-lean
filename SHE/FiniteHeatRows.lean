module

public import SHE.NativeKernelAction
public import SHE.PhysicalMeanSemigroup
public import SHE.HeatAgeContinuity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteHeatRows
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier WordRecursion
open scoped BigOperators ENNReal
local instance finiteHeatRows_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
variable {n : ℕ}

def coefficient (D : WordRecursion.State n →L[ℝ] ℝ) (i : Fin n) : ℝ :=
  D (EuclideanSpace.basisFun (Fin n) ℝ i)

theorem apply_eq_sum (D : WordRecursion.State n →L[ℝ] ℝ) (z : WordRecursion.State n) :
    D z=∑ i : Fin n,coefficient D i*z i := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hz : (∑ i : Fin n,z i • e i)=z := by
    simpa only [e,EuclideanSpace.basisFun_repr] using e.sum_repr z
  calc
    D z=D (∑ i : Fin n,z i • e i) := congrArg D hz.symm
    _ = ∑ i : Fin n,z i*D (e i) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- The true L² kernel of a finite physical derivative row. The Gaussian
functional D and its averaging time are independent of the row time r. -/
def kernel (D : WordRecursion.State n →L[ℝ] ℝ) (Z : Fin n → Observation) (r : ℝ) : CircleL2 :=
  ∑ i : Fin n,(coefficient D i:ℂ) • circleHeat ((Z i).target-r) (Z i).center

theorem kernel_ae (D : WordRecursion.State n →L[ℝ] ℝ) (Z : Fin n → Observation)
    {r : ℝ} (hr : ∀ i,r < (Z i).target) :
    (kernel D Z r : HeatCircle → ℂ)=ᵐ[haarAddCircle]
      fun y => ((D (heatRow Z r y):ℝ):ℂ) := by
  classical
  have hs := Lp.coeFn_finsetSum Finset.univ
    (fun i => (coefficient D i:ℂ) • circleHeat ((Z i).target-r) (Z i).center)
  have hsm := ae_all_iff.mpr (fun i : Fin n => Lp.coeFn_smul (coefficient D i:ℂ)
    (circleHeat ((Z i).target-r) (Z i).center))
  have hh := ae_all_iff.mpr (fun i => ProfileVariance.heatPhysical_ae (sub_pos.mpr (hr i)) (Z i).center)
  filter_upwards [hs,hsm,hh] with y hy hsy hhy
  change (∑ i : Fin n,(coefficient D i:ℂ) • circleHeat ((Z i).target-r) (Z i).center) y=_
  rw [hy,Finset.sum_apply,apply_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [hsy i,Pi.smul_apply,←hhy i,smul_eq_mul]
  change (coefficient D i:ℂ)*ProfileVariance.heatPhysical ((Z i).target-r) (Z i).center y=
    (coefficient D i:ℂ)*(((ProfileVariance.heatPhysical ((Z i).target-r) (Z i).center y).re:ℝ):ℂ)
  rw [WordRecursion.heatPhysical_real (sub_pos.mpr (hr i))]

/-- Exact last-half (or quarter) row identity at the actual native heat
clock. It keeps the original derivative functional D unchanged. -/
theorem heat_kernel (D : WordRecursion.State n →L[ℝ] ℝ) (Z : Fin n → Observation)
    {q r : ℝ} (hqr : q ≤ r) (hr : ∀ i,r < (Z i).target) :
    circleHeatOperator (r-q) (sub_nonneg.mpr hqr) (kernel D Z r)=kernel D Z q := by
  unfold kernel
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,circleHeatOperator_heat (sub_nonneg.mpr hqr) (sub_pos.mpr (hr i))]
  congr 2
  ring

def functional (D : WordRecursion.State n →L[ℝ] ℝ) (Z : Fin n → Observation) (r : ℝ) : CircleL2 →L[ℂ] ℂ :=
  innerSL ℂ (kernel D Z r)

/-- Genuine signed-input factorization. No absolute value is inserted on
the input and no Gaussian/current time is changed. -/
theorem functional_split (D : WordRecursion.State n →L[ℝ] ℝ) (Z : Fin n → Observation)
    {q r : ℝ} (hqr : q ≤ r) (hr : ∀ i,r < (Z i).target) :
    functional D Z q=(functional D Z r).comp (circleHeatOperator (r-q) (sub_nonneg.mpr hqr)) := by
  apply ContinuousLinearMap.ext
  intro v
  change inner ℂ (kernel D Z q) v=inner ℂ (kernel D Z r) (circleHeatOperator (r-q) _ v)
  rw [←heat_kernel D Z hqr hr]
  exact circleHeatOperator_self_adjoint _ _ _ _

/-- The functional is exactly the scalar integral against the displayed
physical row kernel. -/
theorem functional_integral (D : WordRecursion.State n →L[ℝ] ℝ) (Z : Fin n → Observation)
    {r : ℝ} (hr : ∀ i,r < (Z i).target) (v : CircleL2) :
    functional D Z r v=∫ y : HeatCircle,((D (heatRow Z r y):ℝ):ℂ)*v y ∂haarAddCircle := by
  change inner ℂ (kernel D Z r) v=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernel_ae D Z hr] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,Complex.conj_ofReal]
  ring

end SHE.FiniteHeatRows
