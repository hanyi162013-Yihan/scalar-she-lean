module

public import SHE.NativeHeatObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Literal real square-summable noise rows of the physical heat
observations. Their cross inner products give the true covariance
density, including every original individual stopping mask. -/
noncomputable section
namespace SHE.NativeObservationCovariance
open MeasureTheory AddCircle CircleHeat FiniteHaar DyadicApproximation
open NativeHeatObservation WordRecursion
open scoped ENNReal
local instance nativeObservationCovariance_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeObservationCovariance_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem realInputPart_inner {x y : HaarInput} (hx : ∀ q, (x q).im=0) (hy : ∀ q,(y q).im=0) :
    inner ℝ (realInputPart x) (realInputPart y)=(inner ℂ x y).re := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,Complex.re_tsum (lp.summable_inner x y)]
  apply tsum_congr
  intro q
  change inner ℝ (x q).re (y q).re=(inner ℂ (x q) (y q)).re
  simp only [RCLike.inner_apply,conj_trivial,Complex.mul_re,Complex.conj_re,Complex.conj_im,hx q,hy q,
    neg_zero,mul_zero,sub_zero]

def row {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
    (T r : ℝ) (x : StoppedFourier.HeatCircle) : RealHaarInput :=
  realInputPart (nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2 (StoppedFourier.circleHeat (T-r) x))

theorem analysis_heat_real {ell M T r : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
    (hr : r < T) (x : StoppedFourier.HeatCircle) (q : HaarNode) :
    (nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2 (StoppedFourier.circleHeat (T-r) x) q).im=0 := by
  change (inner ℂ (globalHaarColumn q f.1)
    (CircleNormalization.push.symm (StoppedFourier.circleHeat (T-r) x))).im=0
  exact inner_real_fields_im _ _ (globalHaarColumn_real_ae q f.1 f.2.1)
    (CircleNormalization.push_symm_ae_property _ (fun z => z.im=0) (circleHeat_real_ae (sub_pos.mpr hr) x))

theorem row_cross_covariance {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
    {n : ℕ} (Z : Fin n → Observation) (r : ℝ) (i j : Fin n)
    (hi : r < (Z i).target) (hj : r < (Z j).target) :
    inner ℝ (row hell f (Z i).target r (Z i).center) (row hell f (Z j).target r (Z j).center)=
      covarianceDensity (fun p => (CircleNormalization.push f.1 p.2).re) Z r i j := by
  rw [row,row,realInputPart_inner (analysis_heat_real hell f hi _) (analysis_heat_real hell f hj _)]
  exact nativeFactorAnalysis_heat_covarianceDensity f.1 ell M hell f.2.1 f.2.2 Z r i j hi hj

def stoppedRow {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
    (Z : Observation) (r : ℝ) : RealHaarInput :=
  if r < Z.stop then row hell f Z.target r Z.center else 0

/-- Individual stopping times are visible as the two density masks.
They are not replaced by a common target or minimum target. -/
theorem stoppedRow_cross_covariance {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
    {n : ℕ} (Z : Fin n → Observation) (r : ℝ) (i j : Fin n)
    (hi : (Z i).stop ≤ (Z i).target) (hj : (Z j).stop ≤ (Z j).target) :
    inner ℝ (stoppedRow hell f (Z i) r) (stoppedRow hell f (Z j) r)=
      if r < (Z i).stop ∧ r < (Z j).stop then
        covarianceDensity (fun p => (CircleNormalization.push f.1 p.2).re) Z r i j else 0 := by
  classical
  by_cases hri : r < (Z i).stop <;> by_cases hrj : r < (Z j).stop
  · simp only [stoppedRow,hri,hrj,and_self,ite_true]
    exact row_cross_covariance hell f Z r i j (hri.trans_le hi) (hrj.trans_le hj)
  · simp [stoppedRow,hri,hrj]
  · simp [stoppedRow,hri,hrj]
  · simp [stoppedRow,hri,hrj]

end SHE.NativeObservationCovariance
