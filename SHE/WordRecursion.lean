module

public import SHE.CanonicalProfile
public import SHE.Algebra
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section
set_option autoImplicit false

/-! Concrete physical observation cylinders and exact covariance insertions.
The stochastic Itô input and the deterministic Gaussian backward equation
are distinguished explicitly in the one-step results. -/
noncomputable section
namespace SHE.WordRecursion
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier ProfileVariance PhysicalProfile

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure Observation where
  stop : ℝ
  target : ℝ
  center : HeatCircle

def appendObservation {n : ℕ} (Z : Fin n → Observation) (t : ℝ) (x : HeatCircle) :
    Fin (n + 1) → Observation := Fin.cases ⟨t, t, x⟩ Z

/-- The physical heat row, with its original target time. -/
def heatRow {n : ℕ} (Z : Fin n → Observation) (t : ℝ) (x : HeatCircle) : State n :=
  WithLp.toLp 2 (fun i => (heatPhysical ((Z i).target - t) (Z i).center x).re)

theorem heatCrossKernel_symm (t : ℝ) (x y : HeatCircle) : heatCrossKernel t x y = heatCrossKernel t y x := by
  unfold heatCrossKernel
  calc
    _ = ∑' n : ℤ, (Real.exp (-t * ((-n : ℤ) : ℝ) ^ 2) : ℂ) * fourier (-n) x * fourier (-(-n)) y :=
      ((Equiv.neg ℤ).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [Int.cast_neg, neg_sq, neg_neg]
      ring

theorem heatPhysical_real {t : ℝ} (ht : 0 < t) (x y : HeatCircle) :
    ((heatPhysical t x y).re : ℂ) = heatPhysical t x y := by
  have hh : 0 < t / 2 := by positivity
  have hxy := circleHeat_cross_gram hh hh y x
  have hyx := circleHeat_cross_gram hh hh x y
  simp only [show t / 2 + t / 2 = t by ring] at hxy hyx
  apply RCLike.conj_eq_iff_re.mp
  change (starRingEnd ℂ) (heatCrossKernel t y x) = heatCrossKernel t y x
  calc
    _ = (starRingEnd ℂ) (inner ℂ (circleHeat (t / 2) y) (circleHeat (t / 2) x)) := by rw [hxy]
    _ = inner ℂ (circleHeat (t / 2) x) (circleHeat (t / 2) y) := inner_conj_symm _ _
    _ = heatCrossKernel t x y := hyx
    _ = _ := heatCrossKernel_symm t x y

theorem heatPhysical_re_sq {t : ℝ} (ht : 0 < t) (x y : HeatCircle) :
    (heatPhysical t x y).re ^ 2 = ‖heatPhysical t x y‖ ^ 2 := by
  have he := congrArg (fun z : ℂ => ‖z‖ ^ 2) (heatPhysical_real ht x y)
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using he

theorem heatPhysical_re_bound {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (x y : HeatCircle) :
    |(heatPhysical t x y).re| ≤ 1 + heatConstant * (δ / 2) ^ (-(1 / 2 : ℝ)) := by
  have ht : 0 < t := hδ.trans_le hδt
  have hh : 0 < t / 2 := by positivity
  have he := circleHeat_cross_gram hh hh y x
  simp only [show t / 2 + t / 2 = t by ring] at he
  have hc (z : HeatCircle) : ‖circleHeat (t / 2) z‖ = ‖circleHeat (t / 2) (0 : HeatCircle)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (circleHeat_norm_sq_center _ z 0)
  have hi := norm_inner_le_norm (𝕜 := ℂ) (circleHeat (t / 2) y) (circleHeat (t / 2) x)
  rw [he, hc x, hc y, ← pow_two] at hi
  have hp : (t / 2) ^ (-(1 / 2 : ℝ)) ≤ (δ / 2) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hb : ‖circleHeat (t / 2) (0 : HeatCircle)‖ ^ 2 ≤
      1 + heatConstant * (δ / 2) ^ (-(1 / 2 : ℝ)) :=
    (circleHeat_norm_sq_bound hh 0).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hp heatConstant_pos.le))
  exact (Complex.abs_re_le_norm _).trans (hi.trans hb)

/-- Actual backward heat observations; at terminal age zero the original
physical state version is retained explicitly. -/
def observe {n : ℕ} (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (t : ℝ) : State n :=
  WithLp.toLp 2 (fun i => if t < (Z i).target then
    physicalHeatMean (U t) ((Z i).target - t, (Z i).center) else X (t, (Z i).center))

theorem observe_append_zero {n : ℕ} (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (t : ℝ) (x : HeatCircle) :
    observe U X (appendObservation Z t x) t 0 = X (t, x) := by
  simp [observe, appendObservation]

theorem observe_append_succ {n : ℕ} (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (t : ℝ) (x : HeatCircle) (i : Fin n) :
    observe U X (appendObservation Z t x) t i.succ = observe U X Z t i := by
  rfl

def covarianceDensity {n : ℕ} (c : ℝ × HeatCircle → ℝ) (Z : Fin n → Observation)
    (t : ℝ) (i j : Fin n) : ℝ :=
  ∫ x : HeatCircle, c (t, x) * heatRow Z t x i * heatRow Z t x j ∂haarAddCircle

def covariance {n : ℕ} (c : ℝ × HeatCircle → ℝ) (Z : Fin n → Observation)
    (q s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ t in q..s, covarianceDensity c Z t i j

/-- The reference convolution is an actual finite-dimensional Gaussian law.
Its positive covariance and backward derivative are separate obligations. -/
def gaussianSemigroup {n : ℕ} (c : ℝ × HeatCircle → ℝ) (Z : Fin n → Observation)
    (q s : ℝ) (F : State n → ℝ) (z : State n) : ℝ :=
  ∫ y : State n, F (z + y) ∂multivariateGaussian 0 (covariance c Z q s)

def hessian {n : ℕ} (F : State n → ℝ) (z : State n) : State n →L[ℝ] State n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ F) z

def directionalSecond {n : ℕ} (F : State n → ℝ) (z q : State n) : ℝ := hessian F z q q

theorem bilinear_mixed_pairs {n : ℕ} (H : State n →L[ℝ] State n →L[ℝ] ℝ) (q : State n) :
    H q q = ∑ i : Fin n, ∑ j : Fin n,
      q i * q j * H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hq : (∑ i : Fin n, q i • EuclideanSpace.basisFun (Fin n) ℝ i) = q := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr q
  calc
    _ = H (∑ i : Fin n, q i • EuclideanSpace.basisFun (Fin n) ℝ i)
        (∑ j : Fin n, q j • EuclideanSpace.basisFun (Fin n) ℝ j) := by rw [hq]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The covariance insertion includes every diagonal and mixed observation
pair and appends the actual new physical observation. -/
def insertion {n : ℕ} (a : ℝ → ℝ) (c : ℝ × HeatCircle → ℝ) (Z : Fin n → Observation)
    (t : ℝ) (x : HeatCircle) (F : State n → ℝ) (z : State (n + 1)) : ℝ :=
  (1 / 2 : ℝ) * (a (z 0) - c (t, x)) *
    directionalSecond F (WithLp.toLp 2 (fun i => z i.succ)) (heatRow Z t x)

theorem insertion_observe {n : ℕ} (a : ℝ → ℝ) (c : ℝ × HeatCircle → ℝ)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) (Z : Fin n → Observation)
    (t : ℝ) (x : HeatCircle) (F : State n → ℝ) :
    insertion a c Z t x F (observe U X (appendObservation Z t x) t) =
      (1 / 2 : ℝ) * (a (X (t, x)) - c (t, x)) * directionalSecond F (observe U X Z t) (heatRow Z t x) := by
  rw [insertion, observe_append_zero]
  have he : WithLp.toLp 2 (fun i => observe U X (appendObservation Z t x) t i.succ) = observe U X Z t := by
    ext i
    exact observe_append_succ U X Z t x i
  rw [he]

end SHE.WordRecursion
