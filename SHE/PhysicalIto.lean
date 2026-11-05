module

public import SHE.PhysicalInsertion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Physical one-step word recursion from the ordinary, un-cancelled
finite-dimensional Itô formula. All Gaussian analytic inputs are proved. -/
noncomputable section
namespace SHE.PhysicalIto
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier
open GaussianTaylorAverage GaussianConvolution GaussianItoTest
open WordRecursion CovarianceMatrix CovarianceEndpoint PhysicalInsertion

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev State (n : ℕ) := WordRecursion.State n

/-- The sole stochastic input in this module: the standard finite-
dimensional Itô formula with its original time derivative and covariance
bracket. It is universally quantified over regular deterministic tests;
it does not assume cancellation or an operator-word identity. -/
def FiniteItoInput {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (Y : Ω → ℝ → State n) (Γ : Ω → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (a b : ℝ) (N : (ℝ → State n → ℝ) → Ω → ℝ) : Prop :=
  ∀ G dG, RegularTest a b G dG → ∀ᵐ ω ∂μ,
    G b (Y ω b) = G a (Y ω a) + N G ω +
      ∫ t in a..b, dG t (Y ω t) + (1 / 2 : ℝ) *
        covarianceAction (Γ ω t) (GaussianTaylor.hessian (G t) (Y ω t))

def insertedWord {n : ℕ} (W : EndpointWindow n) (a : ℝ → ℝ)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) (F : State n → ℝ)
    (t : ℝ) (x : HeatCircle) : ℝ :=
  insertion a W.coefficient W.observations t x (backward W F t)
    (observe U X (appendObservation W.observations t x) t)

def wordRemainder {n : ℕ} (W : EndpointWindow n) (a : ℝ → ℝ)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) (F : State n → ℝ) : ℝ :=
  ∫ t in W.left..W.right, ∫ x : HeatCircle, insertedWord W a U X F t x ∂haarAddCircle

theorem backward_eq_semigroup {n : ℕ} (W : EndpointWindow n) (F : State n → ℝ)
    {t : ℝ} (ht : t ∈ Icc W.left W.right) :
    backward W F t = gaussianSemigroup W.coefficient W.observations t W.right F := by
  unfold backward
  rw [W.path_eq ht]
  rfl

theorem backward_terminal {n : ℕ} (W : EndpointWindow n) (F : State n → ℝ) :
    backward W F W.right = F := by
  rw [backward_eq_semigroup W F ⟨W.ordered, le_rfl⟩]
  funext z
  exact gaussianSemigroup_terminal _ _ _ _ _

/-- An exact physical operator insertion after applying Itô to the proved
backward test. The most recent observation has target equal to the node
time; no positive terminal heat gap or covariance inverse is required. -/
theorem physical_one_step {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (W : EndpointWindow n) (a : ℝ → ℝ) (ha : Measurable a)
    (U : Ω → ℝ → CircleL2) (X : Ω → ℝ × HeatCircle → ℝ)
    (hX : ∀ᵐ ω ∂μ, Measurable (X ω)) {A : ℝ} (hA : 0 ≤ A) (habound : ∀ z, |a z| ≤ A)
    (N : (ℝ → State n → ℝ) → Ω → ℝ)
    (hIto : FiniteItoInput μ (fun ω => observe (U ω) (X ω) W.observations)
      (fun ω t => densityMatrix (fun p => a (X ω p)) W.observations t) W.left W.right N)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖GaussianTaylor.hessian F w - GaussianTaylor.hessian F z‖ ≤ K * ‖w - z‖) :
    ∀ᵐ ω ∂μ, F (observe (U ω) (X ω) W.observations W.right) =
      gaussianSemigroup W.coefficient W.observations W.left W.right F
        (observe (U ω) (X ω) W.observations W.left) + N (backward W F) ω +
          wordRemainder W a (U ω) (X ω) F := by
  have hreg := backward_regular W hF hbound hD hDD hB hK hH
  filter_upwards [hIto _ _ hreg, hX] with ω hω hXω
  rw [backward_terminal W F] at hω
  rw [backward_eq_semigroup W F ⟨le_rfl, W.ordered⟩] at hω
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le W.ordered
  intro t ht
  exact insertion_generator W a ha (U ω) (X ω) hXω hA habound ht

/-- A genuinely stopped observation. It equals the evolving heat cylinder
only before its own original stopping time. -/
def stoppedObserve {n : ℕ} (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (t : ℝ) : State n :=
  WithLp.toLp 2 (fun i =>
    let r := min t (Z i).stop
    if r < (Z i).target then PhysicalProfile.physicalHeatMean (U r) ((Z i).target - r, (Z i).center)
    else X (r, (Z i).center))

theorem stoppedObserve_eq {n : ℕ} (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) {t : ℝ} (ht : ∀ i, t ≤ (Z i).stop) :
    stoppedObserve U X Z t = observe U X Z t := by
  ext i
  change (if min t (Z i).stop < (Z i).target then
      PhysicalProfile.physicalHeatMean (U (min t (Z i).stop))
        ((Z i).target - min t (Z i).stop, (Z i).center)
    else X (min t (Z i).stop, (Z i).center)) = _
  rw [min_eq_left (ht i)]
  rfl

end SHE.PhysicalIto
