module

public import SHEStochastic.FiniteStateDriverCoordinates
public import SHEStochastic.BoundedFourierCylinderGenerator
public import SHEStochastic.StateDriverCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.JointFourierCylinderGenerator
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle GaussianItoTest
open NativeFourierHeatCoordinate FiniteStateDriverCoordinates FourierCylinderGenerator
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B)
  {s d : ℕ} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  (b : Fin d → Lp V 2 (haarAddCircle (T := 2 * Real.pi)))

def cross (i : Fin s) (j : Fin d) : BoundedContinuousFunction RealL2 ℝ :=
  (StateDriverCovariance.bounded haarAddCircle hβ hβ1 hG (weight (a i) (n i)) (b j) B hB hb).compContinuous
    ⟨NativePhysicalState.push, NativePhysicalState.push.continuous⟩

/-- The full joint covariance has state/state, state/driver and
driver/driver entries. The driver directions may repeat or be correlated. -/
def covariance (i j : Fin (s + d)) : BoundedContinuousFunction RealL2 ℝ :=
  Fin.addCases
    (fun k ↦ Fin.addCases
      (fun l ↦ BoundedFourierCylinderGenerator.covariance hG hβ hβ1 B hB hb a n k l)
      (fun l ↦ cross hG hβ hβ1 B hB hb a n b k l) j)
    (fun k ↦ Fin.addCases
      (fun l ↦ cross hG hβ hβ1 B hB hb a n b l k)
      (fun l ↦ BoundedContinuousFunction.const RealL2 (inner ℝ (b k) (b l))) j) i

def rows (u : RealL2) : Fin (s + d) → Lp V 2 (haarAddCircle (T := 2 * Real.pi)) :=
  Fin.addCases (fun i ↦ StateNoiseCovariance.row haarAddCircle hβ hβ1 hG
    (weight (a i) (n i)) (NativePhysicalState.push u)) b

theorem covariance_apply (u : RealL2) (i j : Fin (s + d)) :
    covariance hG hβ hβ1 B hB hb a n b i j u =
      inner ℝ (rows hG hβ hβ1 a n b u i) (rows hG hβ hβ1 a n b u j) := by
  refine Fin.addCases ?_ ?_ i
  · intro k
    refine Fin.addCases ?_ ?_ j
    · intro l
      simp only [covariance, rows, Fin.addCases_left]
      rfl
    · intro l
      simp only [covariance, rows, Fin.addCases_left, Fin.addCases_right]
      rfl
  · intro k
    refine Fin.addCases ?_ ?_ j
    · intro l
      simp only [covariance, rows, Fin.addCases_left, Fin.addCases_right]
      change inner ℝ (StateNoiseCovariance.row haarAddCircle hβ hβ1 hG
        (weight (a l) (n l)) (NativePhysicalState.push u)) (b k) =
          inner ℝ (b k) (StateNoiseCovariance.row haarAddCircle hβ hβ1 hG
            (weight (a l) (n l)) (NativePhysicalState.push u))
      exact real_inner_comm _ _
    · intro l
      simp only [covariance, rows, Fin.addCases_right]
      rfl

variable {ι : Type*} (driver : Fin d → ι)
  (f : State (s + d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)

def test : BoundedContinuousFunction (RealL2 × (ι → ℝ)) ℝ :=
  (_root_.ofCompactSupport f hf.continuous hs).compContinuous (projectionMap a n driver)

/-- The literal joint generator is defined without global boundedness
of the coefficient. Boundedness is used only to bundle its cutoff. -/
def value (q : RealL2 × (ι → ℝ)) : ℝ :=
  heatDrift f hf hs (frequencies (d := d) n) (projection a n driver q) +
    (1 / 2 : ℝ) * ∑ i : Fin (s + d), ∑ j : Fin (s + d),
      inner ℝ (rows hG hβ hβ1 a n b q.1 i) (rows hG hβ hβ1 a n b q.1 j) *
        GaussianTaylor.hessian f (projection a n driver q)
          (EuclideanSpace.basisFun (Fin (s + d)) ℝ i) (EuclideanSpace.basisFun (Fin (s + d)) ℝ j)

theorem continuous_value : Continuous (value hG hβ hβ1 a n b driver f hf hs) := by
  have hr (i : Fin (s + d)) : Continuous (fun q : RealL2 × (ι → ℝ) ↦ rows hG hβ hβ1 a n b q.1 i) := by
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp only [rows, Fin.addCases_left]
      exact (StateNoiseCovariance.row_continuous haarAddCircle hβ hβ1 hG (weight (a k) (n k))).comp
        (NativePhysicalState.push.continuous.comp continuous_fst)
    · intro k
      simp only [rows, Fin.addCases_right]
      exact continuous_const
  apply Continuous.add
  · exact (heatDrift f hf hs (frequencies (d := d) n)).continuous.comp
      (FiniteStateDriverCoordinates.continuous_projection a n driver)
  · apply Continuous.const_mul
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact ((hr i).inner (hr j)).mul ((hessianEntry f hf hs i j).continuous.comp
      (FiniteStateDriverCoordinates.continuous_projection a n driver))

/-- The bounded joint cylinder generator retains the cross brackets
needed to identify the state equation with its actual Brownian driver. -/
def generator : BoundedContinuousFunction (RealL2 × (ι → ℝ)) ℝ :=
  (heatDrift f hf hs (frequencies (d := d) n)).compContinuous (projectionMap a n driver) +
    (1 / 2 : ℝ) • ∑ i : Fin (s + d), ∑ j : Fin (s + d),
      (covariance hG hβ hβ1 B hB hb a n b i j).compContinuous ContinuousMap.fst *
        (hessianEntry f hf hs i j).compContinuous (projectionMap a n driver)

theorem generator_apply (q : RealL2 × (ι → ℝ)) :
    generator hG hβ hβ1 B hB hb a n b driver f hf hs q =
      heatDrift f hf hs (frequencies (d := d) n) (projection a n driver q) +
        (1 / 2 : ℝ) * ∑ i : Fin (s + d), ∑ j : Fin (s + d),
          inner ℝ (rows hG hβ hβ1 a n b q.1 i) (rows hG hβ hβ1 a n b q.1 j) *
            GaussianTaylor.hessian f (projection a n driver q)
              (EuclideanSpace.basisFun (Fin (s + d)) ℝ i)
              (EuclideanSpace.basisFun (Fin (s + d)) ℝ j) := by
  change (BoundedContinuousFunction.evalCLM ℝ q) (generator hG hβ hβ1 B hB hb a n b driver f hf hs) = _
  simp only [generator, map_add, map_smul, map_sum, BoundedContinuousFunction.evalCLM_apply,
    BoundedContinuousFunction.mul_apply, smul_eq_mul, BoundedContinuousFunction.compContinuous_apply,
    covariance_apply]
  rfl

theorem generator_value (q : RealL2 × (ι → ℝ)) :
    generator hG hβ hβ1 B hB hb a n b driver f hf hs q = value hG hβ hβ1 a n b driver f hf hs q :=
  generator_apply hG hβ hβ1 B hB hb a n b driver f hf hs q

theorem coe_generator : (generator hG hβ hβ1 B hB hb a n b driver f hf hs : RealL2 × (ι → ℝ) → ℝ) =
    value hG hβ hβ1 a n b driver f hf hs :=
  funext (generator_value hG hβ hβ1 B hB hb a n b driver f hf hs)

def cutoff (R : ℝ≥0) : BoundedContinuousFunction (RealL2 × (ι → ℝ)) ℝ :=
  generator (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
    (‖G 0‖ + (C : ℝ) * (R : ℝ) ^ (β : ℝ)) (by positivity)
    (UnboundedCoefficientCutoff.bounded hG R) a n b driver f hf hs

theorem rows_cutoff_agrees (R : ℝ≥0) (u : RealL2)
    (hu : ∀ᵐ x ∂haarAddCircle, ‖NativePhysicalState.push u x‖ ≤ R) :
    rows (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 a n b u = rows hG hβ hβ1 a n b u := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [rows, Fin.addCases_left]
    exact StateNoiseCovariance.row_congr haarAddCircle hβ hβ1
      (UnboundedCoefficientCutoff.holder hG R) hG (weight (a j) (n j)) (NativePhysicalState.push u)
        (hu.mono fun _ hx ↦ UnboundedCoefficientCutoff.agrees G R hx)
  · intro j
    simp only [rows, Fin.addCases_right]

/-- State, mixed and pure-driver generator entries all agree with the
original equation before the same uniform coefficient exit. -/
theorem cutoff_agrees (R : ℝ≥0) (q : RealL2 × (ι → ℝ))
    (hq : ∀ᵐ x ∂haarAddCircle, ‖NativePhysicalState.push q.1 x‖ ≤ R) :
    cutoff hG hβ hβ1 a n b driver f hf hs R q = value hG hβ hβ1 a n b driver f hf hs q := by
  rw [cutoff, generator_value]
  simp only [value, rows_cutoff_agrees hG hβ hβ1 a n b R q.1 hq]

variable {Gn : ℕ → ℝ → V} {Cn : ℕ → ℝ≥0}
  (hGn : ∀ k, HolderWith (Cn k) β (Gn k)) (hbn : ∀ k z, ‖Gn k z‖ ≤ B)

theorem uniform_cross_limit (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z - Gn k z‖ ≤ δ k) (i : Fin s) (j : Fin d) :
    Filter.Tendsto (fun k ↦ cross (hGn k) hβ hβ1 B hB (hbn k) a n b i j)
      Filter.atTop (𝓝 (cross hG hβ hβ1 B hB hb a n b i j)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbnd (k : ℕ) : ‖cross hG hβ hβ1 B hB hb a n b i j -
      cross (hGn k) hβ hβ1 B hB (hbn k) a n b i j‖ ≤
        ‖weight (a i) (n i)‖ * δ k * ‖b j‖ := by
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (mul_nonneg (norm_nonneg _) (hδ k)) (norm_nonneg _))).mpr
    intro u
    exact StateDriverCovariance.difference haarAddCircle hβ hβ1 hG (hGn k)
      (weight (a i) (n i)) (b j) (δ k) (hδ k) (hclose k) (NativePhysicalState.push u)
  have hn := squeeze_zero (fun k ↦ norm_nonneg _) hbnd
    (by simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hδlim).mul_const ‖b j‖)
  simpa only [norm_sub_rev] using hn

theorem uniform_covariance_limit (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z - Gn k z‖ ≤ δ k) (i j : Fin (s + d)) :
    Filter.Tendsto (fun k ↦ covariance (hGn k) hβ hβ1 B hB (hbn k) a n b i j)
      Filter.atTop (𝓝 (covariance hG hβ hβ1 B hB hb a n b i j)) := by
  refine Fin.addCases ?_ ?_ i
  · intro l
    refine Fin.addCases ?_ ?_ j
    · intro m
      simp only [covariance, Fin.addCases_left]
      exact BoundedFourierCylinderGenerator.uniform_covariance_limit hG hβ hβ1 B hB hb a n
        hGn hbn δ hδ hδlim hclose l m
    · intro m
      simp only [covariance, Fin.addCases_left, Fin.addCases_right]
      exact uniform_cross_limit hG hβ hβ1 B hB hb a n b hGn hbn δ hδ hδlim hclose l m
  · intro l
    refine Fin.addCases ?_ ?_ j
    · intro m
      simp only [covariance, Fin.addCases_left, Fin.addCases_right]
      exact uniform_cross_limit hG hβ hβ1 B hB hb a n b hGn hbn δ hδ hδlim hclose m l
    · intro m
      simp only [covariance, Fin.addCases_right]
      exact tendsto_const_nhds

/-- Joint generators converge uniformly, including the mixed brackets;
the approximation requires only a common coefficient bound and uniform
coefficient convergence, with no common smoothness seminorm. -/
theorem uniform_generator_limit (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z - Gn k z‖ ≤ δ k) :
    Filter.Tendsto (fun k ↦
      ‖generator hG hβ hβ1 B hB hb a n b driver f hf hs -
        generator (hGn k) hβ hβ1 B hB (hbn k) a n b driver f hf hs‖)
      Filter.atTop (𝓝 0) := by
  have hc := uniform_covariance_limit hG hβ hβ1 B hB hb a n b hGn hbn δ hδ hδlim hclose
  have hg : Filter.Tendsto
      (fun k ↦ generator (hGn k) hβ hβ1 B hB (hbn k) a n b driver f hf hs)
      Filter.atTop (𝓝 (generator hG hβ hβ1 B hB hb a n b driver f hf hs)) := by
    unfold generator
    apply tendsto_const_nhds.add
    apply Filter.Tendsto.const_smul
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (((BoundedContinuousFunction.continuous_compContinuous
      (ContinuousMap.fst : C(RealL2 × (ι → ℝ), RealL2))).tendsto _).comp
        (hc i j)).mul tendsto_const_nhds
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hg
  simpa only [norm_sub_rev] using hn

end SHEStochastic.JointFourierCylinderGenerator
