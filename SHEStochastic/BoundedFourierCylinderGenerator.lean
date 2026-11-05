module

public import SHEStochastic.FourierCylinderGenerator
public import SHEStochastic.StateNoiseCovarianceStability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.BoundedFourierCylinderGenerator
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open GaussianItoTest NativeFourierHeatCoordinate FourierCylinderGenerator
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B)
  {d : ℕ} (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)

/-- A bounded coefficient needs no further state truncation. This is
the original canonical covariance, bundled as a bounded function. -/
def covariance (i j : Fin d) : BoundedContinuousFunction RealL2 ℝ :=
  (StateNoiseCovariance.bounded haarAddCircle hβ hβ1 hG hG
    (weight (a i) (n i)) (weight (a j) (n j)) B B hB hB hb hb).compContinuous
      ⟨NativePhysicalState.push, NativePhysicalState.push.continuous⟩

def generator (f : State d → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    BoundedContinuousFunction RealL2 ℝ :=
  (∑ i : Fin d, (driftComponent f hf hs n i).compContinuous (projectionMap a n)) +
    (1 / 2 : ℝ) • ∑ i : Fin d, ∑ j : Fin d,
      covariance hG hβ hβ1 B hB hb a n i j *
        (hessianEntry f hf hs i j).compContinuous (projectionMap a n)

theorem generator_apply (f : State d → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (u : RealL2) : generator hG hβ hβ1 B hB hb a n f hf hs u =
      FourierCylinderGenerator.value f hG hβ hβ1 a n u := by
  change (BoundedContinuousFunction.evalCLM ℝ u) (generator hG hβ hβ1 B hB hb a n f hf hs) = _
  simp only [generator, map_add, map_smul, map_sum, BoundedContinuousFunction.evalCLM_apply,
    BoundedContinuousFunction.mul_apply, smul_eq_mul]
  rfl

variable {K : ℝ → V} {D : ℝ≥0} (hK : HolderWith D β K)
  (hbK : ∀ z, ‖K z‖ ≤ B)

theorem covariance_difference (i j : Fin d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ z, ‖G z - K z‖ ≤ δ) :
    ‖covariance hG hβ hβ1 B hB hb a n i j - covariance hK hβ hβ1 B hB hbK a n i j‖ ≤
      ‖weight (a i) (n i)‖ * ‖weight (a j) (n j)‖ * (B + B) * δ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro u
  exact StateNoiseCovarianceStability.value_difference haarAddCircle hβ hβ1 hG hK
    (weight (a i) (n i)) (weight (a j) (n j)) B B δ hB hB hδ hb hbK hclose
    (NativePhysicalState.push u)

variable {Gn : ℕ → ℝ → V} {Cn : ℕ → ℝ≥0}
  (hGn : ∀ k, HolderWith (Cn k) β (Gn k)) (hbn : ∀ k z, ‖Gn k z‖ ≤ B)

theorem uniform_covariance_limit (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z - Gn k z‖ ≤ δ k) (i j : Fin d) :
    Filter.Tendsto (fun k ↦ covariance (hGn k) hβ hβ1 B hB (hbn k) a n i j)
      Filter.atTop (𝓝 (covariance hG hβ hβ1 B hB hb a n i j)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := squeeze_zero (fun k ↦ norm_nonneg _)
    (fun k ↦ covariance_difference hG hβ hβ1 B hB hb a n (hGn k) (hbn k) i j
      (δ k) (hδ k) (hclose k))
    (by simpa only [mul_zero] using tendsto_const_nhds.mul hδlim)
  simpa only [norm_sub_rev] using hn

/-- Uniform coefficient approximation gives uniform convergence of the
bounded canonical generators. Heat drift and mixed Hessian entries are
reused unchanged; no extra differentiability of the coefficient is used. -/
theorem uniform_generator_limit (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (hδlim : Filter.Tendsto δ Filter.atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z - Gn k z‖ ≤ δ k)
    (f : State d → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Filter.Tendsto (fun k ↦
      ‖generator hG hβ hβ1 B hB hb a n f hf hs -
        generator (hGn k) hβ hβ1 B hB (hbn k) a n f hf hs‖)
      Filter.atTop (𝓝 0) := by
  have hc := uniform_covariance_limit hG hβ hβ1 B hB hb a n hGn hbn δ hδ hδlim hclose
  have hg : Filter.Tendsto
      (fun k ↦ generator (hGn k) hβ hβ1 B hB (hbn k) a n f hf hs)
      Filter.atTop (𝓝 (generator hG hβ hβ1 B hB hb a n f hf hs)) := by
    unfold generator
    apply tendsto_const_nhds.add
    apply Filter.Tendsto.const_smul
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact (hc i j).mul tendsto_const_nhds
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hg
  simpa only [norm_sub_rev] using hn

end SHEStochastic.BoundedFourierCylinderGenerator
