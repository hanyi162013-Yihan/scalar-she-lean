module

public import SHEStochastic.ScalarFourierL1Separation
public import SHEStochastic.StateNoiseCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarNoiseRowSeparation
open MeasureTheory Set SHE SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "w" => NativeFourierHeatCoordinate.weight

/-- Nondegeneracy lets the original scalar noise rows separate every
L² noise direction, including when the diffusion is unbounded. -/
theorem eq_zero {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
    (h₀ : ∀ x,g x≠0) (u v : Noise)
    (hre : ∀ n,inner ℝ (StateNoiseCovariance.row ν hβ hβ₁ hg (w Complex.reCLM n) u) v=0)
    (him : ∀ n,inner ℝ (StateNoiseCovariance.row ν hβ hβ₁ hg (w Complex.imCLM n) u) v=0) :
    v=0 := by
  let q := HolderCoefficientIntegrability.coefficient hβ hβ₁ hg u
  let f (x : HeatCircle) := q x*v x
  have hf : Integrable f ν := (Lp.memLp q).integrable_mul (Lp.memLp v)
  have hm : Measurable f := (Lp.stronglyMeasurable q).measurable.mul (Lp.stronglyMeasurable v).measurable
  have hp (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) : inner ℝ
      (StateNoiseCovariance.row ν hβ hβ₁ hg (w ψ n) u) v=∫ x,w ψ n x*f x ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [StateNoiseCovariance.row_ae ν hβ hβ₁ hg (w ψ n) u,
      HolderCoefficientIntegrability.coefficient_ae hβ hβ₁ hg u] with x hr hq
    change q x=g (u x) at hq
    rw [hr,real_inner_smul_left,RCLike.inner_apply,conj_trivial]
    simp only [f,hq,mul_comm (v x)]
  have hz := ScalarFourierL1Separation.ae_zero f hf hm
    (fun n => (hp Complex.reCLM n).symm.trans (hre n))
    (fun n => (hp Complex.imCLM n).symm.trans (him n))
  apply Lp.ext
  filter_upwards [hz,HolderCoefficientIntegrability.coefficient_ae hβ hβ₁ hg u,Lp.coeFn_zero ℝ 2 ν]
    with x h hq hzero
  change q x*v x=0 at h
  change q x=g (u x) at hq
  rw [hq] at h
  rw [hzero,Pi.zero_apply]
  exact (mul_eq_zero.mp h).resolve_left (h₀ (u x))

end SHEStochastic.ScalarNoiseRowSeparation
