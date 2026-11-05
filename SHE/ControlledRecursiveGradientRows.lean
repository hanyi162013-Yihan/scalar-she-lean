module

public import SHE.ControlledReferenceRecursiveBackward
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.GaussianParameterContinuity
public import SHE.ParameterSmoothContinuity
public import SHE.BackwardRegularity
public import SHE.FiniteItoNoise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledRecursiveGradientRows
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledRecursiveGradientRows_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledRecursiveGradientRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledRecursiveGradientRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

/-- Actual finite recursive Gaussian gradients have one global bound
across all past-state parameters, backward times and heat cutoffs. The
constant may depend on the fixed smooth depth and time cutoff. -/
theorem gradient_bound (k:ℕ):∃C:ℝ,0≤C ∧ ∀(p:Inputs)(ε:ℝ≥0)(h:History Unit k)(t:ℝ)(z:WordRecursion.State (n+k)),
    ‖fderiv ℝ (GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) t) z‖≤C:=by
  have hU:=ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k
  obtain ⟨C₀,hC₀,hB₀⟩:=hU.norm_bound
  obtain ⟨C₁,hC₁,hB₁⟩:=hU.fderiv.norm_bound
  refine ⟨C₁,hC₁,?_⟩
  intro p ε h t z
  exact BackwardRegularity.gaussian_state_gradient_bound _
    (((L p ε k).test_uniform.smooth h).of_le (by simp))
    (hB₀ (p,(ε,h))) (hB₁ (p,(ε,h))) z

include hsmall in
/-- Joint past-parameter/current-state continuity of the actual moving
recursive Gaussian gradient; this supplies true predictable product
measurability for random F_v parameters. -/
theorem continuous_gradient (hΛ:0≤Λ)(ε:ℝ≥0)(k:ℕ)(h:History Unit k)(t:ℝ):
    Continuous (fun q:Inputs×WordRecursion.State (n+k)=>
      fderiv ℝ (GaussianItoTest.backward ((L q.1 ε k).window h) ((L q.1 ε k).test h) t) q.2):=by
  have hU:=ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k
  obtain ⟨C₀,hC₀,hB₀⟩:=hU.norm_bound
  obtain ⟨C₁,hC₁,hB₁⟩:=hU.fderiv.norm_bound
  obtain ⟨C₂,hC₂,hB₂⟩:=hU.fderiv.fderiv.norm_bound
  apply ParameterSmoothContinuity.continuous_fderiv
    (fun p:Inputs=>GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) t)
    (ControlledReferenceRecursiveBackward.continuous_backward P A hA Λ θ v b hvb
      Z htarget hstop F hF δ hδ hsmall hΛ ε k h t)
    (fun p=>BackwardRegularity.gaussian_state_contDiff_two _
      (((L p ε k).test_uniform.smooth h).of_le (by simp))
      (hB₀ (p,(ε,h))) (hB₁ (p,(ε,h))) (hB₂ (p,(ε,h)))) hC₂
  intro p z
  exact BackwardRegularity.gaussian_state_hessian_bound _
    (((L p ε k).test_uniform.smooth h).of_le (by simp))
    (hB₀ (p,(ε,h))) (hB₁ (p,(ε,h))) (hB₂ (p,(ε,h))) z

theorem admissible_gradient (ε:ℝ≥0)(k:ℕ)(h:History Unit k)(p:Inputs):
    FiniteItoNoise.AdmissibleGradient
      (GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h)):=by
  have hU:=ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k
  obtain ⟨C₀,hC₀,hB₀⟩:=hU.norm_bound
  obtain ⟨C₁,hC₁,hB₁⟩:=hU.fderiv.norm_bound
  refine ⟨BackwardRegularity.gaussian_gradient_joint_continuous _ ((L p ε k).window h).continuous_path
    (((L p ε k).test_uniform.smooth h).of_le (by simp))
    (hB₀ (p,(ε,h))) (hB₁ (p,(ε,h))),?_⟩
  obtain ⟨C,hC,hCb⟩:=gradient_bound P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k
  exact ⟨C,fun t z=>hCb p ε h t z⟩

end SHE.ControlledRecursiveGradientRows
