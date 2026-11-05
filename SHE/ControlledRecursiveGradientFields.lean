module

public import SHE.ControlledRecursiveGradientRows
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.GaussianParameterContinuity
public import SHE.ParameterSmoothContinuity
public import SHE.BackwardRegularity
public import SHE.FiniteItoNoise
public import SHE.CutoffWordAnalytic
public import SHE.MeasurableDerivatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledRecursiveGradientFields
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledRecursiveGradientFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledRecursiveGradientFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledRecursiveGradientFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance controlledRecursiveGradientFields_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
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

attribute [local irreducible] ControlledReferenceRecursiveBounds.level

include hsmall in
private theorem value_joint_measurable (hΛ:0≤Λ)(ε:ℝ≥0)(k:ℕ):Measurable
    (fun z:(Inputs×(History Unit k×ℝ))×WordRecursion.State (n+k)=>
      GaussianItoTest.backward ((L z.1.1 ε k).window z.1.2.1)
        ((L z.1.1 ε k).test z.1.2.1) z.1.2.2 z.2):=by
  have hc:∀z:(History Unit k×ℝ)×WordRecursion.State (n+k),Continuous (fun p:Inputs=>
      GaussianItoTest.backward ((L p ε k).window z.1.1) ((L p ε k).test z.1.1) z.1.2 z.2):=by
    intro z
    have hh:=ControlledReferenceRecursiveBackward.continuous_backward P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k z.1.1 z.1.2
    have hmap:Continuous (fun p:Inputs=>(p,z.2)):=continuous_id.prodMk continuous_const
    have hhc:=hh.comp hmap
    simpa only [Function.comp_def] using hhc
  have hm:∀p:Inputs,Measurable (fun z:(History Unit k×ℝ)×WordRecursion.State (n+k)=>
      GaussianItoTest.backward ((L p ε k).window z.1.1) ((L p ε k).test z.1.1) z.1.2 z.2):=by
    intro p
    exact CutoffWordAnalytic.backward_measurable (L p ε k)
  have ht:=measurable_uncurry_of_continuous_of_measurable hc hm
  have hmap:Measurable (fun z:(Inputs×(History Unit k×ℝ))×WordRecursion.State (n+k)=>
      (z.1.1,(z.1.2,z.2))):=measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hh:=ht.comp hmap
  exact hh

include hsmall in
/-- Joint Borel gradient of the actual positive-cutoff recursive family,
including its original history and backward time parameters. -/
theorem gradient_joint_measurable (hΛ:0≤Λ)(ε:ℝ≥0)(k:ℕ):Measurable
    (fun z:Inputs×((History Unit k×ℝ)×WordRecursion.State (n+k))=>
      fderiv ℝ (GaussianItoTest.backward ((L z.1 ε k).window z.2.1.1)
        ((L z.1 ε k).test z.2.1.1) z.2.1.2) z.2.2):=by
  have hd:=MeasurableDerivatives.fderiv_measurable
    (value_joint_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k)
    (fun q:(Inputs×(History Unit k×ℝ))=>
      ((CutoffWordAnalytic.backward_uniform (L q.1 ε k)).smooth q.2).differentiable (by simp))
  have hmap:Measurable (fun z:Inputs×((History Unit k×ℝ)×WordRecursion.State (n+k))=>
      ((z.1,z.2.1),z.2.2)):=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hh:=hd.comp hmap
  exact hh

end SHE.ControlledRecursiveGradientFields
