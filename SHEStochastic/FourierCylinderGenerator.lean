module

public import SHEStochastic.NativeFourierHeatCoordinate
public import SHEStochastic.StateNoiseCovariance
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import Mathlib.Analysis.Calculus.FDeriv.Const

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.FourierCylinderGenerator
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open GaussianItoTest NativeFourierHeatCoordinate
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {d : ℕ}

def projection (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) : RealL2 →L[ℝ] State d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ coordinate (a i) (n i))

def projectionMap (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) : C(RealL2, State d) :=
  ⟨projection a n, (projection a n).continuous⟩

variable (F : State d → ℝ) (hF : ContDiff ℝ 2 F) (hs : HasCompactSupport F)

def test (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) : BoundedContinuousFunction RealL2 ℝ :=
  (_root_.ofCompactSupport F hF.continuous hs).compContinuous (projectionMap a n)

/-- Compact support of the gradient makes the heat drift bounded even
though the Fourier coordinate itself ranges over the whole real line. -/
def driftComponent (n : Fin d → ℤ) (i : Fin d) : BoundedContinuousFunction (State d) ℝ := by
  let f := fun z : State d ↦ -(n i : ℝ) ^ 2 * z i *
    fderiv ℝ F z (EuclideanSpace.basisFun (Fin d) ℝ i)
  have hc : Continuous f :=
    (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i)).mul
      ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hd : HasCompactSupport (fun z ↦ fderiv ℝ F z (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
    hs.fderiv_apply ℝ _
  exact _root_.ofCompactSupport f hc
    (hd.mul_left (f := fun z : State d ↦ -(n i : ℝ) ^ 2 * z i))

def hessianEntry (i j : Fin d) : BoundedContinuousFunction (State d) ℝ := by
  have hc : Continuous (GaussianTaylor.hessian F) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hd : HasCompactSupport (GaussianTaylor.hessian F) := (hs.fderiv ℝ).fderiv ℝ
  exact _root_.ofCompactSupport
    (fun z ↦ GaussianTaylor.hessian F z (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ j))
    ((hc.clm_apply continuous_const).clm_apply continuous_const)
    (hd.comp_left (g := fun A : State d →L[ℝ] State d →L[ℝ] ℝ ↦
      A (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j)) (by simp))

def heatDrift (n : Fin d → ℤ) : BoundedContinuousFunction (State d) ℝ :=
  ∑ i : Fin d, driftComponent F hF hs n i

theorem heatDrift_apply (n : Fin d → ℤ) (z : State d) :
    heatDrift F hF hs n z = ∑ i : Fin d, -(n i : ℝ) ^ 2 * z i *
      fderiv ℝ F z (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  change (BoundedContinuousFunction.evalCLM ℝ z) (∑ i : Fin d, driftComponent F hF hs n i) = _
  rw [map_sum]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)

/-- The actual covariance entry is a bounded continuous state function
for the radially truncated coefficient. -/
def covariance (R : ℝ≥0) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) (i j : Fin d) :
    BoundedContinuousFunction RealL2 ℝ := by
  let B := ‖G 0‖ + (C : ℝ) * (R : ℝ) ^ (β : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let b := StateNoiseCovariance.bounded haarAddCircle hβ hβ1
    (UnboundedCoefficientCutoff.holder hG R) (UnboundedCoefficientCutoff.holder hG R)
    (weight (a i) (n i)) (weight (a j) (n j)) B B hB hB
    (UnboundedCoefficientCutoff.bounded hG R) (UnboundedCoefficientCutoff.bounded hG R)
  exact b.compContinuous ⟨NativePhysicalState.push, NativePhysicalState.push.continuous⟩

/-- The finite Fourier cylinder generator for a bounded radial cutoff,
constructed in precisely the bounded continuous class used by the
continuation and canonical martingale-law pasting theorems. -/
def generator (R : ℝ≥0) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    BoundedContinuousFunction RealL2 ℝ :=
  (∑ i : Fin d, (driftComponent F hF hs n i).compContinuous (projectionMap a n)) +
    (1 / 2 : ℝ) • ∑ i : Fin d, ∑ j : Fin d,
      covariance hG hβ hβ1 R a n i j *
        (hessianEntry F hF hs i j).compContinuous (projectionMap a n)

/-- The literal finite Fourier generator, also defined for an unbounded
coefficient. Its bounded cutoff realization is the bundled generator. -/
def value (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) (u : RealL2) : ℝ :=
  (∑ i : Fin d, -(n i : ℝ) ^ 2 * projection a n u i *
    fderiv ℝ F (projection a n u) (EuclideanSpace.basisFun (Fin d) ℝ i)) +
    (1 / 2 : ℝ) * ∑ i : Fin d, ∑ j : Fin d,
      StateNoiseCovariance.value haarAddCircle hβ hβ1 hG hG (weight (a i) (n i)) (weight (a j) (n j))
        (NativePhysicalState.push u) * GaussianTaylor.hessian F (projection a n u)
          (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j)

include hF in
theorem continuous_value (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    Continuous (value F hG hβ hβ1 a n) := by
  have hp := (projection a n).continuous
  have hd := (hF.continuous_fderiv (by norm_num)).comp hp
  have hh : Continuous (fun u : RealL2 ↦ GaussianTaylor.hessian F (projection a n u)) :=
    ((hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)).comp hp
  unfold value
  apply Continuous.add
  · apply continuous_finsetSum
    intro i _
    exact (continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).comp hp)).mul
      (hd.clm_apply continuous_const)
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((StateNoiseCovariance.continuous haarAddCircle hβ hβ1 hG hG
      (weight (a i) (n i)) (weight (a j) (n j))).comp NativePhysicalState.push.continuous).mul
        ((hh.clm_apply continuous_const).clm_apply continuous_const)

theorem generator_apply (R : ℝ≥0) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) (u : RealL2) :
    generator F hF hs hG hβ hβ1 R a n u =
      value F (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 a n u := by
  change (BoundedContinuousFunction.evalCLM ℝ u) (generator F hF hs hG hβ hβ1 R a n) = _
  simp only [generator, map_add, map_smul, map_sum, BoundedContinuousFunction.evalCLM_apply,
    BoundedContinuousFunction.mul_apply, smul_eq_mul]
  rfl

/-- This is the exact canonical-generator agreement needed before
the uniform exit; agreement is proved for actual L2 state classes. -/
theorem generator_agrees (R : ℝ≥0) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) (u : RealL2)
    (hu : ∀ᵐ x ∂haarAddCircle, ‖NativePhysicalState.push u x‖ ≤ R) :
    generator F hF hs hG hβ hβ1 R a n u = value F hG hβ hβ1 a n u := by
  rw [generator_apply]
  simp only [value]
  simp_rw [StateNoiseCovariance.cutoff_agrees haarAddCircle hβ hβ1 hG _ _ R (NativePhysicalState.push u) hu]

end SHEStochastic.FourierCylinderGenerator
