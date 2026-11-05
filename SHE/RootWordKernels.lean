module

public import SHE.RootWordLinearity
public import SHE.WeightedMeanBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootWordLinearity
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution GaussianSmooth SmoothCylinders CutoffInsertionCore ActualMeanKernel
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L K : Level R X n) (hT : ∀ x,L.terminal x=K.terminal x)
    (hZ : ∀ x,L.observations.observations x=K.observations.observations x)
variable (M : Level R X n) (hTM : ∀ x,L.terminal x=M.terminal x)
    (hZM : ∀ x,L.observations.observations x=M.observations.observations x)
include hT hZ hTM hZM

theorem gradient_add (hroot : ∀ x,L.test x=K.test x+M.test x)
    (k : ℕ) (q : ℝ) (p : History X k) (z : WordRecursion.State (n+k)) :
    fderiv ℝ (cappedAverage L k q p) z=
      fderiv ℝ (cappedAverage K k q p) z+fderiv ℝ (cappedAverage M k q p) z := by
  rw [cappedAverage_add L K hT hZ M hTM hZM hroot k q p]
  exact fderiv_add (cappedAverage_differentiable K k q p z) (cappedAverage_differentiable M k q p z)

/-- The actual stop-weighted terminal derivative is additive in the
root, retaining its q-law, later row time, and all original stops. -/
theorem weightedPoint_add (hroot : ∀ x,L.test x=K.test x+M.test x)
    (k : ℕ) (Λ q r : ℝ) (m : History X k→WordRecursion.State (n+k)) (p : History X k) (y : HeatCircle) :
    weightedPoint L k Λ q r m p y=weightedPoint K k Λ q r m p y+weightedPoint M k Λ q r m p y := by
  classical
  have htK:=CarrierGeometryCongruence.terminal L K rfl hT k p
  have htM:=CarrierGeometryCongruence.terminal L M rfl hTM k p
  have hzK:=CarrierGeometryCongruence.observations L K rfl hT hZ k p
  have hzM:=CarrierGeometryCongruence.observations L M rfl hTM hZM k p
  by_cases ha : q<(carrier L k).terminal p ∧ r<(carrier L k).terminal p
  · have hqK : q<(carrier K k).terminal p:=by rw [←htK];exact ha.1
    have hrK : r<(carrier K k).terminal p:=by rw [←htK];exact ha.2
    have hqM : q<(carrier M k).terminal p:=by rw [←htM];exact ha.1
    have hrM : r<(carrier M k).terminal p:=by rw [←htM];exact ha.2
    rw [weightedPoint_of_active L k Λ q r m p y ha.1 ha.2,
      weightedPoint_of_active K k Λ q r m p y hqK hrK,
      weightedPoint_of_active M k Λ q r m p y hqM hrM]
    have hh:=congrArg (fun D : WordRecursion.State (n+k)→L[ℝ]ℝ=>
      D (StopWeightedRows.weightedHeatRow Λ ((carrier L k).observations.observations p) q r y))
      (gradient_add L K hT hZ M hTM hZM hroot k q p (m p))
    simp only [cappedAverage,min_eq_left ha.1.le,min_eq_left hqK.le,min_eq_left hqM.le,
      ContinuousLinearMap.add_apply] at hh
    rw [←hzK,←hzM] at hh ⊢
    exact hh
  · simp only [weightedPoint,←htK,←htM,ite_eq_right ha,add_zero]

omit hT hZ hTM hZM in
/-- Vanishing of the initial root forces the ACTUAL recursive test and
all of its capped Gaussian averages to vanish, at every depth. -/
theorem test_zero {Y : Type} [MeasurableSpace Y] {Q : ReferenceData} {d : ℕ}
    (B : Level Q Y d) (hroot : ∀ x,B.test x=0) (k : ℕ) (p : History Y k) :
    UncutSmoothWords.test B k p=0 := by
  have hh:=test_add B B (fun _=>rfl) (fun _=>rfl) B (fun _=>rfl) (fun _=>rfl)
    (fun x=>by rw [hroot x];simp only [add_zero]) k p
  funext z
  have he:=congrFun hh z
  change UncutSmoothWords.test B k p z=0
  change UncutSmoothWords.test B k p z=UncutSmoothWords.test B k p z+UncutSmoothWords.test B k p z at he
  linarith
end SHE.RootWordLinearity
