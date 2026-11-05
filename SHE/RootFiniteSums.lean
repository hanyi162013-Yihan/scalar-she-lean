module

public import SHE.RootWordKernels
public import SHE.RootSmoothSums

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootFiniteSums
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianConvolution SmoothCylinders UniformSmooth RootSmoothSums RootWordLinearity ActualMeanKernel
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

def withRoot (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
    (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2)) : Level R X n:=
  { L with test:=F,test_uniform:=hF,test_measurable:=hFm }

variable (F : ℕ→X→WordRecursion.State n→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
  (hFm : ∀ j,Measurable (fun z : X×WordRecursion.State n=>F j z.1 z.2))

def band (j : ℕ) : Level R X n:=withRoot L (F j) (hF j) (hFm j)
def sumLevel (s : Finset ℕ) : Level R X n:=
  withRoot L (rootSum F s) (rootSum_uniform F hF s) (rootSum_measurable F hFm s)

local notation "B"=>band L F hF hFm
local notation "S"=>sumLevel L F hF hFm

theorem test_sum (s : Finset ℕ) (k : ℕ) (p : History X k) :
    UncutSmoothWords.test (S s) k p=∑ j∈s,UncutSmoothWords.test (B j) k p := by
  induction s using Finset.induction_on with
  | empty=>
    rw [Finset.sum_empty]
    exact RootWordLinearity.test_zero (S ∅) (fun x=>by funext z;simp only [sumLevel,withRoot,rootSum,Finset.sum_empty,Pi.zero_apply]) k p
  | @insert j s hj ih=>
    have hr (x : X) : (S (insert j s)).test x=(B j).test x+(S s).test x:=by
      funext z
      simp only [sumLevel,band,withRoot,rootSum,Finset.sum_insert hj,Pi.add_apply]
    rw [RootWordLinearity.test_add (S (insert j s)) (B j) (fun _=>rfl) (fun _=>rfl)
      (S s) (fun _=>rfl) (fun _=>rfl) hr k p,ih,Finset.sum_insert hj]

theorem cappedAverage_sum (s : Finset ℕ) (k : ℕ) (q : ℝ) (p : History X k) :
    cappedAverage (S s) k q p=∑ j∈s,cappedAverage (B j) k q p := by
  induction s using Finset.induction_on with
  | empty=>
    rw [Finset.sum_empty]
    have hz:=test_sum L F hF hFm ∅ k p
    simp only [Finset.sum_empty] at hz
    funext z
    simp only [cappedAverage,hz,gaussianAverage,Pi.zero_apply,integral_zero]
  | @insert j s hj ih=>
    have hr (x : X) : (S (insert j s)).test x=(B j).test x+(S s).test x:=by
      funext z
      simp only [sumLevel,band,withRoot,rootSum,Finset.sum_insert hj,Pi.add_apply]
    rw [RootWordLinearity.cappedAverage_add (S (insert j s)) (B j) (fun _=>rfl) (fun _=>rfl)
      (S s) (fun _=>rfl) (fun _=>rfl) hr k q p,ih,Finset.sum_insert hj]

theorem gradient_sum (s : Finset ℕ) (k : ℕ) (q : ℝ) (p : History X k) (z : WordRecursion.State (n+k)) :
    fderiv ℝ (cappedAverage (S s) k q p) z=∑ j∈s,fderiv ℝ (cappedAverage (B j) k q p) z := by
  rw [cappedAverage_sum L F hF hFm s k q p]
  have he : (∑ j∈s,cappedAverage (B j) k q p)=
      (fun y=>∑ j∈s,cappedAverage (B j) k q p y) := by
    ext y
    simp only [Finset.sum_apply]
  rw [he]
  exact fderiv_fun_sum (u:=s) (fun j _=>cappedAverage_differentiable (B j) k q p z)

/-- Literal finite root cutoffs give the finite sum of actual weighted
physical kernels, with no replacement of their q-law or original stops. -/
theorem weightedPoint_sum (s : Finset ℕ) (k : ℕ) (Λ q r : ℝ)
    (m : History X k→WordRecursion.State (n+k)) (p : History X k) (y : HeatCircle) :
    weightedPoint (S s) k Λ q r m p y=∑ j∈s,weightedPoint (B j) k Λ q r m p y := by
  induction s using Finset.induction_on with
  | empty=>
    rw [Finset.sum_empty]
    have hz:=test_sum L F hF hFm ∅ k p
    simp only [Finset.sum_empty] at hz
    have hg (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ) :
        gaussianAverage A (0 : WordRecursion.State (n+k)→ℝ)=fun _=>(0:ℝ):=by
      funext z
      simp only [gaussianAverage,Pi.zero_apply,integral_zero]
    have hd : fderiv ℝ (fun _ : WordRecursion.State (n+k)=>(0:ℝ)) (m p)=0:=
      (hasFDerivAt_const (0:ℝ) (m p)).fderiv
    simp only [weightedPoint,hz,hg,hd,ContinuousLinearMap.zero_apply,ite_self]
  | @insert j s hj ih=>
    have hr (x : X) : (S (insert j s)).test x=(B j).test x+(S s).test x:=by
      funext z
      simp only [sumLevel,band,withRoot,rootSum,Finset.sum_insert hj,Pi.add_apply]
    rw [RootWordLinearity.weightedPoint_add (S (insert j s)) (B j) (fun _=>rfl) (fun _=>rfl)
      (S s) (fun _=>rfl) (fun _=>rfl) hr k Λ q r m p y,ih,Finset.sum_insert hj]
end SHE.RootFiniteSums
