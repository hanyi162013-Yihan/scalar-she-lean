module

public import SHE.OldOnlyTimeFactor
public import SHE.BaselineOriginalGain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.OmittedTimeFactor
open Set Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays CoveredControlledLaw GaussianCoordinates GaussianAssignmentBlocks
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

def factor (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (cs : List (Fin k×Fin (k+1))) (j0 : Fin k) (A0 ν : ℝ) : ℝ :=
  VectorPhysicalRoot.scale cs 0 (lower L k p) (upper L k p) A0 ν (P.lower/2) n*
    ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P cs j.succ (lower L k p) (upper L k p)
      (targets L k p (leafIndex k (fun i=>i) j)) (OldOnlyTimeFactor.chosen L k p cs j)

/-- Restoring the erased original leaf gives EXACTLY the old full word
factor, rather than a lower-order word with weakened time degree. -/
theorem restore_factor (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (cs : List (Fin k×Fin (k+1))) (j0 : Fin k) (q A0 ν : ℝ) :
    factor L P k p cs j0 A0 ν*NativeAssignedLeafMoments.leafScale P cs j0.succ (lower L k p) (upper L k p)
      (targets L k p (leafIndex k (fun i=>i) j0)) (OldOnlyTimeFactor.chosen L k p cs j0)=
      SharpWordTimeScale.factor L P k p q cs A0 ν := by
  rw [←OldOnlyTimeFactor.factor_eq_sharp L P k p q A0 ν cs]
  unfold factor OldOnlyTimeFactor.factor
  rw [mul_assoc,Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j0)]

/-- A genuine baseline profile derivative restores the same original
empty-leaf age and leaves only the universal fresh degree3/4. -/
theorem restored_gain (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (k : ℕ) (p : History X k) (cs : List (Fin k×Fin (k+1))) (j0 : Fin k)
    (hblock : block cs j0.succ=[]) (q A0 ν : ℝ) {gap : ℝ} (hgap : 0<gap)
    (hga : gap≤targets L k p (leafIndex k (fun i=>i) j0)) :
    ControlledScoreRates.sharpConstant P d*
        (targets L k p (leafIndex k (fun i=>i) j0))^((P.exponent-1)/4)*|factor L P k p cs j0 A0 ν|≤
      BaselineOriginalGain.unitSharp P d*|SharpWordTimeScale.factor L P k p q cs A0 ν| *gap^(-(1/4:ℝ)) := by
  let s := NativeAssignedLeafMoments.leafScale P cs j0.succ (lower L k p) (upper L k p)
    (targets L k p (leafIndex k (fun i=>i) j0)) (OldOnlyTimeFactor.chosen L k p cs j0)
  have hs : 0≤s := by
    simp only [s,NativeAssignedLeafMoments.leafScale,dite_eq_left hblock]
    exact mul_nonneg P.holder_nonneg (rpow_nonneg (hgap.le.trans hga) _)
  have hg := BaselineOriginalGain.empty_leaf_gain P d cs j0.succ hblock (lower L k p) (upper L k p)
    (OldOnlyTimeFactor.chosen L k p cs j0) hgap hga
  have hr : |factor L P k p cs j0 A0 ν| *s=|SharpWordTimeScale.factor L P k p q cs A0 ν| := by
    rw [←abs_of_nonneg hs,←abs_mul]
    exact congrArg abs (restore_factor L P k p cs j0 q A0 ν)
  have hh := mul_le_mul_of_nonneg_right hg (abs_nonneg (factor L P k p cs j0 A0 ν))
  change _≤BaselineOriginalGain.unitSharp P d*|SharpWordTimeScale.factor L P k p q cs A0 ν| *gap^(-(1/4:ℝ))
  rw [←hr]
  convert! hh using 1
  ring

end SHE.OmittedTimeFactor
