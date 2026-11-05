module

public import SHE.AssignedCurrentTelescope
public import SHE.PairedEndpointLeaf
public import SHE.PhysicalPairedRough

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.OwnBaselineTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  AssignedCurrentTelescope GaussianRoughBlocks JointGaussianBlocks
open scoped BigOperators
variable {n d r m k : ℕ}

/-- Exact endpoint product telescope with BOTH original baselines.
All old score matrices remain fixed and exactly one factor is paired
in each summand. -/
theorem coefficientWord_difference (a : ℝ→ℝ) (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r→State n) (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ)
    (newMean oldMean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (newBaseline oldBaseline : Fin m→ℝ) (x : (Fin r→State n)×State n) :
    VectorControlledAssignedWord.coefficientWord a A D choices F newMean g leaf newBaseline x-
      VectorControlledAssignedWord.coefficientWord a A D choices F oldMean g leaf oldBaseline x=
      (∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
        (terms (factor a choices F newMean g leaf newBaseline x)
          (factor a choices F oldMean g leaf oldBaseline x) (List.ofFn (fun i : Fin (m+1) => i))).sum := by
  rw [terms_sum]
  simp only [List.map_ofFn,Fin.prod_ofFn,Function.comp_apply]
  rw [factor_product,factor_product]
  unfold VectorControlledAssignedWord.coefficientWord
  ring

/-- In a nonempty assigned rough block each endpoint baseline vanishes
separately. The genuine paired value is therefore the original scalar
current increment, with no baseline interpolation. -/
theorem leaf_nonempty_difference (choices : List (Fin r×Fin k)) (factor : Fin k)
    (hblock : block choices factor≠[]) (a : ℝ→ℝ) (newMean oldMean : State n)
    (i : Fin n) (newBaseline oldBaseline : ℝ) :
    (fun x=>(ControlledAssignedLeaf.leaf choices factor a newMean i newBaseline x-
      ControlledAssignedLeaf.leaf choices factor a oldMean i oldBaseline x))=
      PairedRoughBlocks.value choices factor a (fun y=>oldMean i+y i)
        (fun _ : Fin r=>EuclideanSpace.proj (𝕜:=ℝ) i) (newMean i-oldMean i) := by
  rw [ControlledAssignedLeaf.leaf_nonempty choices factor hblock,
    ControlledAssignedLeaf.leaf_nonempty choices factor hblock]
  unfold PairedRoughBlocks.value
  have he : (fun y : State n=>oldMean i+y i+(newMean i-oldMean i))=
      (fun y : State n=>newMean i+y i) := by funext y; ring
  rw [he]

/-- Empty-block pairing applies to the WHOLE centered endpoint leaf.
The true own-baseline difference remains a distinct input source. -/
theorem leaf_empty_bound (choices : List (Fin r×Fin k)) (factor : Fin k)
    (hblock : block choices factor=[]) (a : ℝ→ℝ) {H β χ : ℝ}
    (hH : 0≤H) (hβ : 0<β) (hχ : 0≤χ) (hχβ : χ≤β)
    (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (newMean oldMean : State n) (i : Fin n) (newBaseline oldBaseline : ℝ)
    (x : (Fin r→State n)×State n) :
    |ControlledAssignedLeaf.leaf choices factor a newMean i newBaseline x-
      ControlledAssignedLeaf.leaf choices factor a oldMean i oldBaseline x|≤
      (H^(χ/β)*|newMean i-oldMean i|^χ+|newBaseline-oldBaseline|^(χ/β))*
        (|ControlledAssignedLeaf.leaf choices factor a newMean i newBaseline x|+
          |ControlledAssignedLeaf.leaf choices factor a oldMean i oldBaseline x|)^(1-χ/β) := by
  simp_rw [ControlledAssignedLeaf.leaf_empty choices factor hblock]
  have hh:=PairedEndpointLeaf.bound a hH hβ hχ hχβ hholder (oldMean i)
    (newMean i-oldMean i) (((∑ j,suppress (suppressed choices factor) x.1 j)+x.2) i)
    oldBaseline newBaseline
  have he : oldMean i+(newMean i-oldMean i)=newMean i:=by ring
  simpa only [he] using hh

end SHE.OwnBaselineTelescope
