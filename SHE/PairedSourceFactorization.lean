module

public import SHE.PairedRoughWordMoments
public import SHE.ScalarNormalizedRootPair

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.PairedSourceFactorization
open Set MeasureTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianCoordinates
open scoped BigOperators
variable {n r k:ℕ}

/-- Exact fractional current root source extraction, INCLUDING its zero
case. The finite actual derivative packet supplies the zero implication. -/
theorem root (choices:List (Fin r×Fin k)) (hnd:(choices.map Prod.fst).Nodup)
    (factor:Fin k) (g:Fin 1→Fin n) (F:State 1→ℝ) {A0 ν χ:ℝ}
    (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχ1:χ≤1)
    (hF:ContDiff ℝ ((block choices factor).length+1) F)
    (hb:∀j,j≤(block choices factor).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (newMean oldMean:State n) (x:(Fin r→State n)×State n) :
    (min 1 (ν*‖projection g (newMean-oldMean)‖))^χ*
      NormalizedScalarMoment.value
        (VectorControlledRoot.value choices factor F newMean g x-
          VectorControlledRoot.value choices factor F oldMean g x)
        ((min 1 (ν*‖projection g (newMean-oldMean)‖))^χ)=
        VectorControlledRoot.value choices factor F newMean g x-
          VectorControlledRoot.value choices factor F oldMean g x := by
  apply NormalizedScalarMoment.factorization
  intro hz
  have hh:=VectorPairedJointRoot.pointwise_bound choices hnd factor F hA0 hν hχ hχ1 hF hb
    (fun y=>projection g (oldMean+y)) (fun _ : Fin r=>projection g)
    (projection g (newMean-oldMean)) x
  rw [←PairedControlledRootMoments.difference_eq choices factor F newMean oldMean g] at hh
  simp only [hz,mul_zero,zero_mul] at hh
  exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))

/-- Every actual rough paired slot has exact current-source extraction.
For an empty block the WHOLE own-baseline difference is retained. -/
theorem rough (P:CanonicalCovariance.ProfileParameters)
    (choices:List (Fin r×Fin k)) (hnd:(choices.map Prod.fst).Nodup) (factor:Fin k)
    {χ:ℝ} (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (newMean oldMean:State n) (i:Fin n) (newBaseline oldBaseline:ℝ)
    (x:(Fin r→State n)×State n) :
    PairedRoughWordMoments.source P choices factor χ newMean oldMean i newBaseline oldBaseline*
      PairedRoughWordMoments.value P choices factor χ newMean oldMean i newBaseline oldBaseline x=
      ControlledAssignedLeaf.leaf choices factor P.coefficient newMean i newBaseline x-
        ControlledAssignedLeaf.leaf choices factor P.coefficient oldMean i oldBaseline x := by
  by_cases hb:block choices factor=[]
  · unfold PairedRoughWordMoments.value
    apply NormalizedScalarMoment.factorization
    intro hz
    have hh:=OwnBaselineTelescope.leaf_empty_bound choices factor hb P.coefficient P.holder_nonneg
      P.exponent_pos hχ hχβ P.holder_bound newMean oldMean i newBaseline oldBaseline x
    have hs:PairedRoughWordMoments.source P choices factor χ newMean oldMean i newBaseline oldBaseline=
        P.holder^(χ/P.exponent)*|newMean i-oldMean i|^χ+|newBaseline-oldBaseline|^(χ/P.exponent) := by
      simp only [PairedRoughWordMoments.source,hb,ite_true,NormalizedPairedLeaf.source]
    rw [←hs,hz,zero_mul] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  · obtain ⟨j,hj⟩:=List.exists_mem_of_ne_nil (block choices factor) hb
    simpa only [PairedRoughWordMoments.value,PairedRoughWordMoments.source,hb,ite_false] using
      PhysicalNormalizedAssignedPair.factorization P choices hnd factor j hj i newMean oldMean newBaseline oldBaseline hχ hχβ x

end SHE.PairedSourceFactorization
