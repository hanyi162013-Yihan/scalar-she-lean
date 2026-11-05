module

public import SHE.NormalizedProductTelescope
public import SHE.PairedSourceFactorization
public import SHE.NoFreshGaussianIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PairedAssignedTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianCoordinates
open scoped BigOperators
variable {n r m:ℕ}

def sources (P:CanonicalCovariance.ProfileParameters) (choices:List (Fin r×Fin (m+1)))
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n)
    (newBaseline oldBaseline:Fin m→ℝ) (ν χ:ℝ) : Fin (m+1)→ℝ :=
  Fin.cases ((min 1 (ν*‖projection g (newMean-oldMean)‖))^χ)
    (fun j=>PairedRoughWordMoments.source P choices j.succ χ newMean oldMean (leaf j)
      (newBaseline j) (oldBaseline j))

def slot (P:CanonicalCovariance.ProfileParameters) (A:Fin r→Matrix (Fin n) (Fin n) ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n)
    (newBaseline oldBaseline:Fin m→ℝ) (ν χ:ℝ) (i:Fin (m+1))
    (x:(Fin r→State n)×State n) : ℝ :=
  (∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
    NormalizedProductTelescope.term
      (AssignedCurrentTelescope.factor P.coefficient choices F newMean g leaf newBaseline x)
      (AssignedCurrentTelescope.factor P.coefficient choices F oldMean g leaf oldBaseline x)
      (sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ) i

/-- Literal NO-FRESH assigned word comparison with OWN endpoint
baselines. Every current source is extracted before the Gaussian law;
all unchanged original old scores remain in each normalized slot. -/
theorem word_difference (P:CanonicalCovariance.ProfileParameters)
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n)
    (choices:List (Fin r×Fin (m+1))) (hnd:(choices.map Prod.fst).Nodup)
    (F:State 1→ℝ) (g:Fin 1→Fin n) (leaf:Fin m→Fin n)
    (newMean oldMean:State n) (newBaseline oldBaseline:Fin m→ℝ)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hF:ContDiff ℝ ((block choices 0).length+1) F)
    (hb:∀j,j≤(block choices 0).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (x:(Fin r→State n)×State n) :
    NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf newBaseline newMean x-
      NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf oldBaseline oldMean x=
      ∑i,sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ i*
        slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ i x := by
  have hz(i:Fin (m+1)) : sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ i=0→
      AssignedCurrentTelescope.factor P.coefficient choices F newMean g leaf newBaseline x i=
        AssignedCurrentTelescope.factor P.coefficient choices F oldMean g leaf oldBaseline x i := by
    refine Fin.cases ?_ (fun j=>?_) i
    · intro hs
      have hh:=PairedSourceFactorization.root choices hnd 0 g F hA0 hν hχ
        (hχβ.trans P.exponent_le_one) hF hb newMean oldMean x
      simp only [sources,Fin.cases_zero] at hs
      rw [hs,zero_mul] at hh
      exact sub_eq_zero.mp hh.symm
    · intro hs
      have hh:=PairedSourceFactorization.rough P choices hnd j.succ hχ hχβ newMean oldMean
        (leaf j) (newBaseline j) (oldBaseline j) x
      simp only [sources,Fin.cases_succ] at hs
      rw [hs,zero_mul] at hh
      exact sub_eq_zero.mp hh.symm
  have he:=NormalizedProductTelescope.sum_difference
    (AssignedCurrentTelescope.factor P.coefficient choices F newMean g leaf newBaseline x)
    (AssignedCurrentTelescope.factor P.coefficient choices F oldMean g leaf oldBaseline x)
    (sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ) hz
  simp only [AssignedCurrentTelescope.factor_product] at he
  unfold NoFreshGaussianIdentity.value
  calc
    _=(∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
        ((VectorControlledRoot.value choices 0 F newMean g x*
          ∏j,ControlledAssignedLeaf.leaf choices j.succ P.coefficient newMean (leaf j) (newBaseline j) x)-
        (VectorControlledRoot.value choices 0 F oldMean g x*
          ∏j,ControlledAssignedLeaf.leaf choices j.succ P.coefficient oldMean (leaf j) (oldBaseline j) x)) := by ring
    _=_ := by rw [he,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;unfold slot;ring

end SHE.PairedAssignedTelescope
