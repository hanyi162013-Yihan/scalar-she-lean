module

public import SHE.NormalizedProductIntegrability
public import SHE.PairedSlotIdentities

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.PairedAssignedTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianCoordinates
  GaussianVectorFractions StoppedFourier
open scoped BigOperators
open Classical
variable {n r m:ℕ}

/-- Genuine Gaussian integral telescope of the literal original
NO-FRESH assigned word. Every normalized slot's integrability is
derived internally from the bounded scalar coefficient/root. Both OWN
baselines and the actual current sources remain unchanged. -/
theorem gaussian_difference (P:CanonicalCovariance.ProfileParameters)
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n) (B:Matrix (Fin n) (Fin n) ℝ)
    (choices:List (Fin r×Fin (m+1))) (hnd:(choices.map Prod.fst).Nodup)
    (F:State 1→ℝ) (g:Fin 1→Fin n) (leaf:Fin m→Fin n)
    (newMean oldMean:State n) (newBaseline oldBaseline:Fin m→ℝ)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hF:ContDiff ℝ ((block choices 0).length+1) F)
    (hb:∀j,j≤(block choices 0).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j) :
    let μG:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)
    (∀i,Integrable (slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ i) μG) ∧
      (∫x,NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf newBaseline newMean x ∂μG)-
        (∫x,NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf oldBaseline oldMean x ∂μG)=
      ∑i,sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ i*
        (∫x,slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ i x ∂μG) := by
  intro μG
  let S:=fun x:(Fin r→State n)×State n=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j)
  let new:=fun x=>AssignedCurrentTelescope.factor P.coefficient choices F newMean g leaf newBaseline x
  let old:=fun x=>AssignedCurrentTelescope.factor P.coefficient choices F oldMean g leaf oldBaseline x
  let C:Fin (m+1)→ℝ:=fun i=>(2:ℝ)^(block choices i).length*
    Fin.cases A0 (fun j=>P.upper+max |newBaseline j| |oldBaseline j|) i
  have hF0(z):|F z|≤A0:=by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] using hb 0 (by omega) z
  have ha(z):|P.coefficient z|≤P.upper:=by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have hC(i):0≤C i:=by
    unfold C
    apply mul_nonneg (by positivity)
    exact Fin.cases hA0 (fun j=>add_nonneg P.upper_nonneg ((abs_nonneg _).trans (le_max_left _ _))) i
  have hm(mean:State n)(bas:Fin m→ℝ)(i:Fin (m+1)):
      Measurable (fun x=>AssignedCurrentTelescope.factor P.coefficient choices F mean g leaf bas x i):=by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact VectorControlledRoot.value_measurable choices 0 F hF.continuous.measurable mean g
    · exact ControlledAssignedLeaf.leaf_measurable choices j.succ P.coefficient P.measurable mean (leaf j) (bas j)
  have hbound(mean:State n)(bas:Fin m→ℝ)
      (hbas:∀j,|bas j|≤max |newBaseline j| |oldBaseline j|):
      ∀x i,|AssignedCurrentTelescope.factor P.coefficient choices F mean g leaf bas x i|≤C i := by
    intro x i
    refine Fin.cases ?_ (fun j=>?_) i
    · change |VectorControlledRoot.value choices 0 F mean g x|≤(2:ℝ)^(block choices 0).length*A0
      unfold VectorControlledRoot.value VectorJointRoot.value
      exact fractionDifferences_bound _ _ A0 (fun _=>hF0 _) _
    · change |ControlledAssignedLeaf.leaf choices j.succ P.coefficient mean (leaf j) (bas j) x|≤
        (2:ℝ)^(block choices j.succ).length*(P.upper+max |newBaseline j| |oldBaseline j|)
      unfold ControlledAssignedLeaf.leaf
      apply fractionDifferences_bound
      intro y
      exact (abs_sub _ _).trans (add_le_add (ha _) (hbas j))
  have hSi:Integrable S μG:=(Integrable.fintype_prod
    (fun j=>GaussianVectorFractions.gaussian_secondScore_integrable (A j) (D j))).comp_fst _
  have hI:=NormalizedProductTelescope.integrable_slots μG new old (hm newMean newBaseline)
    (hm oldMean oldBaseline) C hC
    (hbound newMean newBaseline (fun j=>le_max_left _ _))
    (hbound oldMean oldBaseline (fun j=>le_max_right _ _)) S hSi
    (sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ)
  have hi:∀i,Integrable (slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ i) μG:=by
    intro i
    exact hI.1 i
  have hnew:Integrable (NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf newBaseline newMean) μG:=by
    have hh:=hI.2.1
    simp only [new,AssignedCurrentTelescope.factor_product] at hh
    convert! hh using 1
    funext x
    unfold NoFreshGaussianIdentity.value S
    ring
  have hold:Integrable (NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf oldBaseline oldMean) μG:=by
    have hh:=hI.2.2
    simp only [old,AssignedCurrentTelescope.factor_product] at hh
    convert! hh using 1
    funext x
    unfold NoFreshGaussianIdentity.value S
    ring
  refine ⟨hi,?_⟩
  rw [←integral_sub hnew hold]
  calc
    _=(∫x,∑i,sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ i*
      slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ i x ∂μG):=by
        apply integral_congr_ae
        exact ae_of_all _ (fun x=>word_difference P A D choices hnd F g leaf newMean oldMean
          newBaseline oldBaseline hA0 hν hχ hχβ hF hb x)
    _=_:=by
      rw [integral_finsetSum _ (fun i _=>(hi i).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_const_mul _ _

end SHE.PairedAssignedTelescope
