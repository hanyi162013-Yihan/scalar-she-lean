module

public import SHE.PairedAssignedTelescope
public import SHE.NormalizedProductSlots
public import SHE.PairedRootVaryingMoments
public import SHE.PairedRoughVaryingMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section
namespace SHE.PairedAssignedTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianCoordinates
  StoppedFourier ControlledOldIntervals OldIntervalCovariance
open scoped BigOperators
open Classical
variable {n r m:ℕ}

theorem root_slot (P:CanonicalCovariance.ProfileParameters)
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n)
    (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ) (g:Fin 1→Fin n) (leaf:Fin m→Fin n)
    (newMean oldMean:State n) (newBaseline oldBaseline:Fin m→ℝ) (ν χ:ℝ)
    (x:(Fin r→State n)×State n) :
    slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ 0 x=
      (∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
        NormalizedScalarMoment.value
          (VectorControlledRoot.value choices 0 F newMean g x-VectorControlledRoot.value choices 0 F oldMean g x)
          ((min 1 (ν*‖projection g (newMean-oldMean)‖))^χ)*
        ∏j,ControlledAssignedLeaf.leaf choices j.succ P.coefficient newMean (leaf j) (newBaseline j) x := by
  unfold slot
  rw [NormalizedProductTelescope.term_eq_product,Fin.prod_univ_succ]
  have hpos(j:Fin m):(0:Fin (m+1))<j.succ:=by change 0<j.val+1;omega
  simp only [sources,AssignedCurrentTelescope.factor,Fin.cases_zero,Fin.cases_succ,ite_true,
    Fin.succ_ne_zero,ite_false,hpos]
  ring

theorem rough_slot (P:CanonicalCovariance.ProfileParameters)
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n)
    (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ) (g:Fin 1→Fin n) (leaf:Fin m→Fin n)
    (newMean oldMean:State n) (newBaseline oldBaseline:Fin m→ℝ) (ν χ:ℝ) (j0:Fin m)
    (x:(Fin r→State n)×State n) :
    slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ j0.succ x=
      (∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
        VectorControlledRoot.value choices 0 F oldMean g x*
        ∏j,if j=j0 then PairedRoughWordMoments.value P choices j0.succ χ newMean oldMean (leaf j0)
          (newBaseline j0) (oldBaseline j0) x
        else if j0<j then ControlledAssignedLeaf.leaf choices j.succ P.coefficient newMean (leaf j) (newBaseline j) x
        else ControlledAssignedLeaf.leaf choices j.succ P.coefficient oldMean (leaf j) (oldBaseline j) x := by
  unfold slot
  rw [NormalizedProductTelescope.term_eq_product,Fin.prod_univ_succ]
  have hne:(0:Fin (m+1))≠j0.succ:=(Fin.succ_ne_zero j0).symm
  have hnlt:¬j0.succ<(0:Fin (m+1)):=by change ¬(j0.val+1<(0:ℕ));omega
  simp only [hne,hnlt,ite_false,AssignedCurrentTelescope.factor,
    Fin.cases_zero,Fin.cases_succ,sources,Fin.succ_inj,Fin.succ_lt_succ_iff,
    PairedRoughWordMoments.value]
  ring

/-- The literal ROOT telescope Gaussian average is exactly the
normalized root fibre already carrying all checked dependent moments. -/
theorem root_average (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ ηNew ηOld q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n) (ν χ:ℝ) :
    let A:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let bas:=fun η j=>ControlledProfile.profile P Λ u d (η,(target (leaf j),center (leaf j)))
    (∫x,slot P A D choices F g leaf newMean oldMean (bas ηNew) (bas ηOld) ν χ 0 x
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B))=
      PairedRootVaryingMoments.fibreAverage P Λ u d θ q σ target center lo hi newMean oldMean
        (fun _=>newMean) (fun _=>ηNew) D g leaf choices F ν χ := by
  intro A B bas
  unfold PairedRootVaryingMoments.fibreAverage
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>root_slot P A D choices F g leaf newMean oldMean (bas ηNew) (bas ηOld) ν χ x)

/-- Every literal ROUGH telescope Gaussian average is exactly the
checked paired rough fibre, with its original per-factor endpoint choice. -/
theorem rough_average (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ ηNew ηOld q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n) (ν χ:ℝ) (j0:Fin m) :
    let A:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let bas:=fun η j=>ControlledProfile.profile P Λ u d (η,(target (leaf j),center (leaf j)))
    (∫x,slot P A D choices F g leaf newMean oldMean (bas ηNew) (bas ηOld) ν χ j0.succ x
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B))=
      PairedRoughVaryingMoments.fibreAverage P Λ u d θ ηOld ηNew q σ target center lo hi
        newMean oldMean oldMean (fun j=>decide (j0<j)) D g leaf choices j0 F χ := by
  intro A B bas
  unfold PairedRoughVaryingMoments.fibreAverage
  apply integral_congr_ae
  apply ae_of_all
  intro x
  rw [rough_slot P A D choices F g leaf newMean oldMean (bas ηNew) (bas ηOld) ν χ j0 x]
  congr 2
  funext j
  by_cases hj:j=j0
  · subst j;simp only [ite_true,bas]
  · simp only [hj,ite_false]
    by_cases hlt:j0<j <;> simp [hlt,bas]

end SHE.PairedAssignedTelescope
