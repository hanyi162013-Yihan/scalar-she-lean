module

public import SHE.AssignmentGapGain
public import SHE.PhysicalOrderedGaps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.PhysicalAssignmentGapScale
open Set MeasureTheory Real GaussianAssignmentBlocks GaussianFreshAssignments
  AssignmentGapPartition AllocatedAssignmentKernel CoveredHistoryGeometry
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays
open scoped BigOperators
open Classical
variable {k m : ℕ}

def leafPrefactor (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) : ℝ :=
  if block cs j.succ=[] then Q.holder else
    (2:ℝ)^((block cs j.succ).length-1)*Q.holder*
      (ProfileVariance.upperConstant*(Q.lower/2))^(Q.exponent/2)

def prefactor (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    (A0 : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^(block cs 0).length*A0*(n:ℝ)^(block cs 0).length*∏ j,leafPrefactor Q cs j

def leafGain (cs : List (Fin k×Fin (m+1))) (a : ℝ) (age : Fin m→ℝ) (d : Fin k→ℝ) (j : Fin m) : ℝ :=
  if h : block cs j.succ=[] then (age j)^a else (d (MinimumGapChoice.choose d (block cs j.succ) h))^a

def plainFactor (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    (d age : Fin k→ℝ) (A0 ν : ℝ) (n : ℕ) : ℝ :=
  VectorPhysicalRoot.scale cs 0 (fun _=>0) d A0 ν (Q.lower/2) n*
    ∏ j,NativeAssignedLeafMoments.leafScale Q cs j.succ (fun _=>0) d (age j)
      (fun h=>MinimumGapChoice.blockChoice (fun _=>0) d cs j.succ h)

theorem fullGain_eq (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) (age : Fin m→ℝ) :
    gain cs ν a d*emptyGain cs a age=
      (∏ j : Fin (block cs 0).length,min 1 (ν*(d ((block cs 0).get j))^(1/4:ℝ)))*
        ∏ j,leafGain cs a age d j := by
  rw [gain_eq_root_rough]
  unfold emptyGain
  rw [mul_assoc,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hb : block cs j.succ=[] <;> simp only [leafGain,hb,dite_true,dite_false,ite_true,ite_false,one_mul,mul_one]

theorem plainFactor_eq (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    (d age : Fin k→ℝ) (A0 ν : ℝ) (n : ℕ) :
    plainFactor Q cs d age A0 ν n=prefactor Q cs A0 n*
      gain cs (ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))) (Q.exponent/4) d*
        emptyGain cs (Q.exponent/4) age := by
  have hl (j : Fin k) :
      NativeAssignedLeafMoments.leafScale Q cs j.succ (fun _=>0) d (age j)
        (fun h=>MinimumGapChoice.blockChoice (fun _=>0) d cs j.succ h)=
          leafPrefactor Q cs j*leafGain cs (Q.exponent/4) age d j := by
    unfold NativeAssignedLeafMoments.leafScale leafPrefactor leafGain MinimumGapChoice.blockChoice
    split_ifs <;> simp only [sub_zero]
  rw [plainFactor]
  simp_rw [hl]
  rw [Finset.prod_mul_distrib]
  have hr : VectorPhysicalRoot.scale cs 0 (fun _=>0) d A0 ν (Q.lower/2) n=
      ((2:ℝ)^(block cs 0).length*A0*(n:ℝ)^(block cs 0).length)*
        (∏ j : Fin (block cs 0).length,min 1 ((ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2)))*
          (d ((block cs 0).get j))^(1/4:ℝ))) := by
    simp only [VectorPhysicalRoot.scale,sub_zero]
  rw [hr]
  calc
    _ = prefactor Q cs A0 n*
        ((∏ j : Fin (block cs 0).length,min 1 ((ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2)))*
          (d ((block cs 0).get j))^(1/4:ℝ)))*∏ j,leafGain cs (Q.exponent/4) age d j) := by
      unfold prefactor
      ring
    _ = _ := by rw [←fullGain_eq];ring

theorem prefactor_nonneg (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    {A0 : ℝ} (hA0 : 0≤A0) (n : ℕ) : 0≤prefactor Q cs A0 n := by
  unfold prefactor
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  unfold leafPrefactor
  split_ifs
  · exact Q.holder_nonneg
  · exact mul_nonneg (mul_nonneg (by positivity) Q.holder_nonneg)
      (Real.rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le
        (div_nonneg Q.lower_pos.le (by norm_num))) _)

theorem rootScale_lift (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    (lo hi : Fin (k+1)→ℝ) (A0 ν : ℝ) (n : ℕ) :
    VectorPhysicalRoot.scale (liftChoices cs) 0 lo hi A0 ν (Q.lower/2) n=
      VectorPhysicalRoot.scale cs 0 (fun _=>0) (fun j=>hi j.succ-lo j.succ) A0 ν (Q.lower/2) n := by
  have hp (is : List (Fin k)) (f : Fin (k+1)→ℝ) :
      (∏ j : Fin (is.map Fin.succ).length,f ((is.map Fin.succ).get j))=
        ∏ j : Fin is.length,f (is.get j).succ := by
    calc
      _ = ((is.map Fin.succ).map f).prod := by
        simpa only [List.get_eq_getElem] using Fin.prod_univ_fun_getElem (is.map Fin.succ) f
      _ = (is.map (fun i=>f i.succ)).prod := by simp only [List.map_map,Function.comp_def]
      _ = _ := by
        symm
        simpa only [List.get_eq_getElem] using Fin.prod_univ_fun_getElem is (fun i=>f i.succ)
  unfold VectorPhysicalRoot.scale
  rw [block_lift]
  have hh := hp (block cs 0) (fun i=>min 1 (ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))*
    (hi i-lo i)^(1/4:ℝ)))
  simpa only [List.length_map,sub_zero] using congrArg
    (fun z : ℝ=>((2:ℝ)^(block cs 0).length*A0*(n:ℝ)^(block cs 0).length)*z) hh

theorem minGap_lift (cs : List (Fin k×Fin (k+1))) (lo hi : Fin (k+1)→ℝ)
    (j : Fin k) (h : block (liftChoices cs) j.succ≠[]) (h' : block cs j.succ≠[]) :
    hi (MinimumGapChoice.blockChoice lo hi (liftChoices cs) j.succ h)-
      lo (MinimumGapChoice.blockChoice lo hi (liftChoices cs) j.succ h)=
      (hi (MinimumGapChoice.choose (fun i=>hi i.succ-lo i.succ) (block cs j.succ) h').succ-
        lo (MinimumGapChoice.choose (fun i=>hi i.succ-lo i.succ) (block cs j.succ) h').succ) := by
  unfold MinimumGapChoice.blockChoice
  have hm : (block cs j.succ).map Fin.succ≠[] := by simpa only [block_lift] using h
  have he := MinimumGapChoice.choose_map (fun i=>hi i-lo i) Fin.succ (block cs j.succ) h' hm
  simpa only [block_lift] using congrArg (fun i=>hi i-lo i) he

theorem leafScale_lift (Q : CanonicalCovariance.ProfileParameters) (cs : List (Fin k×Fin (k+1)))
    (lo hi : Fin (k+1)→ℝ) (age : ℝ) (j : Fin k) :
    NativeAssignedLeafMoments.leafScale Q (liftChoices cs) j.succ lo hi age
      (fun h=>MinimumGapChoice.blockChoice lo hi (liftChoices cs) j.succ h)=
    NativeAssignedLeafMoments.leafScale Q cs j.succ (fun _=>0) (fun i=>hi i.succ-lo i.succ) age
      (fun h=>MinimumGapChoice.blockChoice (fun _=>0) (fun i=>hi i.succ-lo i.succ) cs j.succ h) := by
  by_cases hb : block cs j.succ=[]
  · have hb' : block (liftChoices cs) j.succ=[] := by rw [block_lift,hb,List.map_nil]
    simp only [NativeAssignedLeafMoments.leafScale,hb,hb',dite_true]
  · have hb' : block (liftChoices cs) j.succ≠[] := by
      intro he
      have hh := congrArg List.length he
      rw [block_lift,List.length_map,List.length_nil] at hh
      exact hb (List.length_eq_zero_iff.mp hh)
    have hlen : (block (liftChoices cs) j.succ).length=(block cs j.succ).length := by
      rw [block_lift,List.length_map]
    simp only [NativeAssignedLeafMoments.leafScale,hb,hb',dite_false]
    rw [hlen,minGap_lift cs lo hi j hb' hb]
    simp only [MinimumGapChoice.blockChoice,sub_zero]

variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- The actual sharp physical time factor is exactly a deterministic
prefactor times the numeric assignment gain on its original gaps. -/
theorem physical_factor_eq (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (k : ℕ) (p : History X k) (q A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) :
    SharpWordTimeScale.factor L Q k p q cs A0 ν=
      prefactor Q cs A0 n*
        gain cs (ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))) (Q.exponent/4)
          (fun j=>upper L k p j-lower L k p j)*
        emptyGain cs (Q.exponent/4) (fun j=>CoveredControlledLaw.targets L k p (leafIndex k (fun i=>i) j)) := by
  unfold SharpWordTimeScale.factor PhysicalWordTimeScale.factor SharpWordTimeScale.chosen
  rw [rootScale_lift]
  simp_rw [leafScale_lift]
  have hh := plainFactor_eq Q cs (fun j=>upper L k p j-lower L k p j)
    (fun j=>CoveredControlledLaw.targets L k p (leafIndex k (fun i=>i) j)) A0 ν n
  simpa only [plainFactor,upperWith,lowerWith,Fin.cons_succ] using hh

end SHE.PhysicalAssignmentGapScale
