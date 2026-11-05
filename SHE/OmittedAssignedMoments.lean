module

public import SHE.FullResidualAssignedAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.OmittedAssignedMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance omittedAssignedMoments_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

theorem omit_product (j0 : Fin m) (f : Fin m→ℝ) :
    (∏ j,if j=j0 then 1 else f j)=∏ j∈Finset.univ.erase j0,f j := by
  rw [←Finset.prod_erase_mul Finset.univ (fun j=>if j=j0 then 1 else f j) (Finset.mem_univ j0)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

def oldScores (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (x : (Fin r→State n)×State n) : ℝ := ∏ j,secondScore (A j) (D j) (x.1 j)

def word (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (a : ℝ→ℝ) (F : State d→ℝ)
    (mean : Ω→State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (z : Ω×((Fin r→State n)×State n)) : ℝ :=
  oldScores A D z.2*VectorControlledRoot.value choices 0 F (mean z.1) g z.2*
    ∏ j∈Finset.univ.erase j0,ControlledAssignedLeaf.leaf choices j.succ a (mean z.1)
      (leaf j) (baseline j) z.2

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (b : ℕ) (C0 : ℝ) : ℝ :=
  GaussianAudit.secondScoreMoment (b*(m+2))^r+ControlledAssignedRoot.constant (b*(m+2)) choices 0+
    ∑ j : Fin m,if j=j0 then 1 else OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ

/-- Omitting a baseline leaf keeps every original old Gaussian score,
root clip and remaining rough block. No fictitious moment or age gain is
assigned to the erased factor. -/
theorem joint_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (hm : Measurable mean) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup) (j0 : Fin m)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (C0 : ℝ) (hC0 : 0≤C0)
    (hoffset : ∀ j,j≠j0→Integrable (fun ω=>|mean ω (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
    let νG := (Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B)
    let W := word A D choices j0 P.coefficient F mean g leaf
      (fun j=>ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun z=>|W z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|W z|^(2*b) ∂μ.prod νG)≤constant P r m choices j0 b C0*
        ((∏ j,scoreVariance (A j) (D j))*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi
            (target (leaf j)) (chosen j))^(2*b) := by
  classical
  intro A B νG W
  let Score := fun z : Ω×((Fin r→State n)×State n)=>oldScores A D z.2
  let Root := fun z : Ω×((Fin r→State n)×State n)=>VectorControlledRoot.value choices 0 F (mean z.1) g z.2
  let Leaf := fun j : Fin m=>fun z : Ω×((Fin r→State n)×State n)=>
    if j=j0 then 1 else ControlledAssignedLeaf.leaf choices j.succ P.coefficient (mean z.1)
      (leaf j) (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) z.2
  let ls := fun j : Fin m=>if j=j0 then 1 else NativeAssignedLeafMoments.leafScale P choices j.succ
    lo hi (target (leaf j)) (chosen j)
  let lc := fun j : Fin m=>if j=j0 then 1 else OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d0)
    (fun p=>⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d0 p).1,
      (referenceProfile_bounds P Λ u d0 p).2⟩) (lo j) (hi j)
  have hSm : Measurable Score := by
    dsimp only [Score,oldScores]
    apply Finset.measurable_prod Finset.univ
    intro j _
    exact (factor_measurable true (A j) (D j)).comp ((measurable_pi_apply j).comp measurable_snd.fst)
  have hRm : Measurable Root := ParametricAssignedMoments.root_measurable choices 0 F hFm mean hm g
  have hLm (j : Fin m) : Measurable (Leaf j) := by
    by_cases hj : j=j0
    · simpa only [Leaf,ite_eq_left hj] using (measurable_const (a:=(1:ℝ)) : Measurable (fun _ : Ω×((Fin r→State n)×State n)=>(1:ℝ)))
    · simpa only [Leaf,ite_eq_right hj] using ParametricAssignedMoments.leaf_measurable choices j.succ
        P.coefficient P.measurable mean hm (leaf j) (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
  have hOld := OldIntervalScoreMoments.product_even_moment A hA D hD (b*(m+2))
  have hs0 : Integrable (fun x : (Fin r→State n)×State n=>|oldScores A D x|^(2*(b*(m+2)))) νG :=
    hOld.1.comp_fst (multivariateGaussian 0 B)
  have hsb : (∫ x : (Fin r→State n)×State n,|oldScores A D x|^(2*(b*(m+2))) ∂νG)=
      GaussianAudit.secondScoreMoment (b*(m+2))^r*(∏ j,scoreVariance (A j) (D j))^(2*(b*(m+2))) := by
    have hh := integral_fun_fst
      (μ:=Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)))
      (ν:=multivariateGaussian (0 : State n) B)
      (fun y : Fin r→State n=>|∏ j,secondScore (A j) (D j) (y j)|^(2*(b*(m+2))))
    simpa only [νG,oldScores,probReal_univ,one_smul,hOld.2] using hh
  have hs := UniformFiberMoments.even_moment μ νG Score hSm (b*(m+2)) _
    (fun _=>hs0) (fun _=>hsb.le)
  have hr := ParametricAssignedMoments.root_even_moment μ P Λ u d0 lo hi σ target center hσ hσ1 hages
    (fun j=>hq.trans (hlo j)) hlohi hstop B mean hm g choices hnd 0 F hFm hA0 hν hf hfb
    (b*(m+2)) (Nat.mul_pos hb0 (by omega))
  have hl (j : Fin m) : Integrable (fun z=>|Leaf j z|^(2*(b*(m+2)))) (μ.prod νG) ∧
      (∫ z,|Leaf j z|^(2*(b*(m+2))) ∂μ.prod νG)≤lc j*(ls j)^(2*(b*(m+2))) := by
    by_cases hj : j=j0
    · simp only [Leaf,lc,ls,ite_eq_left hj,abs_one,one_pow,mul_one]
      exact ⟨integrable_const _,by simp⟩
    · simpa only [Leaf,lc,ls,ite_eq_right hj] using OffsetAssignedLeafMoments.even_moment μ P Λ u d0 θ
        σ target center hσ hσ1 hages hq lo hi hlo hlohi hstop hdisjoint mean hm (leaf j) (hnative j) (ht j)
        choices hnd j.succ (chosen j) (hchosen j) (b*(m+2)) C0 (hoffset j hj)
  have hls (j : Fin m) : 0≤ls j := by
    dsimp only [ls]
    split_ifs with hj
    · positivity
    · unfold NativeAssignedLeafMoments.leafScale
      split_ifs
      · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
          (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
          (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  have hlc (j : Fin m) : 0≤lc j := by
    dsimp only [lc]
    split_ifs
    · positivity
    · exact OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ
  simp only [←Nat.mul_assoc] at hs hr hl
  have hh := DependentWordMoments.word_even_moment (μ.prod νG) Score Root Leaf hSm hRm hLm
    (∏ j,scoreVariance (A j) (D j)) (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d) ls
    (Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j)))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j=>(hlohi j).le) hA0 hν d) hls
    _ _ lc (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _)
    (ControlledAssignedRoot.constant_nonneg _ _ _) hlc b hs.1 hr.1 (fun j=>(hl j).1) hs.2 hr.2 (fun j=>(hl j).2)
  have hprod (z : Ω×((Fin r→State n)×State n)) :
      (∏ j,Leaf j z)=∏ j∈Finset.univ.erase j0,ControlledAssignedLeaf.leaf choices j.succ
        P.coefficient (mean z.1) (leaf j) (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) z.2 :=
    omit_product j0 _
  simp_rw [hprod] at hh
  rw [omit_product j0] at hh
  exact hh

end SHE.OmittedAssignedMoments
