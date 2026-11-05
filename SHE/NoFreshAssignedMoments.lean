module

public import SHE.OffsetAssignedLeafMoments
public import SHE.GaussianJointScoreMoments
public import SHE.DependentWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.NoFreshAssignedMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance noFreshAssignedMoments_periodPos : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r × Fin (m+1))) (b : ℕ) (C0 : ℝ) : ℝ :=
  GaussianAudit.secondScoreMoment (b*(m+2))^r+
    ControlledAssignedRoot.constant (b*(m+2)) choices 0+
      ∑ j : Fin m,OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ

/-- The genuine old Gaussian scores with no fresh mark. In an actual
remainder the newest stopped coordinate can remain outside the future
expectation; no artificial fresh first or second score is introduced. -/
def word (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (choices : List (Fin r × Fin (m+1)))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : Ω → State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ)
    (z : Ω × ((Fin r → State n) × State n)) : ℝ :=
  (∏ j,secondScore (A j) (D j) (z.2.1 j))*
    VectorControlledRoot.value choices 0 F (mean z.1) g z.2*
      ∏ j,ControlledAssignedLeaf.leaf choices j.succ a (mean z.1) (leaf j) (baseline j) z.2

theorem word_measurable (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r → State n) (choices : List (Fin r × Fin (m+1)))
    (a : ℝ → ℝ) (ha : Measurable a) (F : State d → ℝ) (hF : Measurable F)
    (mean : Ω → State n) (hm : Measurable mean) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ) :
    Measurable (word A D choices a F mean g leaf baseline) := by
  have hs : Measurable (fun z : Ω×((Fin r→State n)×State n)=>
      ∏ j,secondScore (A j) (D j) (z.2.1 j)) := by
    apply Finset.measurable_prod
    intro j _
    exact (factor_measurable true (A j) (D j)).comp
      ((measurable_pi_apply j).comp measurable_snd.fst)
  exact (hs.mul (ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g)).mul
    (Finset.measurable_prod Finset.univ (fun j _=>
      ParametricAssignedMoments.leaf_measurable choices j.succ a ha mean hm (leaf j) (baseline j)))

/-- Collision-uniform actual old-score word moments, without a fresh
mark. The physical scales keep every old root clip and rough block,
including the full newest-leaf offset when its Gaussian coordinate is zero. -/
theorem joint_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0 ≤ q) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i,0 < σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    (lo hi : Fin r → ℝ) (hlo : ∀ j,q ≤ lo j) (hlohi : ∀ j,lo j < hi j)
    (hstop : ∀ j i,σ i ≤ lo j ∨ hi j ≤ σ i)
    (hdisjoint : ∀ j l,j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (mean : Ω → State n) (hm : Measurable mean) (D : Fin r → State n)
    (hD : ∀ j,D j ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (g : Fin d → Fin n) (leaf : Fin m → Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j) ∈ Ioc 0 P.horizon)
    (choices : List (Fin r × Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ ≠ [] → Fin r)
    (hchosen : ∀ j h,chosen j h ∈ block choices j.succ)
    (F : State d → ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j ≤ (block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (b : ℕ) (hb0 : 0 < b) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hoffset : ∀ j,Integrable (fun ω => |mean ω (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ) ≤ C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let W := word A D choices P.coefficient F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun z => |W z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|W z|^(2*b) ∂μ.prod νG) ≤ constant P r m choices b C0*
        ((∏ j,scoreVariance (A j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
            ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A B νG W
  let Score := fun z : Ω × ((Fin r → State n) × State n) =>
    ∏ j,secondScore (A j) (D j) (z.2.1 j)
  let Root := fun z : Ω × ((Fin r → State n) × State n) => VectorControlledRoot.value choices 0 F (mean z.1) g z.2
  let Leaf := fun j : Fin m => fun z : Ω × ((Fin r → State n) × State n) =>
    ControlledAssignedLeaf.leaf choices j.succ P.coefficient (mean z.1) (leaf j)
      (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) z.2
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d0)
    (fun p => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d0 p).1,
      (referenceProfile_bounds P Λ u d0 p).2⟩) (lo j) (hi j)
  have hSm : Measurable Score := by
    apply Finset.measurable_prod
    intro j _
    exact (factor_measurable true (A j) (D j)).comp
      ((measurable_pi_apply j).comp measurable_snd.fst)
  have hRm : Measurable Root := ParametricAssignedMoments.root_measurable choices 0 F hFm mean hm g
  have hLm (j : Fin m) : Measurable (Leaf j) := ParametricAssignedMoments.leaf_measurable choices j.succ
    P.coefficient P.measurable mean hm (leaf j) _
  have hs0:=OldIntervalScoreMoments.product_even_moment A hA D hD (b*(m+2))
  have hmap : HasLaw (fun z : Ω×((Fin r→State n)×State n)=>z.2.1)
      (Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))) (μ.prod νG):=
    (measurePreserving_fst (μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))
      (ν:=multivariateGaussian (0:State n) B)).hasLaw.fun_comp
        (measurePreserving_snd (μ:=μ) (ν:=νG)).hasLaw
  have hs : Integrable (fun z=>|Score z|^(2*(b*(m+2)))) (μ.prod νG) ∧
      (∫ z,|Score z|^(2*(b*(m+2))) ∂μ.prod νG)≤
        GaussianAudit.secondScoreMoment (b*(m+2))^r*
          (∏ j,scoreVariance (A j) (D j))^(2*(b*(m+2))):=by
    refine ⟨?_,?_⟩
    · convert! hmap.integrable_comp hs0.1 using 1
    · have he:=hmap.integral_comp hs0.1.aestronglyMeasurable
      exact le_of_eq (he.trans hs0.2)
  have hr := ParametricAssignedMoments.root_even_moment μ P Λ u d0 lo hi σ target center hσ hσ1 hages
    (fun j => hq.trans (hlo j)) hlohi hstop B mean hm g choices hnd 0 F hFm hA0 hν hf hfb
    (b*(m+2)) (Nat.mul_pos hb0 (by omega))
  have hl (j : Fin m) := OffsetAssignedLeafMoments.even_moment μ P Λ u d0 θ σ target center hσ hσ1 hages
    hq lo hi hlo hlohi hstop hdisjoint mean hm (leaf j) (hnative j) (ht j) choices hnd j.succ
    (chosen j) (hchosen j) (b*(m+2)) C0 (hoffset j)
  have hLS (j : Fin m) : 0 ≤ NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs
    · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
        (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
        (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  simp only [←Nat.mul_assoc] at hs hr hl
  exact DependentWordMoments.word_even_moment (μ.prod νG) Score Root Leaf hSm hRm hLm
    (∏ j,scoreVariance (A j) (D j))
    (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d)
    (fun j => NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))
    (Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j)))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j => (hlohi j).le) hA0 hν d) hLS
    _ _ _ (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _)
    (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j => OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ)
    b hs.1 hr.1 (fun j => (hl j).1) hs.2 hr.2 (fun j => (hl j).2)

end SHE.NoFreshAssignedMoments
