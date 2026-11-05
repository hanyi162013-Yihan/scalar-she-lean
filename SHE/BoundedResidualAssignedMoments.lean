module

public import SHE.BoundedAssignedLeaf
public import SHE.FullResidualAssignedMoments
public import SHE.GaussianJointScoreMoments
public import SHE.DependentWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.BoundedResidualAssignedMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance fullResidualAssignedMoments_periodPos : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n r m : ℕ}

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r × Fin (m+1))) (b : ℕ) (C0 : ℝ) : ℝ :=
  GaussianAudit.secondScoreMoment (b*(m+2))^r*productMomentConstant (b*(m+2))+
    ControlledAssignedRoot.constant (b*(m+2)) choices 0+
      ∑ j : Fin m,OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ

/-- A new mean or covariance score is carried by the full residual.
Every old fraction, centered leaf, root and baseline remains unchanged. -/
def word (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (choices : List (Fin r × Fin (m+1)))
    (a : ℝ → ℝ) (F : State 1 → ℝ) (mean : Ω → State n) (g : Fin 1 → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ)
    (z : Ω × ((Fin r → State n) × State n)) : ℝ :=
  scores second A D B E z.2*
    VectorControlledRoot.value choices 0 F (mean z.1) g z.2*
      ∏ j,ControlledAssignedLeaf.leaf choices j.succ a (mean z.1) (leaf j) (baseline j) z.2

theorem word_measurable (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r → State n) (B : Matrix (Fin n) (Fin n) ℝ) (E : State n)
    (choices : List (Fin r × Fin (m+1))) (a : ℝ → ℝ) (ha : Measurable a)
    (F : State 1 → ℝ) (hF : Measurable F) (mean : Ω → State n) (hm : Measurable mean)
    (g : Fin 1 → Fin n) (leaf : Fin m → Fin n) (baseline : Fin m → ℝ) :
    Measurable (word second A D B E choices a F mean g leaf baseline) :=
  (((scores_measurable second A D B E).comp measurable_snd).mul
    (ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g)).mul
      (Finset.measurable_prod Finset.univ (fun j _ =>
        ParametricAssignedMoments.leaf_measurable choices j.succ a ha mean hm (leaf j) (baseline j)))

/-- Collision-uniform Gaussian full-word moments use just the original
old intervals and one new score on their full positive residual. All
current mean dependence stays correlated with the entire word. -/
theorem joint_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2)
    (c : Domain→ℝ) (hc : Measurable c) (hcb : ∀ p,P.lower≤c p ∧ c p≤P.upper) (η : ℝ)
    (q : ℝ) (hq : 0 ≤ q) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i,0 < σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    (lo hi : Fin r → ℝ) (hlo : ∀ j,q ≤ lo j) (hlohi : ∀ j,lo j < hi j)
    (hstop : ∀ j i,σ i ≤ lo j ∨ hi j ≤ σ i)
    (hdisjoint : ∀ j l,j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (mean : Ω → State n) (hm : Measurable mean) (second : Bool) (D : Fin r → State n)
    (hD : ∀ j,D j ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E : State n) (hE : E ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d0 lo hi c) q)).range)
    (g : Fin 1 → Fin n) (leaf : Fin m → Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j) ∈ Ioc 0 P.horizon)
    (choices : List (Fin r × Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ ≠ [] → Fin r)
    (hchosen : ∀ j h,chosen j h ∈ block choices j.succ)
    (F : State 1 → ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j ≤ (block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (b : ℕ) (hb0 : 0 < b) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hoffset : ∀ j,Integrable (fun ω => |mean ω (leaf j)-ControlledProfile.mean Λ u d0
        (η,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ u d0 (η,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ) ≤ C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d0 lo hi c) q
    let νG := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let W := word second A D B E choices P.coefficient F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (η,(target (leaf j),center (leaf j))))
    Integrable (fun z => |W z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|W z|^(2*b) ∂μ.prod νG) ≤ constant P r m choices b C0*
        (((∏ j,scoreVariance (A j) (D j))*scale second B E)*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1*
            ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A B νG W
  let Score := fun z : Ω × ((Fin r → State n) × State n) => scores second A D B E z.2
  let Root := fun z : Ω × ((Fin r → State n) × State n) => VectorControlledRoot.value choices 0 F (mean z.1) g z.2
  let Leaf := fun j : Fin m => fun z : Ω × ((Fin r → State n) × State n) =>
    ControlledAssignedLeaf.leaf choices j.succ P.coefficient (mean z.1) (leaf j)
      (ControlledProfile.profile P Λ u d0 (η,(target (leaf j),center (leaf j)))) z.2
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d0)
    (fun p => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d0 p).1,
      (referenceProfile_bounds P Λ u d0 p).2⟩) (lo j) (hi j)
  have hB : B.PosSemidef := StoppedCovarianceSplit.covariance_posSemidef σ target center hages q
    (BoundedWindowDecomposition.residual_measurable P Λ u d0 lo hi c hc)
    (fun p=>⟨(half_pos P.lower_pos).le.trans
      (BoundedWindowDecomposition.residual_bounds P Λ u d0 lo hi hdisjoint c hcb p).1,
      (BoundedWindowDecomposition.residual_bounds P Λ u d0 lo hi hdisjoint c hcb p).2⟩)
  have hSm : Measurable Score := (scores_measurable second A D B E).comp measurable_snd
  have hRm : Measurable Root := ParametricAssignedMoments.root_measurable choices 0 F hFm mean hm g
  have hLm (j : Fin m) : Measurable (Leaf j) := ParametricAssignedMoments.leaf_measurable choices j.succ
    P.coefficient P.measurable mean hm (leaf j) _
  have hs0 := scores_even_moment second A hA D hD B hB E hE (b*(m+2))
  have hs := UniformFiberMoments.even_moment μ νG Score hSm (b*(m+2))
    ((GaussianAudit.secondScoreMoment (b*(m+2))^r*productMomentConstant (b*(m+2)))*
      ((∏ j,scoreVariance (A j) (D j))*scale second B E)^(2*(b*(m+2))))
    (fun _ => hs0.1) (fun _ => hs0.2)
  have hr := ParametricAssignedMoments.root_even_moment μ P Λ u d0 lo hi σ target center hσ hσ1 hages
    (fun j => hq.trans (hlo j)) hlohi hstop B mean hm g choices hnd 0 F hFm hA0 hν hf hfb
    (b*(m+2)) (Nat.mul_pos hb0 (by omega))
  have hl (j : Fin m) := BoundedAssignedLeaf.even_moment μ P Λ u d0 c hc hcb η σ target center hσ hσ1 hages
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
    ((∏ j,scoreVariance (A j) (D j))*scale second B E)
    (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)
    (fun j => NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))
    (mul_nonneg (Finset.prod_nonneg (fun j _ => scoreVariance_nonneg (hA j) (hD j)))
      (scale_nonneg hB hE second))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j => (hlohi j).le) hA0 hν 1) hLS
    _ _ _ (mul_nonneg (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _) (productMomentConstant_nonneg _))
    (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j => OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ)
    b hs.1 hr.1 (fun j => (hl j).1) hs.2 hr.2 (fun j => (hl j).2)

end SHE.BoundedResidualAssignedMoments
