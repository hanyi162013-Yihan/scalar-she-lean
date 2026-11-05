module

public import SHE.OffsetAssignedLeafMoments
public import SHE.NativeFirstScoreAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.OffsetFirstScoreWordMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores NativeFirstScoreWordMoments
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r×Fin (m+1))) (b : ℕ) (C0 : ℝ) : ℝ :=
  productMomentConstant (b*(m+2))^r+ControlledAssignedRoot.constant (b*(m+2)) choices 0+
    ∑ j : Fin m,OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ

/-- A whole correlated Gaussian word needs only actual scalar
displacement moments of its current mean. Root jets, Gaussian scores,
suppressed assigned blocks and full-profile baselines are all estimated
here, rather than packaged as an assumed word-moment bound. -/
theorem joint_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (hm : Measurable mean) (second : Fin r→Bool) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (C0 : ℝ) (hC0 : 0≤C0)
    (hoffset : ∀ j,Integrable (fun ω => |mean ω (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let W := word P.coefficient second A D choices F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun z => |W z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|W z|^(2*b) ∂μ.prod νG)≤constant P r m choices b C0*
        ((∏ j,scale (second j) (A j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A B νG W
  let Score := fun z : Ω×((Fin r→State n)×State n) => GaussianFractionMixedMoments.value second A D z.2.1
  let Root := fun z : Ω×((Fin r→State n)×State n) => VectorControlledRoot.value choices 0 F (mean z.1) g z.2
  let Leaf := fun j : Fin m => fun z : Ω×((Fin r→State n)×State n) =>
    ControlledAssignedLeaf.leaf choices j.succ P.coefficient (mean z.1) (leaf j)
      (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) z.2
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d0)
    (fun p => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d0 p).1,
      (referenceProfile_bounds P Λ u d0 p).2⟩) (lo j) (hi j)
  have hSm : Measurable Score := (GaussianFractionMixedMoments.measurable_value second A D).comp measurable_snd.fst
  have hRm : Measurable Root := ParametricAssignedMoments.root_measurable choices 0 F hFm mean hm g
  have hLm (j : Fin m) : Measurable (Leaf j) := ParametricAssignedMoments.leaf_measurable choices j.succ
    P.coefficient P.measurable mean hm (leaf j) _
  have hs0 := GaussianFractionMixedMoments.residual_even_moment second A hA D hD B (b*(m+2))
  have hs := UniformFiberMoments.even_moment μ νG Score hSm (b*(m+2))
    (productMomentConstant (b*(m+2))^r*(∏ j,scale (second j) (A j) (D j))^(2*(b*(m+2))))
    (fun _ => hs0.1) (fun _ => hs0.2)
  have hr := ParametricAssignedMoments.root_even_moment μ P Λ u d0 lo hi σ target center hσ hσ1 hages
    (fun j => hq.trans (hlo j)) hlohi hstop B mean hm g choices hnd 0 F hFm hA0 hν hf hfb
    (b*(m+2)) (Nat.mul_pos hb0 (by omega))
  have hl (j : Fin m) := OffsetAssignedLeafMoments.even_moment μ P Λ u d0 θ σ target center hσ hσ1 hages
    hq lo hi hlo hlohi hstop hdisjoint mean hm (leaf j) (hnative j) (ht j) choices hnd j.succ
    (chosen j) (hchosen j) (b*(m+2)) C0 (hoffset j)
  have hLS (j : Fin m) : 0≤NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs
    · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
        (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
        (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  simp only [←Nat.mul_assoc] at hs hr hl
  exact DependentWordMoments.word_even_moment (μ.prod νG) Score Root Leaf hSm hRm hLm
    (∏ j,scale (second j) (A j) (D j))
    (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d)
    (fun j => NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))
    (Finset.prod_nonneg (fun j _ => scale_nonneg (hA j) (hD j) _))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j => (hlohi j).le) hA0 hν d) hLS
    _ _ _ (pow_nonneg (productMomentConstant_nonneg _) _) (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j => OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ)
    b hs.1 hr.1 (fun j => (hl j).1) hs.2 hr.2 (fun j => (hl j).2)

/-- Genuine Gaussian averaging preserves the same all-order moment bound. -/
theorem averaged_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (hm : Measurable mean) (second : Fin r→Bool) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (C0 : ℝ) (hC0 : 0≤C0)
    (hoffset : ∀ j,Integrable (fun ω => |mean ω (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let W := word P.coefficient second A D choices F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun ω => |∫ x,W (ω,x) ∂νG|^(2*b)) μ ∧
      (∫ ω,|∫ x,W (ω,x) ∂νG|^(2*b) ∂μ)≤constant P r m choices b C0*
        ((∏ j,scale (second j) (A j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A B νG W
  have hh := joint_even_moment μ P Λ u d0 θ q hq σ target center hσ hσ1 hages lo hi hlo hlohi hstop hdisjoint
    mean hm second D hD g leaf hnative ht choices hnd chosen hchosen F hFm hA0 hν hf hfb b hb0 C0 hC0 hoffset
  have hW : Measurable W := NativeFirstScoreWordMoments.word_measurable P.coefficient P.measurable second A D
    choices F hFm mean hm g leaf _
  have hi2b : Integrable (fun z => ‖W z‖^(2*b)) (μ.prod νG) := by
    simpa only [Real.norm_eq_abs] using hh.1
  have hi1 := integrable_norm_pow_of_le hW.aestronglyMeasurable (by omega : 1≤2*b) hi2b
  have hiW : Integrable W (μ.prod νG) := (integrable_norm_iff hW.aestronglyMeasurable).mp
    (by simpa only [pow_one] using hi1)
  have hj := UniformFiberMoments.average_even_moment μ νG W hiW b hh.1
  exact ⟨hj.1,hj.2.trans hh.2⟩

end SHE.OffsetFirstScoreWordMoments
