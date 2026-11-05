module

public import SHE.ScalarNormalizedRootPair
public import SHE.TwoProfileAssignedFiber
public import SHE.NoFreshAssignedMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.PairedRootWordMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier
  GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
local instance pairedRootWordMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n r m : ℕ}

/-- A FULL actual old-score assigned product with exactly the root slot
paired. Every other rough factor may come from EITHER endpoint and keeps
its OWN mean and baseline under the COMMON future Gaussian law. Current
input is normalized before this dependent Gaussian product estimate. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (η : Fin m→ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (q : ℝ) (hq : 0≤q) (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j)
    (hlohi : ∀ j,lo j<hi j) (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j)).range)
    (newMean oldMean : State n) (leafMean : Fin m→State n)
    (g : Fin 1→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State 1→ℝ) (hFm : Measurable F) {A0 ν χ C0 : ℝ}
    (hA0 : 0≤A0) (hν : 0≤ν) (hχ : 0≤χ) (hχ1 : χ≤1) (hC0 : 0≤C0)
    (hf : ContDiff ℝ ((block choices 0).length+1) F)
    (hfb : ∀ j,j≤(block choices 0).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b)
    (hoff : ∀ j,|leafMean j (leaf j)-ControlledProfile.mean Λ u d
      (η j,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)≤
        C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A : Fin r→Matrix (Fin n) (Fin n) ℝ:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B : Matrix (Fin n) (Fin n) ℝ:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let μ : Measure ((Fin r→State n)×State n):=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let source:=(min 1 (ν*‖GaussianCoordinates.projection g (newMean-oldMean)‖))^χ
    let Root : ((Fin r→State n)×State n)→ℝ:=fun x=>NormalizedScalarMoment.value
      (VectorControlledRoot.value choices 0 F newMean g x-VectorControlledRoot.value choices 0 F oldMean g x) source
    let Leaf : Fin m→((Fin r→State n)×State n)→ℝ:=fun j x=>ControlledAssignedLeaf.leaf choices j.succ P.coefficient (leafMean j) (leaf j)
      (ControlledProfile.profile P Λ u d (η j,(target (leaf j),center (leaf j)))) x
    let W : ((Fin r→State n)×State n)→ℝ:=fun x=>(∏ j,secondScore (A j) (D j) (x.1 j))*Root x*∏j,Leaf j x
    let S:=(∏ j,scoreVariance (A j) (D j))*(2*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)*
      ∏j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)
    Integrable (fun x=>|W x|^(2*b)) μ ∧
      (∫ x,|W x|^(2*b) ∂μ)≤NoFreshAssignedMoments.constant P r m choices b C0*S^(2*b) ∧
      |∫ x,W x ∂μ|^(2*b)≤NoFreshAssignedMoments.constant P r m choices b C0*S^(2*b) := by
  intro A B μ source Root Leaf W S
  let Score:=fun x : (Fin r→State n)×State n=>∏j,secondScore (A j) (D j) (x.1 j)
  have hcref (p : ControlledProfile.Domain) : 0≤referenceProfile P Λ u d p ∧ referenceProfile P Λ u d p≤P.lower/2 :=
    ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d p).1,
      (referenceProfile_bounds P Λ u d p).2⟩
  have hA (j : Fin r) : (A j).PosSemidef:=covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d) hcref (lo j) (hi j)
  have hp : 0<b*(m+2):=Nat.mul_pos hb0 (by omega)
  have hSm : Measurable Score:=Finset.measurable_prod Finset.univ (fun j _=>
    (MeasurableGaussianScores.secondScore_measurable (n:=n)).comp
      ((measurable_const.prodMk measurable_const).prodMk ((measurable_pi_apply j).comp measurable_fst)))
  have hRm : Measurable Root:=NormalizedScalarMoment.measurable _ _
    ((VectorControlledRoot.value_measurable choices 0 F hFm newMean g).sub
      (VectorControlledRoot.value_measurable choices 0 F hFm oldMean g)) measurable_const
  have hLm (j : Fin m) : Measurable (Leaf j):=ControlledAssignedLeaf.leaf_measurable choices j.succ
    P.coefficient P.measurable (leafMean j) (leaf j) _
  have hs0:=OldIntervalScoreMoments.product_even_moment A hA D hD (b*(m+2))
  have hmap := (measurePreserving_fst (μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))
    (ν:=multivariateGaussian (0:State n) B)).hasLaw
  have hs : Integrable (fun x=>|Score x|^(2*(b*(m+2)))) μ ∧
      (∫x,|Score x|^(2*(b*(m+2))) ∂μ)≤
        GaussianAudit.secondScoreMoment (b*(m+2))^r*(∏j,scoreVariance (A j) (D j))^(2*(b*(m+2))) := by
    refine ⟨by convert! hmap.integrable_comp hs0.1 using 1,?_⟩
    exact le_of_eq ((hmap.integral_comp hs0.1.aestronglyMeasurable).trans hs0.2)
  have hr:=ScalarNormalizedRootPair.even_moment σ target center hσ hσ1 hages _
    (referenceProfile_measurable P Λ u d) hcref lo hi (fun j=>hq.trans (hlo j)) hlohi hstop B
    choices hnd 0 g F hA0 hν hχ hχ1 hf hfb newMean oldMean (b*(m+2)) hp
  have hl (j : Fin m):=TwoProfileAssignedFiber.endpoint_moment P Λ u d θ (η j) σ target center
    hσ hσ1 hages hq lo hi hlo hlohi hstop hdisjoint (leafMean j) (leaf j) (hnative j) (ht j)
    choices hnd j.succ (chosen j) (hchosen j) (b*(m+2)) C0 (hoff j)
  have hLS (j : Fin m) : 0≤NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs
    · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
        (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
        (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  simp only [←Nat.mul_assoc] at hs hr hl
  have hh:=DependentWordMoments.word_even_moment μ Score Root Leaf hSm hRm hLm
    (∏j,scoreVariance (A j) (D j)) (2*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)
    (fun j=>NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))
    (Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j)))
    (mul_nonneg (by norm_num) (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j=>(hlohi j).le) hA0 hν 1))
    hLS _ _ _ (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _)
    (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j=>OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ)
    b hs.1 hr.1 (fun j=>(hl j).1) hs.2 hr.2 (fun j=>(hl j).2)
  have hWm : Measurable W:=(hSm.mul hRm).mul (Finset.measurable_prod Finset.univ (fun j _=>hLm j))
  have hiPow : Integrable (fun x=>‖W x‖^(2*b)) μ:=by simpa only [Real.norm_eq_abs] using hh.1
  have hiOne:=integrable_norm_pow_of_le hWm.aestronglyMeasurable (by omega : 1≤2*b) hiPow
  have hiW : Integrable W μ:=(integrable_norm_iff hWm.aestronglyMeasurable).mp (by simpa only [pow_one] using hiOne)
  refine ⟨hh.1,hh.2,?_⟩
  have hj:=SHE.even_moment_average_le μ b hiW (by simpa only [pow_abs_two_mul] using hh.1)
  have hj' : |∫x,W x ∂μ|^(2*b)≤∫x,|W x|^(2*b) ∂μ := by
    simpa only [pow_abs_two_mul] using hj
  exact hj'.trans hh.2

end SHE.PairedRootWordMoments
