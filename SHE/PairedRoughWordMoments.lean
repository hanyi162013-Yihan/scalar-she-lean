module

public import SHE.PhysicalNormalizedAssignedPair
public import SHE.PhysicalNormalizedEmptyLeaf
public import SHE.TwoProfileAssignedFiber
public import SHE.NoFreshAssignedMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.PairedRoughWordMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier
  GaussianDependentScores MeasurableGaussianScores OffsetAssignedLeafMoments
open scoped BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
local instance pairedRoughWordMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n r m k : ℕ}

def source (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r×Fin k)) (factor : Fin k)
    (χ : ℝ) (newMean oldMean : State n) (i : Fin n) (newBaseline oldBaseline : ℝ) : ℝ :=
  if block choices factor=[] then
    NormalizedPairedLeaf.source P.holder P.exponent χ (newMean i) (oldMean i) newBaseline oldBaseline
  else |newMean i-oldMean i|^χ

def value (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r×Fin k)) (factor : Fin k)
    (χ : ℝ) (newMean oldMean : State n) (i : Fin n) (newBaseline oldBaseline : ℝ)
    (x : (Fin r→State n)×State n) : ℝ :=
  NormalizedScalarMoment.value
    (ControlledAssignedLeaf.leaf choices factor P.coefficient newMean i newBaseline x-
      ControlledAssignedLeaf.leaf choices factor P.coefficient oldMean i oldBaseline x)
    (source P choices factor χ newMean oldMean i newBaseline oldBaseline)

def pairScale (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r×Fin k)) (factor : Fin k)
    (χ : ℝ) (lo hi : Fin r→ℝ) (age : ℝ) (chosen : block choices factor≠[]→Fin r) : ℝ :=
  if h : block choices factor=[] then (P.holder*age^(P.exponent/4))^(1-χ/P.exponent)
  else (2:ℝ)^((block choices factor).length)*P.holder*(ProfileVariance.upperConstant*(P.lower/2))^((P.exponent-χ)/2)*
    (hi (chosen h)-lo (chosen h))^((P.exponent-χ)/4)

def pairConstant (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r×Fin k)) (factor : Fin k)
    (χ : ℝ) (p : ℕ) (C0 : ℝ) : ℝ :=
  if block choices factor=[] then 1+(2:ℝ)^(2*p-1)*(leafConstant P p C0 choices factor+leafConstant P p C0 choices factor)
  else GaussianAudit.gaussianAbsMoment (((2*p:ℕ):ℝ)*(P.exponent-χ))

def constant (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (χ : ℝ) (b : ℕ) (C0 : ℝ) : ℝ :=
  GaussianAudit.secondScoreMoment (b*(m+2))^r+ControlledAssignedRoot.constant (b*(m+2)) choices 0+
    ∑j,if j=j0 then pairConstant P choices j0.succ χ (b*(m+2)) C0
      else leafConstant P (b*(m+2)) C0 choices j.succ

/-- FULL actual dependent product with exactly one rough factor paired.
The distinguished current source has been removed first. All other
leaves retain their chosen endpoint means/baselines under one common
future law; every original old score/root clip remains explicit. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ ηOld ηNew : ℝ) (η : Fin m→ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (q : ℝ) (hq : 0≤q) (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j)
    (hlohi : ∀ j,lo j<hi j) (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j)).range)
    (newMean oldMean rootMean : State n) (leafMean : Fin m→State n)
    (g : Fin 1→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (j0 : Fin m) (F : State 1→ℝ) (hFm : Measurable F) {A0 ν χ C0 : ℝ}
    (hA0 : 0≤A0) (hν : 0≤ν) (hχ : 0≤χ) (hχβ : χ≤P.exponent) (hC0 : 0≤C0)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b)
    (hoff : ∀ j,|leafMean j (leaf j)-ControlledProfile.mean Λ u d
      (η j,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)≤
        C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2))
    (hOld : |oldMean (leaf j0)-ControlledProfile.mean Λ u d
      (ηOld,(target (leaf j0),center (leaf j0)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)≤
        C0*(target (leaf j0))^((b*(m+2):ℕ)*P.exponent/2))
    (hNew : |newMean (leaf j0)-ControlledProfile.mean Λ u d
      (ηNew,(target (leaf j0),center (leaf j0)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)≤
        C0*(target (leaf j0))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A : Fin r→Matrix (Fin n) (Fin n) ℝ:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B : Matrix (Fin n) (Fin n) ℝ:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let μ : Measure ((Fin r→State n)×State n):=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let Root : ((Fin r→State n)×State n)→ℝ:=VectorControlledRoot.value choices 0 F rootMean g
    let Pair : ((Fin r→State n)×State n)→ℝ:=value P choices j0.succ χ newMean oldMean (leaf j0)
      (ControlledProfile.profile P Λ u d (ηNew,(target (leaf j0),center (leaf j0))))
      (ControlledProfile.profile P Λ u d (ηOld,(target (leaf j0),center (leaf j0))))
    let Leaf : Fin m→((Fin r→State n)×State n)→ℝ:=fun j x=>if j=j0 then Pair x else ControlledAssignedLeaf.leaf choices j.succ P.coefficient (leafMean j) (leaf j)
      (ControlledProfile.profile P Λ u d (η j,(target (leaf j),center (leaf j)))) x
    let LS:=fun j=>if j=j0 then pairScale P choices j0.succ χ lo hi (target (leaf j0)) (chosen j0)
      else NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)
    let CL:=fun j=>if j=j0 then pairConstant P choices j0.succ χ (b*(m+2)) C0
      else leafConstant P (b*(m+2)) C0 choices j.succ
    let W : ((Fin r→State n)×State n)→ℝ:=fun x=>(∏j,secondScore (A j) (D j) (x.1 j))*Root x*∏j,Leaf j x
    let S:=(∏j,scoreVariance (A j) (D j))*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1*∏j,LS j
    let C:=constant P choices j0 χ b C0
    Integrable (fun x=>|W x|^(2*b)) μ ∧ (∫x,|W x|^(2*b) ∂μ)≤C*S^(2*b) ∧ |∫x,W x ∂μ|^(2*b)≤C*S^(2*b) := by
  intro A B μ Root Pair Leaf LS CL W S C
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
  have hRm : Measurable Root:=VectorControlledRoot.value_measurable choices 0 F hFm rootMean g
  have hPm : Measurable Pair:=NormalizedScalarMoment.measurable _ _
    ((ControlledAssignedLeaf.leaf_measurable choices j0.succ P.coefficient P.measurable newMean (leaf j0) _).sub
      (ControlledAssignedLeaf.leaf_measurable choices j0.succ P.coefficient P.measurable oldMean (leaf j0) _)) measurable_const
  have hLm (j : Fin m) : Measurable (Leaf j):=by
    by_cases hj : j=j0
    · simpa only [Leaf,hj,ite_true] using hPm
    · simpa only [Leaf,hj,ite_false] using ControlledAssignedLeaf.leaf_measurable choices j.succ
        P.coefficient P.measurable (leafMean j) (leaf j) (ControlledProfile.profile P Λ u d (η j,(target (leaf j),center (leaf j))))
  have hs0:=OldIntervalScoreMoments.product_even_moment A hA D hD (b*(m+2))
  have hmap := (measurePreserving_fst (μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))
    (ν:=multivariateGaussian (0:State n) B)).hasLaw
  have hs : Integrable (fun x=>|Score x|^(2*(b*(m+2)))) μ ∧
      (∫x,|Score x|^(2*(b*(m+2))) ∂μ)≤
        GaussianAudit.secondScoreMoment (b*(m+2))^r*(∏j,scoreVariance (A j) (D j))^(2*(b*(m+2))) := by
    refine ⟨by convert! hmap.integrable_comp hs0.1 using 1,?_⟩
    exact le_of_eq ((hmap.integral_comp hs0.1.aestronglyMeasurable).trans hs0.2)
  have hr:=WindowAssignedFactors.root_even_moment P Λ u d lo hi σ target center hσ hσ1 hages
    (fun j=>hq.trans (hlo j)) hlohi hstop B rootMean g choices hnd 0 F hA0 hν hf hfb (b*(m+2)) hp
  have hPair : Integrable (fun x=>|Pair x|^(2*(b*(m+2)))) μ ∧
      (∫x,|Pair x|^(2*(b*(m+2))) ∂μ)≤pairConstant P choices j0.succ χ (b*(m+2)) C0*
        (pairScale P choices j0.succ χ lo hi (target (leaf j0)) (chosen j0))^(2*(b*(m+2))) := by
    by_cases hb : block choices j0.succ=[]
    · have hh:=PhysicalNormalizedEmptyLeaf.even_moment P Λ u d θ ηOld ηNew σ target center hσ hσ1 hages hq
        lo hi hlo hlohi hstop hdisjoint newMean oldMean (leaf j0) (hnative j0) (ht j0) choices hnd j0.succ hb
        (b*(m+2)) hχ hχβ hC0 hC0 hOld hNew
      dsimp only at hh
      simp only [Pair,value,source,hb,ite_true,NormalizedScalarMoment.value,
        ControlledAssignedLeaf.leaf_empty choices j0.succ hb,pairConstant,pairScale]
      exact hh
    · let j:=chosen j0 hb
      have hh:=PhysicalNormalizedAssignedPair.even_moment P σ target center hσ hσ1 hages _
        (referenceProfile_measurable P Λ u d) hcref lo hi (fun j=>hq.trans (hlo j)) hlohi hstop B choices hnd
        j0.succ j (hchosen j0 hb) (leaf j0) newMean oldMean
        (ControlledProfile.profile P Λ u d (ηNew,(target (leaf j0),center (leaf j0))))
        (ControlledProfile.profile P Λ u d (ηOld,(target (leaf j0),center (leaf j0)))) hχ hχβ (b*(m+2)) hp
      dsimp only at hh
      simpa only [Pair,value,source,hb,ite_false,dite_false,pairConstant,pairScale,j] using hh
  have hl (j : Fin m) : Integrable (fun x=>|Leaf j x|^(2*(b*(m+2)))) μ ∧
      (∫x,|Leaf j x|^(2*(b*(m+2))) ∂μ)≤CL j*(LS j)^(2*(b*(m+2))) := by
    by_cases hj : j=j0
    · subst j
      simpa only [Leaf,LS,CL,ite_true] using hPair
    · have hh:=TwoProfileAssignedFiber.endpoint_moment P Λ u d θ (η j) σ target center
        hσ hσ1 hages hq lo hi hlo hlohi hstop hdisjoint (leafMean j) (leaf j) (hnative j) (ht j)
        choices hnd j.succ (chosen j) (hchosen j) (b*(m+2)) C0 (hoff j)
      simpa only [Leaf,LS,CL,hj,ite_false] using hh
  have hLS (j : Fin m) : 0≤LS j := by
    by_cases hj : j=j0
    · subst j
      simp only [LS,ite_true,pairScale]
      split_ifs
      · exact rpow_nonneg (mul_nonneg P.holder_nonneg (rpow_nonneg (ht j0).1.le _)) _
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
          (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
          (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
    · simp only [LS,hj,ite_false,NativeAssignedLeafMoments.leafScale]
      split_ifs
      · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
          (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
          (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  have hCL (j : Fin m) : 0≤CL j := by
    by_cases hj : j=j0
    · subst j
      simp only [CL,ite_true,pairConstant]
      split_ifs
      · exact add_nonneg (by norm_num) (mul_nonneg (by positivity)
          (add_nonneg (leafConstant_nonneg P _ hC0 choices _) (leafConstant_nonneg P _ hC0 choices _)))
      · exact GaussianAudit.gaussianAbsMoment_nonneg _
    · simp only [CL,hj,ite_false]
      exact leafConstant_nonneg P _ hC0 choices _
  simp only [←Nat.mul_assoc] at hs hr hl
  have hh:=DependentWordMoments.word_even_moment μ Score Root Leaf hSm hRm hLm
    (∏j,scoreVariance (A j) (D j)) (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1) LS
    (Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j)))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j=>(hlohi j).le) hA0 hν 1)
    hLS _ _ CL (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _)
    (ControlledAssignedRoot.constant_nonneg _ _ _) hCL
    b hs.1 hr.1 (fun j=>(hl j).1) hs.2 hr.2 (fun j=>(hl j).2)
  have hWm : Measurable W:=(hSm.mul hRm).mul (Finset.measurable_prod Finset.univ (fun j _=>hLm j))
  have hiPow : Integrable (fun x=>‖W x‖^(2*b)) μ:=by simpa only [Real.norm_eq_abs] using hh.1
  have hiOne:=integrable_norm_pow_of_le hWm.aestronglyMeasurable (by omega : 1≤2*b) hiPow
  have hiW : Integrable W μ:=(integrable_norm_iff hWm.aestronglyMeasurable).mp (by simpa only [pow_one] using hiOne)
  refine ⟨hh.1,hh.2,?_⟩
  have hj:=SHE.even_moment_average_le μ b hiW (by simpa only [pow_abs_two_mul] using hh.1)
  have hj' : |∫x,W x ∂μ|^(2*b)≤∫x,|W x|^(2*b) ∂μ := by simpa only [pow_abs_two_mul] using hj
  exact hj'.trans hh.2

end SHE.PairedRoughWordMoments
