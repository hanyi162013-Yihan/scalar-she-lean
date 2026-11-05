module

public import SHE.WindowAssignedFactors
public import SHE.GaussianFractionMixedMoments
public import SHE.DependentWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.WindowFirstScoreMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier ProfileVariance
  MeasurableGaussianScores GaussianDependentScores ProfileL2
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n d r m : ℕ}

def word (a : ℝ→ℝ) (second : Fin r→Bool)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ) (mean : State n)
    (rootCoordinates : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (x : (Fin r→State n)×State n) : ℝ :=
  GaussianFractionMixedMoments.value second A D x.1*
    VectorControlledRoot.value choices 0 F mean rootCoordinates x*
      (∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x)

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r×Fin (m+1))) (p : ℕ) : ℝ :=
  (productMomentConstant (p*(m+2)))^r+ControlledAssignedRoot.constant (p*(m+2)) choices 0+
    ∑ j : Fin m,WindowAssignedFactors.leafConstant P (p*(m+2)) choices j.succ

/-- Full actual assigned Gaussian word in the q-window with a terminal
FIRST score and all prior SECOND scores. Current means are arbitrary:
unassigned leaves retain explicit full-profile displacement scales.
Every old root clip and assigned rough gap stays multiplicative; no
score/root/rough-factor independence is used in Hölder. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u dir : CircleL2) (θ : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (second : Fin r→Bool) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u dir) lo hi j)).range)
    (mean : State n) (rootCoordinates : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j))
    (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hfm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (p : ℕ) (hp : 0<p) :
    let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
    let B := ControlledFixedReserve.covariance P Λ u dir (fixedProfile P Λ u dir lo hi)
      σ target center q θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)
    let T := word P.coefficient second A D choices F mean rootCoordinates leaf
      (fun j => ControlledProfile.profile P Λ u dir (θ,(target (leaf j),center (leaf j))))
    Integrable (fun x => |T x|^(2*p)) μ ∧
      (∫ x,|T x|^(2*p) ∂μ)≤constant P r m choices p*
      ((∏ j,scale (second j) (A j) (D j))*
      VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
      (∏ j,WindowAssignedFactors.leafScale P choices j.succ lo hi (target (leaf j)) (mean (leaf j))
        (ControlledProfile.mean Λ u dir (θ,(target (leaf j),center (leaf j)))) (chosen j)))^(2*p) := by
  intro A B μ T
  let S := fun y : (Fin r→State n)×State n => GaussianFractionMixedMoments.value second A D y.1
  let R := VectorControlledRoot.value choices 0 F mean rootCoordinates
  let L := fun j : Fin m => ControlledAssignedLeaf.leaf choices j.succ P.coefficient mean (leaf j)
    (ControlledProfile.profile P Λ u dir (θ,(target (leaf j),center (leaf j))))
  have hA (j : Fin r) : (A j).PosSemidef := OldIntervalCovariance.covariance_posSemidef
    σ target center hages _ (referenceProfile_measurable P Λ u dir)
    (fun z => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u dir z).1,
      (referenceProfile_bounds P Λ u dir z).2⟩) (lo j) (hi j)
  have hS : Measurable S := (GaussianFractionMixedMoments.measurable_value second A D).comp measurable_fst
  have hR : Measurable R := VectorControlledRoot.value_measurable choices 0 F hfm mean rootCoordinates
  have hL (j : Fin m) : Measurable (L j) := ControlledAssignedLeaf.leaf_measurable choices j.succ
    P.coefficient P.measurable mean (leaf j) _
  have hs := GaussianFractionMixedMoments.residual_even_moment second A hA D hD B (p*(m+2))
  have hr := WindowAssignedFactors.root_even_moment P Λ u dir lo hi σ target center hσ hσ1 hages
    (fun j => hq.trans (hlo j)) hgap hstop B mean rootCoordinates choices hnd 0 F hA0 hν hf hfb (p*(m+2)) (Nat.mul_pos hp (by omega))
  have hl (j : Fin m) := WindowAssignedFactors.leaf_even_moment P Λ u dir θ lo hi hdisjoint
    σ target center hσ hσ1 hages hq hlo hgap hstop mean (leaf j) (hnative j) (ht j) choices hnd
    j.succ (chosen j) (hchosen j) (p*(m+2))
  have hs' := hs
  have hr' := hr
  have hl' := hl
  simp only [←Nat.mul_assoc] at hs' hr' hl'
  exact DependentWordMoments.word_even_moment μ S R L hS hR hL
    (∏ j,scale (second j) (A j) (D j))
    (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d)
    (fun j => WindowAssignedFactors.leafScale P choices j.succ lo hi (target (leaf j)) (mean (leaf j))
      (ControlledProfile.mean Λ u dir (θ,(target (leaf j),center (leaf j)))) (chosen j))
    (Finset.prod_nonneg (fun j _ => scale_nonneg (hA j) (hD j) (second j)))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j => (hgap j).le) hA0 hν d)
    (fun j => WindowAssignedFactors.leafScale_nonneg P choices j.succ lo hi (fun l => (hgap l).le)
      (ht j).1.le _ _ (chosen j))
    _ _ _ (pow_nonneg (productMomentConstant_nonneg _) _)
    (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j => WindowAssignedFactors.leafConstant_nonneg _ _ _ _)
    p hs'.1 hr'.1 (fun j => (hl' j).1) hs'.2 hr'.2 (fun j => (hl' j).2)

end SHE.WindowFirstScoreMoments
