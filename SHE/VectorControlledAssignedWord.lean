module

public import SHE.VectorControlledRoot
public import SHE.StoppedAssignedLeaf
public import SHE.DependentWordAssembly

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.VectorControlledAssignedWord
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier ProfileVariance
  MeasurableGaussianScores GaussianDependentScores ProfileL2
open scoped BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {n q r m : ℕ}

def coefficientWord (a : ℝ → ℝ) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (choices : List (Fin r × Fin (m+1))) (f : State q → ℝ) (mean : State n)
    (rootCoordinates : Fin q → Fin n) (leafCoordinate : Fin m → Fin n) (baseline : Fin m → ℝ)
    (x : (Fin r → State n) × State n) : ℝ :=
  (∏ j,secondScore (A j) (D j) (x.1 j))*
    VectorControlledRoot.value choices 0 f mean rootCoordinates x*
      (∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leafCoordinate j) (baseline j) x)

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r × Fin (m+1))) : ℝ :=
  (secondScoreMoment (m+2))^r + ControlledAssignedRoot.constant (m+2) choices 0 +
    ∑ j : Fin m,StoppedAssignedLeaf.constant P (m+2) choices j.succ

/-- Quantitative actual full-cylinder assigned old Gaussian word. Original root clips,
every assigned minimum-gap rough gain, every unassigned full-age rough
gain, and all original covariance-score energies remain multiplicative.
No independence between any score and any rough/root factor is assumed. -/
theorem word_normTwo (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j l, j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i)
    (mean : State n) (rootCoordinates : Fin q → Fin n) (leafCoordinate : Fin m → Fin n)
    (hnative : ∀ j, σ (leafCoordinate j) = target (leafCoordinate j))
    (ht : ∀ j, target (leafCoordinate j) ∈ Ioc 0 P.horizon)
    (hm : ∀ j, mean (leafCoordinate j) = ControlledProfile.mean Λ u d
      (θ,(target (leafCoordinate j),center (leafCoordinate j))))
    (choices : List (Fin r × Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m, block choices j.succ ≠ [] → Fin r)
    (hchosen : ∀ j h, chosen j h ∈ block choices j.succ)
    (F : State q → ℝ) (hfm : Measurable F) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j, j ≤ (block choices 0).length → ∀ z, ‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (x : Fin r → HeatCircle)
    (hD : ∀ j, familyDirection σ target center lo x j ∈
      (Matrix.toEuclideanCLM (𝕜 := ℝ)
        (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j)).range) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let D := familyDirection σ target center lo x
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center 0 θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let T := coefficientWord P.coefficient A D choices F mean rootCoordinates leafCoordinate
      (fun j => ControlledProfile.profile P Λ u d (θ,(target (leafCoordinate j),center (leafCoordinate j))))
    MemLp T 2 μ ∧ normTwo μ T ≤ sqrt (constant P r m choices)*
      (∏ j,scoreVariance (A j) (D j))*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) q*
        (∏ j,StoppedAssignedLeaf.scale P choices j.succ lo hi (target (leafCoordinate j)) (chosen j)) := by
  intro A D B μ T
  let S := fun y : (Fin r → State n) × State n => ∏ j,secondScore (A j) (D j) (y.1 j)
  let R := VectorControlledRoot.value choices 0 F mean rootCoordinates
  let L := fun j : Fin m => ControlledAssignedLeaf.leaf choices j.succ P.coefficient mean
    (leafCoordinate j) (ControlledProfile.profile P Λ u d (θ,(target (leafCoordinate j),center (leafCoordinate j))))
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d)
    (fun q => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d q).1,
      (referenceProfile_bounds P Λ u d q).2⟩) (lo j) (hi j)
  have hS : Measurable S := by
    apply Finset.measurable_prod
    intro j _
    exact (factor_measurable true (A j) (D j)).comp ((measurable_pi_apply j).comp measurable_fst)
  have hR : Measurable R := VectorControlledRoot.value_measurable choices 0 F hfm mean rootCoordinates
  have hL (j : Fin m) : Measurable (L j) := ControlledAssignedLeaf.leaf_measurable choices j.succ
    P.coefficient P.measurable mean (leafCoordinate j) _
  have hOld := OldIntervalScoreMoments.product_even_moment A hA D hD (m+2)
  have hfst : HasLaw Prod.fst (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))) μ :=
    (measurePreserving_fst (μ := Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))
      (ν := multivariateGaussian (0 : State n) B)).hasLaw
  have hiS : Integrable (fun y => |S y|^(2*(m+2))) μ := by
    convert! hfst.integrable_comp hOld.1 using 1
  have hbS : (∫ y, |S y|^(2*(m+2)) ∂μ) =
      (secondScoreMoment (m+2))^r*(∏ j,scoreVariance (A j) (D j))^(2*(m+2)) := by
    have he := hfst.integral_comp (f := fun y => |∏ j,secondScore (A j) (D j) (y j)|^(2*(m+2)))
      hOld.1.aestronglyMeasurable
    change (∫ y, |S y|^(2*(m+2)) ∂μ) = _ at he
    rw [he,hOld.2]
  have hr := VectorControlledRoot.root_even_moment P Λ u d θ lo hi σ target center hσ hσ1 hages
    hlo hgap hstop mean rootCoordinates choices hnd 0 F hA0 hν hf hfb (m+2) (by omega)
  have hl (j : Fin m) := StoppedAssignedLeaf.leaf_even_moment P Λ u d θ lo hi hdisjoint σ target center
    hσ hσ1 hages hlo hgap hstop mean (leafCoordinate j) (hnative j) (ht j) (hm j) choices hnd j.succ
    (chosen j) (hchosen j) (m+2)
  exact DependentWordAssembly.word_normTwo μ S R L hS hR hL
    (∏ j,scoreVariance (A j) (D j)) (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) q)
    (fun j => StoppedAssignedLeaf.scale P choices j.succ lo hi (target (leafCoordinate j)) (chosen j))
    (Finset.prod_nonneg (fun j _ => scoreVariance_nonneg (hA j) (hD j)))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j => (hgap j).le) hA0 hν q)
    (fun j => StoppedAssignedLeaf.scale_nonneg P choices j.succ lo hi (fun l => (hgap l).le) (ht j).1.le (chosen j))
    _ _ _ (pow_nonneg (secondScoreMoment_nonneg _) _) (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j => StoppedAssignedLeaf.constant_nonneg _ _ _ _) hiS hr.1 (fun j => (hl j).1)
    hbS.le hr.2 (fun j => (hl j).2)

end SHE.VectorControlledAssignedWord

