module

public import SHE.NativeFirstWholeAverage
public import SHE.NativeFirstWholeOffsets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeFirstWholeMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance nativeFirstWholePointwise_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n d r m : ℕ}

/-- ORIGINAL native-age normalized offsets at a single deterministic
set of data. This is evaluated pointwise before any random-past average. -/
def currentBudget (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (target : Fin n→ℝ) (center : Fin n→HeatCircle) (leaf : Fin m→Fin n) (mean : State n) (b : ℕ) : ℝ :=
  NormalizedLeafOffsets.budget (fun j=>target (leaf j))
    (fun j=>mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j))))
    (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2)

/-- A pointwise deterministic Gaussian assigned-word bound at arbitrary
current mean. It remains valid when ALL data are subsequently evaluated
at a past-dependent parameter; no fixed-covariance outer probability
space has been substituted by a random one. -/
theorem pointwise_even_moment
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E : State n) (hE : E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let R := NativeFirstScoreReserve.covariance P σ target center q
    let C := ControlledFixedReserve.covariance P Λ u d0
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
    let νG := (Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod
      ((multivariateGaussian (0 : State n) R).prod (multivariateGaussian (0 : State n) C))
    let W := word A D R E choices P.coefficient F (fun _ : Unit=>mean) g leaf
      (fun j=>ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    |∫ x,W ((),x) ∂νG|^(2*b)≤constant P r m choices b
      (currentBudget P Λ u d0 θ target center leaf mean b)*
        (((∏ j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
            ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A R C νG W
  let C0 := currentBudget P Λ u d0 θ target center leaf mean b
  have hC0 : 0≤C0 := NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1)
  have hoffset (j : Fin m) :
      Integrable (fun _ : Unit=>|mean (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) (Measure.dirac ()) ∧
      (∫ _ : Unit,|mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂Measure.dirac ())≤C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2) := by
    refine ⟨integrable_const _,?_⟩
    rw [integral_const,probReal_univ,one_smul]
    have hh := NormalizedLeafOffsets.offset_le_budget (fun j=>target (leaf j))
        (fun j=>mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j))))
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2) (fun j=>(ht j).1) j
    convert! hh using 1

  have hh := averaged_even_moment (Measure.dirac ()) P Λ u d0 θ q hq σ target center hσ hσ1 hages
    lo hi hlo hlohi hstop hdisjoint (fun _ : Unit=>mean) measurable_const D hD E hE g leaf hnative ht
    choices hnd chosen hchosen F hFm hA0 hν hf hfb b hb0 C0 hC0 hoffset
  dsimp only at hh
  simpa only [integral_dirac] using hh.2

end SHE.NativeFirstWholeMoments
