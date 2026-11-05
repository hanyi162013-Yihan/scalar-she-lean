module

public import SHE.NativeFirstOmittedOffsets
public import SHE.NativeFirstOmittedAverage
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.NativeFirstOmittedMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance nativeFirstOmittedPointwise_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n d r m : ℕ}

/-- Literal omitted-leaf fibre integral, under the SAME physical old
fractions and full residual as the original word. -/
def fibreAverage (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ q : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : State n) (D : Fin r→State n) (E:State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (F : State d→ℝ) : ℝ :=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let R:=NativeFirstScoreReserve.covariance P σ target center q
  let C:=ControlledFixedReserve.covariance P Λ u d0
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
  ∫ x,word A D R E choices j0 P.coefficient F (fun _ : Unit=>mean) g leaf
      (fun j=>ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) ((),x)
    ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod ((multivariateGaussian (0 : State n) R).prod (multivariateGaussian (0 : State n) C))

/-- Pointwise Gaussian omitted-word estimate at arbitrary current mean.
The exact offset budget remains explicit before any random-past average. -/
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
    (E:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup) (j0 : Fin m)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) :
    |fibreAverage P Λ u d0 θ q σ target center lo hi mean D E g leaf choices j0 F|^(2*b)≤
      constant P r m choices j0 b
        (FullResidualAssignedMoments.currentBudget P Λ u d0 θ target center leaf mean b)*
        ((∏ j,scoreVariance
            (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
          Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center q) E)*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi
            (target (leaf j)) (chosen j))^(2*b) := by
  let C0:=FullResidualAssignedMoments.currentBudget P Λ u d0 θ target center leaf mean b
  have hC0 : 0≤C0:=NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1)
  have hoffset (j : Fin m) (_hj : j≠j0) :
      Integrable (fun _ : Unit=>|mean (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) (Measure.dirac ()) ∧
      (∫ _ : Unit,|mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂Measure.dirac ())≤C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2) := by
    refine ⟨integrable_const _,?_⟩
    rw [integral_const,probReal_univ,one_smul]
    exact NormalizedLeafOffsets.offset_le_budget (fun j=>target (leaf j))
      (fun j=>mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j))))
      (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2) (fun j=>(ht j).1) j
  have hh:=averaged_even_moment (Measure.dirac ()) P Λ u d0 θ q hq σ target center hσ hσ1 hages
    lo hi hlo hlohi hstop hdisjoint (fun _ : Unit=>mean) measurable_const D hD E hE g leaf hnative ht
    choices hnd j0 chosen hchosen F hFm hA0 hν hf hfb b hb C0 hC0 hoffset
  dsimp only at hh
  simpa only [fibreAverage,C0,integral_dirac] using hh.2


end SHE.NativeFirstOmittedMoments
