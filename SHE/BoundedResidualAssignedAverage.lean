module

public import SHE.BoundedResidualAssignedMoments

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
local instance fullResidualAssignedAverage_periodPos : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n r m : ℕ}

/-- Genuine Gaussian averaging preserves the full-residual score bound,
with all old root and rough gains and the dependent current mean intact. -/
theorem averaged_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
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
    Integrable (fun ω => |∫ x,W (ω,x) ∂νG|^(2*b)) μ ∧
      (∫ ω,|∫ x,W (ω,x) ∂νG|^(2*b) ∂μ) ≤ constant P r m choices b C0*
        (((∏ j,scoreVariance (A j) (D j))*scale second B E)*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1*
            ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A B νG W
  have hh := joint_even_moment μ P Λ u d0 c hc hcb η q hq σ target center hσ hσ1 hages lo hi hlo hlohi hstop hdisjoint
    mean hm second D hD E hE g leaf hnative ht choices hnd chosen hchosen F hFm hA0 hν hf hfb b hb0 C0 hC0 hoffset
  have hW : Measurable W := word_measurable second A D B E choices P.coefficient P.measurable
    F hFm mean hm g leaf _
  have hi2b : Integrable (fun z => ‖W z‖^(2*b)) (μ.prod νG) := by
    simpa only [Real.norm_eq_abs] using hh.1
  have hi1 := integrable_norm_pow_of_le hW.aestronglyMeasurable (by omega : 1≤2*b) hi2b
  have hiW : Integrable W (μ.prod νG) := (integrable_norm_iff hW.aestronglyMeasurable).mp
    (by simpa only [pow_one] using hi1)
  have hj := UniformFiberMoments.average_even_moment μ νG W hiW b hh.1
  exact ⟨hj.1,hj.2.trans hh.2⟩

end SHE.BoundedResidualAssignedMoments
