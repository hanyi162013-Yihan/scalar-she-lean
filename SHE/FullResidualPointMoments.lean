module

public import SHE.FullResidualPhysicalMoments
public import SHE.ActualPointMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.FullResidualPointMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry ControlledOldIntervals
open scoped BigOperators NNReal
local instance fullResidualPointMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

theorem assignment_average_measurable (L : CutoffWordLevel.Level R X n) (c : Domain→ℝ)
    (k : ℕ) (p : History X k) (q : ℝ) (direction : WordRecursion.State (n+k))
    (mean : Ω→WordRecursion.State (n+k)) (hm : Measurable mean)
    (choices : List (Fin k×Fin (k+1))) :
    Measurable (fun ω=>∫ x,fullAssignedWord L c k p q direction (mean ω) choices x
      ∂fullAssignedMeasure L c k p q) := by
  haveI : IsProbabilityMeasure (fullAssignedMeasure L c k p q) := by
    dsimp only [fullAssignedMeasure]
    infer_instance
  let Z := (carrier L k).observations.observations p
  have hf : Measurable (fun z : Ω×((Fin k→WordRecursion.State (n+k))×WordRecursion.State (n+k))=>
      fullAssignedWord L c k p q direction (mean z.1) choices z.2) :=
    FullResidualAssignedMoments.word_measurable false (covariances L Z c k p) (directions L Z k p)
      (fullResidualCovariance L c k p q) direction choices R.totalVariance
      R.totalVariance_smooth.smooth.continuous.measurable (L.test (rootParameter k p))
      (L.test_uniform.smooth _).continuous.measurable mean hm
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p)
  exact (hf.stronglyMeasurable.integral_prod_right').measurable

def momentConstant (P : CanonicalCovariance.ProfileParameters) (k b : ℕ) (C0 : ℝ) : ℝ :=
  ((1/2:ℝ)^k)^(2*b)*((assignments (m:=k+1) (List.finRange k)).length:ℝ)^(2*b-1)*
    ((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
      max (FullResidualAssignedMoments.constant P k k choices b C0) 0)).sum

theorem momentConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (k b : ℕ) (C0 : ℝ) :
    0≤momentConstant P k b C0 := by
  unfold momentConstant
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩ := List.mem_map.mp hx
  exact le_max_right _ _

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

/-- The literal all-order derivative admits its sharp moment estimate
for every direction in the full residual range. No common front range
or independent current-state assumption remains. -/
theorem directional_even_moment_ae
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) ρ k,
      ∀ q : ℝ≥0,(q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ direction : WordRecursion.State (n+k),direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (fullResidualCovariance L (referenceProfile P Λ u dir) k p q)).range →
      ∀ mean : Ω→WordRecursion.State (n+k),Measurable mean →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ C0 : ℝ,0≤C0 →
      (∀ j : Fin k,Integrable (fun ω=>|mean ω (leafIndex k (fun i=>i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent)) μ ∧
        (∫ ω,|mean ω (leafIndex k (fun i=>i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
          C0*(targets L k p (leafIndex k (fun i=>i) j))^((b*(k+2):ℕ)*P.exponent/2)) →
      let F := fun ω=>fderiv ℝ (gaussianAverage (WordRecursion.covariance
        (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) (mean ω) direction
      Integrable (fun ω=>|F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        momentConstant P k b C0*(|FullResidualPhysicalMoments.scoreScale P ha Λ u dir θ L k p q direction| *
          SharpWordTimeScale.total L P k p q A0 ν)^(2*b) := by
  have hcb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [FullResidualPhysicalMoments.assignment_even_moment_ae μ P ha Λ u dir θ L hages ρ k,
    full_residual_integral_ae L _ (referenceProfile_measurable P Λ u dir)
      (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k] with p hmom hrepresentation
  intro q hq hp direction hrange mean hm A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  dsimp only
  let c := referenceProfile P Λ u dir
  let cs := assignments (m:=k+1) (List.finRange k)
  let W := fun choices ω=>∫ x,fullAssignedWord L c k p q direction (mean ω) choices x
    ∂fullAssignedMeasure L c k p q
  let s := FullResidualPhysicalMoments.scoreScale P ha Λ u dir θ L k p q direction
  let T := SharpWordTimeScale.total L P k p q A0 ν
  let C := fun choices=>max (FullResidualAssignedMoments.constant P k k choices b C0) 0
  have hW (choices) (_hc : choices∈cs) : Measurable (W choices) :=
    assignment_average_measurable L c k p q direction mean hm choices
  have hbound (choices) (hc : choices∈cs) := hmom q hq hp direction hrange mean hm choices
    (ActualPointMomentSum.choices_nodup k choices hc) A0 ν hA0 hν
    ((L.test_uniform.smooth _).of_le (by simp))
    (fun j hj z=>hjet j (hj.trans (by
      simpa only [Fintype.card_fin] using
        (block_nodup choices (ActualPointMomentSum.choices_nodup k choices hc) 0).length_le_card)) z)
    b hb0 C0 hC0 hoffset
  have hterm (choices) (hc : choices∈cs) :
      (∫ ω,|W choices ω|^(2*b) ∂μ)≤C choices*(|s| *T)^(2*b) := by
    have hfactor := SharpWordTimeScale.factor_le_total L P k p q A0 ν choices hc
    have hpow := pow_le_pow_left₀ (mul_nonneg (abs_nonneg s) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hfactor (abs_nonneg s)) (2*b)
    have he : (s*SharpWordTimeScale.factor L P k p q choices A0 ν)^(2*b)=
        (|s| *|SharpWordTimeScale.factor L P k p q choices A0 ν|)^(2*b) := by
      rw [←abs_mul,pow_abs_two_mul]
    have hh := (hbound choices hc).2
    change (∫ ω,|W choices ω|^(2*b) ∂μ)≤_ at hh
    rw [he] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) _)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
  have hsum := FiniteAssignmentMoments.moment_sum μ cs W hW b hb0
    (fun choices hc=>(hbound choices hc).1) (fun choices=>C choices*(|s| *T)^(2*b)) hterm
  have he (ω : Ω) : fderiv ℝ (gaussianAverage
      (WordRecursion.covariance (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (mean ω) direction=
      (1/2:ℝ)^k*(cs.map (fun choices=>W choices ω)).sum :=
    (hrepresentation q q.2 hq direction (mean ω) hrange).2
  have hpow (ω : Ω) : |fderiv ℝ (gaussianAverage
      (WordRecursion.covariance (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (mean ω) direction|^(2*b)=
      ((1/2:ℝ)^k)^(2*b)*|(cs.map (fun choices=>W choices ω)).sum|^(2*b) := by
    rw [he ω,abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^k),mul_pow]
  constructor
  · exact (hsum.1.const_mul _).congr (ae_of_all _ (fun ω=>(hpow ω).symm))
  · simp_rw [hpow]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hsum.2 (show 0≤((1/2:ℝ)^k)^(2*b) by positivity)
    rw [List.sum_map_mul_right] at hh
    exact hh.trans_eq (by dsimp only [momentConstant,C,cs];ring)

end SHE.FullResidualPointMoments
