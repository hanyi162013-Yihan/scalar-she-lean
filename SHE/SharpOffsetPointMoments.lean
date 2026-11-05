module

public import SHE.PhysicalOffsetPointMoments
public import SHE.SharpWordTimeScale
public import SHE.ActualPointMomentSum
public import SHE.PhysicalWordTimeScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.SharpOffsetPointMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord ControlledOldIntervals
open scoped BigOperators NNReal
local instance sharpOffsetPointPeriod : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

/-- Literal all-order physical directional kernel moments from only actual scalar current displacement moments. -/
theorem directional_even_moment_ae
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) ρ k,
      ∀ q : ℝ≥0,(q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ direction : WordRecursion.State (n+k),direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (intervalCovariance ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) q ((carrier L k).terminal p))).range →
      ∀ mean : Ω→WordRecursion.State (n+k),Measurable mean →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,
        ‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ C0 : ℝ,0≤C0 →
      (∀ j : Fin k,Integrable (fun ω => |mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent)) μ ∧
        (∫ ω,|mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
          C0*(targets L k p (leafIndex k (fun i => i) j))^((b*(k+2):ℕ)*P.exponent/2)) →
      let F := fun ω => fderiv ℝ (gaussianAverage (WordRecursion.covariance
        (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) (mean ω) direction
      let c := referenceProfile P Λ u dir
      Integrable (fun ω => |F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        PhysicalOffsetPointMoments.momentConstant P k b C0*(|scoreScale L c k p q direction| *
          SharpWordTimeScale.total L P k p q A0 ν)^(2*b) := by
  have hcb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [PhysicalOffsetPointAssignments.assignment_even_moment_ae μ P ha Λ u dir θ L hages ρ k,
    terminal_range_integral_ae L _ (referenceProfile_measurable P Λ u dir)
      (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k] with p hmom hrepresentation
  intro q hq hp direction hrange mean hm A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  dsimp only
  let c := referenceProfile P Λ u dir
  let cs := assignments (m:=k+1) (List.finRange k)
  let W := fun choices ω => ∫ x,rangeAssignedWord L c k p q direction (mean ω) choices x
    ∂terminalAssignedMeasure L c k p q
  let s := scoreScale L c k p q direction
  let T := SharpWordTimeScale.total L P k p q A0 ν
  let C := fun choices => max (OffsetFirstScoreWordMoments.constant P (k+1) k (liftChoices choices) b C0) 0
  have hW (choices) (_hc : choices∈cs) : Measurable (W choices) :=
    ActualPointMomentSum.assignment_average_measurable L c k p q direction mean hm choices
  have hbound (choices) (hc : choices∈cs) := hmom q hq hp direction hrange mean hm choices
    (ActualPointMomentSum.choices_nodup k choices hc) (SharpWordTimeScale.chosen L k p q choices)
    (SharpWordTimeScale.chosen_mem L k p q choices) A0 ν hA0 hν
    ((L.test_uniform.smooth _).of_le (by simp))
    (fun j hj z => hjet j (hj.trans (ActualPointMomentSum.root_length_le k choices hc)) z) b hb0 C0 hC0 hoffset
  have hterm (choices) (hc : choices∈cs) : (∫ ω,|W choices ω|^(2*b) ∂μ)≤C choices*(|s| *T)^(2*b) := by
    have hfactor := SharpWordTimeScale.factor_le_total L P k p q A0 ν choices hc
    dsimp only [SharpWordTimeScale.factor] at hfactor
    have hpow := pow_le_pow_left₀ (mul_nonneg (abs_nonneg s) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hfactor (abs_nonneg s)) (2*b)
    have he : (s*PhysicalWordTimeScale.factor L P k p q choices (SharpWordTimeScale.chosen L k p q choices) A0 ν)^(2*b)=
        (|s| *|PhysicalWordTimeScale.factor L P k p q choices (SharpWordTimeScale.chosen L k p q choices) A0 ν|)^(2*b) := by
      rw [←abs_mul,pow_abs_two_mul]
    have hh := (hbound choices hc).2
    change (∫ ω,|W choices ω|^(2*b) ∂μ)≤_ at hh
    rw [he] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) _)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
  have hsum := FiniteAssignmentMoments.moment_sum μ cs W hW b hb0 (fun choices hc => (hbound choices hc).1)
    (fun choices => C choices*(|s| *T)^(2*b)) hterm
  have he (ω : Ω) : fderiv ℝ (gaussianAverage
      (WordRecursion.covariance (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (mean ω) direction=
      (1/2:ℝ)^k*(cs.map (fun choices => W choices ω)).sum :=
    (hrepresentation q q.2 hq direction (mean ω) hrange).2
  have hpow (ω : Ω) : |fderiv ℝ (gaussianAverage
      (WordRecursion.covariance (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (mean ω) direction|^(2*b)=
      ((1/2:ℝ)^k)^(2*b)*|(cs.map (fun choices => W choices ω)).sum|^(2*b) := by
    rw [he ω,abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^k),mul_pow]
  constructor
  · exact (hsum.1.const_mul _).congr (ae_of_all _ (fun ω => (hpow ω).symm))
  · simp_rw [hpow]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hsum.2 (show 0≤((1/2:ℝ)^k)^(2*b) by positivity)
    rw [List.sum_map_mul_right] at hh
    exact hh.trans_eq (by dsimp only [PhysicalOffsetPointMoments.momentConstant,C,cs];ring)

end SHE.SharpOffsetPointMoments
