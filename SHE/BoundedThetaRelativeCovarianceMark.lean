module

public import SHE.BoundedThetaRelativeSecondScore
public import SHE.FullResidualFrameRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.BoundedThetaRelativeCovarianceMark
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i, (b : ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i, (b : ℝ) ≤ (Z.observations x i).stop)
variable (F : X → WordRecursion.State 1 → ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X × WordRecursion.State 1 => F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0, (0, 0))
local notation "Cov" => BoundedThetaRelativeSecondScore.covariance P hA Λ v b hvb Z htarget hstop F hF hFm

/-- The literal signed physical input integral under any common bounded
elliptic future law. One original-history event permits arbitrary observed
past inputs and endpoint baselines, even at q equal to the terminal time. -/
theorem mark_all_parameters_ae
    (hages : ∀ x i, (Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0, 0)) ρ k,
      ∀ p : ℝ × Inputs, ∀ q : ℝ, (v : ℝ) ≤ q → q ≤ (carrier Zero k).terminal h →
      ∀ c : StoppedGaussianFeatures.Domain → ℝ, Measurable c →
      (∀ z, P.lower ≤ c z ∧ c z ≤ P.upper) →
      ∀ e : StoppedGaussianFeatures.Domain → ℝ, ∀ mean : WordRecursion.State (1 + k),
      FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q) (Cov p k h q c)
        (ObservationTimeShift.profile (v : ℝ) e)
        (StoppedGaussianFeatures.stoppedRow (stops (Base p) k h)
          (targets (Base p) k h) (centers (Base p) k h))
        (oldAverage (Base p) (oldProfile P Λ v p.2) k h) mean =
      (1 / 2 : ℝ) * ∫ x, e x * BoundedCompleteGaussianWord.value P Λ p.2.1 p.2.2 c p.1
        (q - (v : ℝ)) (fun i => stops Zero k h i - (v : ℝ))
        (fun i => targets Zero k h i - (v : ℝ)) (centers Zero k h)
        (fun j => lower Zero k h j - (v : ℝ)) (fun j => upper Zero k h j - (v : ℝ))
        mean true (directions Zero ((carrier Zero k).observations.observations h) k h)
        (StoppedGaussianFeatures.stoppedRow (fun i => stops Zero k h i - (v : ℝ))
          (fun i => targets Zero k h i - (v : ℝ)) (centers Zero k h) x)
        (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (F (rootParameter k h))
          ∂StoppedGaussianFeatures.historyMeasure (q - (v : ℝ)) := by
  filter_upwards [BoundedThetaRelativeSecondScore.score_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hrep
  intro p q hvq hqt c hc hcb e mean
  let σ := fun i => stops Zero k h i - (v : ℝ)
  let target := fun i => targets Zero k h i - (v : ℝ)
  let center := centers Zero k h
  let lo := fun j => lower Zero k h j - (v : ℝ)
  let hi := fun j => upper Zero k h j - (v : ℝ)
  let row := StoppedGaussianFeatures.stoppedRow σ target center
  let residual := BoundedWindowDecomposition.residual P Λ p.2.1 p.2.2 lo hi c
  have hgeom (i) : σ i ≤ target i := sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hdisjoint (j l) (hne : j ≠ l) : hi j ≤ lo l ∨ hi l ≤ lo j :=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hcm : Measurable residual :=
    BoundedWindowDecomposition.residual_measurable P Λ p.2.1 p.2.2 lo hi c hc
  have hcb' (z) : P.lower / 2 ≤ residual z ∧ residual z ≤ P.upper :=
    BoundedWindowDecomposition.residual_bounds P Λ p.2.1 p.2.2 lo hi hdisjoint c hcb z
  have hrange := FullResidualFrameRange.row_mem_all_ranges_ae σ target center hgeom
    (q - (v : ℝ)) (fun _ : Unit => residual) (fun _ => hcm)
      (half_pos P.lower_pos) (fun _ => hcb')
  have hrow (x) : StoppedGaussianFeatures.stoppedRow
      (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h)
      (ObservationTimeShift.translation (v : ℝ) x) = row x := by
    rw [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0, (0, 0)) k h,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0, (0, 0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0, (0, 0)) k h]
    have hh := ObservationTimeShift.stoppedRow_translation (v : ℝ) σ target center x
    simpa only [σ, target, sub_add_cancel] using hh
  unfold FiniteWordScores.covarianceMark
  rw [← show (q - (v : ℝ)) + (v : ℝ) = q by ring,
    ← ObservationTimeShift.integral_history_translation (v : ℝ) (q - (v : ℝ))]
  simp only [sub_add_cancel]
  congr 1
  apply integral_congr_ae
  filter_upwards [hrange] with x hx
  rw [ObservationTimeShift.profile_translation, hrow]
  have hd : row x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Cov p k h q c)).range := hx ()
  have hh := hrep p q hvq hqt c hc hcb (row x) mean hd
  change e x * (∫ y, oldAverage (Base p) (oldProfile P Λ v p.2) k h (mean + y) *
    MeasurableGaussianScores.secondScore (Cov p k h q c) (row x) y
      ∂multivariateGaussian 0 (Cov p k h q c)) = _
  rw [hh]

end SHE.BoundedThetaRelativeCovarianceMark
