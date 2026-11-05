module

public import SHE.BoundedThetaRelativeSecondScore
public import SHE.ConvexResidualCovariance
public import SHE.ControlledThetaRelativeArrays

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.BoundedThetaConvexSegment
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

/-- The literal Gaussian matrix segment is exactly the residual of the
convex endpoint profile with every original old fraction held fixed.
No intermediate profile fixed point is assumed. One history event works
for all observed past inputs and all three interpolation parameters. -/
theorem covariance_all_parameters_ae
    (hages : ∀ x i, (Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0, 0)) ρ k,
      ∀ p : ℝ × Inputs, ∀ q : ℝ, (v : ℝ) ≤ q → q ≤ (carrier Zero k).terminal h →
      ∀ θ η ζ : ℝ,
      Cov p k h q (BoundedWindowDecomposition.convexProfile P Λ p.2.1 p.2.2 θ η ζ) =
        (1 - ζ) • fullResidualCovariance (Base (θ, p.2)) (oldProfile P Λ v p.2) k h q +
          ζ • fullResidualCovariance (Base (η, p.2)) (oldProfile P Λ v p.2) k h q := by
  filter_upwards [ControlledThetaRelativeArrays.full_covariance_relative_fixed_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt θ η ζ
  rw [hh (θ, p.2) q (v.2.trans hvq) hqt, hh (η, p.2) q (v.2.trans hvq) hqt]
  exact ConvexResidualCovariance.covariance P Λ p.2.1 p.2.2 _ _
    (RelativeHistoryGeometry.relative_disjoint Zero k h) _ _ _
    (fun i => sub_le_sub_right
      ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _)
    (q - (v : ℝ)) θ η ζ

end SHE.BoundedThetaConvexSegment
