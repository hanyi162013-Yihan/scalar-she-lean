module

public import SHE.ControlledFiniteCovarianceFields
public import SHE.BoundedThetaConvexSegment
public import SHE.BoundedThetaRelativeCovarianceMark
public import SHE.FullResidualFrameRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledFiniteCovarianceRelative
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

local notation "Point" => ControlledFiniteCovarianceFields.point P hA Λ v b hvb Z htarget hstop F hF hFm

/-- Literal finite covariance FTC integrand = the actual complete
conditional terminal word, with fixed old fractions and own baseline.
The common original history event is selected before all past inputs. -/
theorem point_relative_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q → q≤(carrier Zero k).terminal h →
      ∀θ₀ θ₁ ζ:ℝ,0≤ζ → ζ≤1 → ∀mean:WordRecursion.State (1+k),
      let c:=BoundedWindowDecomposition.convexProfile P Λ p.2.1 p.2.2 θ₀ θ₁ ζ
      let e:=fun z=>ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₁,z)-
        ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₀,z)
      Point p k h q θ₀ θ₁ ζ mean=
      (1/2:ℝ)*∫x,e x*BoundedCompleteGaussianWord.value P Λ p.2.1 p.2.2 c p.1
        (q-(v:ℝ)) (fun i=>stops Zero k h i-(v:ℝ))
        (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        mean true (directions Zero ((carrier Zero k).observations.observations h) k h)
        (StoppedGaussianFeatures.stoppedRow (fun i=>stops Zero k h i-(v:ℝ))
          (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h) x)
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
          ∂StoppedGaussianFeatures.historyMeasure (q-(v:ℝ)):=by
  filter_upwards [BoundedThetaRelativeCovarianceMark.mark_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    BoundedThetaConvexSegment.covariance_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hm hc
  intro p q hvq hqt θ₀ θ₁ ζ hζ hζ1 mean c e
  rw [ControlledFiniteCovarianceFields.point_of_window P hA Λ v b hvb Z htarget hstop F hF hFm
    p k h q hqt θ₀ θ₁ ζ mean,←hc p q hvq hqt θ₀ θ₁ ζ]
  exact hm p q hvq hqt c
    (BoundedWindowDecomposition.convexProfile_measurable P Λ p.2.1 p.2.2 θ₀ θ₁ ζ)
    (BoundedWindowDecomposition.convexProfile_bounds P Λ p.2.1 p.2.2 θ₀ θ₁ hζ hζ1) e mean

end SHE.ControlledFiniteCovarianceRelative
