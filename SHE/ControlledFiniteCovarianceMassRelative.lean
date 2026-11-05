module

public import SHE.ControlledFiniteCovarianceMass
public import SHE.BoundedThetaConvexSegment
public import SHE.FullResidualFrameRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledFiniteCovarianceMassRelative
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

local notation "Mass"=>ControlledFiniteCovarianceMass.mass P hA Λ v b hvb Z htarget hstop F hF hFm

/-- Exact TRUE physical finite covariance score mass on relative arrays.
No range/inverse or stochastic applicability hypothesis is needed for
this clock identity; ONE history event supports all random past inputs. -/
theorem mass_relative_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q → q≤(carrier Zero k).terminal h → ∀θ₀ θ₁ ζ:ℝ,
      let σ:=fun i=>stops Zero k h i-(v:ℝ)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let center:=centers Zero k h
      let c:=BoundedWindowDecomposition.convexProfile P Λ p.2.1 p.2.2 θ₀ θ₁ ζ
      let e:=fun z=>ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₁,z)-
        ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₀,z)
      Mass p k h q θ₀ θ₁ ζ=
        ∫z,|e z| *MeasurableGaussianScores.scoreVariance
          (Cov p k h q c) (StoppedGaussianFeatures.stoppedRow σ target center z)
            ∂StoppedGaussianFeatures.historyMeasure (q-(v:ℝ)):=by
  filter_upwards [BoundedThetaConvexSegment.covariance_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt θ₀ θ₁ ζ σ target center c e
  have ht(a:ℝ):q≤(carrier (Base (a,p.2)) k).terminal h:=by
    rwa [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm (a,p.2) (0,(0,0)) k h]
  have hrow(z):StoppedGaussianFeatures.stoppedRow (stops (Base p) k h)
      (targets (Base p) k h) (centers (Base p) k h) (ObservationTimeShift.translation (v:ℝ) z)=
      StoppedGaussianFeatures.stoppedRow σ target center z:=by
    rw [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    have he:=ObservationTimeShift.stoppedRow_translation (v:ℝ) σ target center z
    simpa only [σ,target,sub_add_cancel] using he
  unfold ControlledFiniteCovarianceMass.mass
  simp only [ActualCovarianceMarkFields.cappedResidual,min_eq_left (ht θ₀),min_eq_left (ht θ₁)]
  rw [←hh p q hvq hqt θ₀ θ₁ ζ]
  rw [←show (q-(v:ℝ))+(v:ℝ)=q by ring,
    ←ObservationTimeShift.integral_history_translation (v:ℝ) (q-(v:ℝ))]
  simp only [sub_add_cancel]
  apply integral_congr_ae
  filter_upwards with z
  rw [ObservationTimeShift.profile_translation,hrow]

end SHE.ControlledFiniteCovarianceMassRelative
