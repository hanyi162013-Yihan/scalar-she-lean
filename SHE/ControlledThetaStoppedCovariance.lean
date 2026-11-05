module

public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledThetaStoppedCovariance
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaStoppedCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaStoppedCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaStoppedCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem absolute_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,0≤q → q≤(carrier (Base p) k).terminal h →
      fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q=
      StoppedGaussianFeatures.stoppedCovariance (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h)
        (fun z=>coefficient P Λ p.1 v p.2 z-
          OldIntervalCovariance.sumProfile (oldProfile P Λ v p.2)
            (lower (Base p) k h) (upper (Base p) k h) z) q := by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae P A hA Λ v b hvb
    Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p
  obtain ⟨chain,_,_,hphysical⟩:=hh p
  have hc : Measurable (oldProfile P Λ v p.2):=
    (coefficient_section_measurable P Λ 0 v p.2).const_mul (fraction P)
  have hell : 0<fraction P*P.lower:=mul_pos (fraction_pos P) P.lower_pos
  have hb (z : StoppedGaussianFeatures.Domain) : fraction P*P.lower≤oldProfile P Λ v p.2 z ∧
      oldProfile P Λ v p.2 z≤(referenceData P A hA Λ p.1 v b hvb p.2).reference z := by
    have he:=referenceProfile_bounds P Λ p.2.1 p.2.2 (z.1-(v:ℝ),z.2)
    exact ⟨he.1,he.2.trans ((half_le_self P.lower_pos.le).trans
      (coefficient_bounds P Λ p.1 v p.2 z).1)⟩
  exact full_residual_eq_stopped_of_chain (Base p) (oldProfile P Λ v p.2) hc hell hb chain hphysical
    (RecursiveScoreSupport.carrier_ages (Base p) hages k h)

/-- The ACTUAL canonical family residual is exactly the relative-age
full stopped residual covariance used by the conditional Gaussian
moment estimates. One history event works for every theta and random
past input. Original targets and covered stops are stated separately. -/
theorem relative_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,0≤q → q≤(carrier (Base p) k).terminal h →
      fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q=
      ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
        (fixedProfile P Λ p.2.1 p.2.2 (fun j=>lower (Base p) k h j-(v:ℝ))
          (fun j=>upper (Base p) k h j-(v:ℝ)))
        (fun i=>stops (Base p) k h i-(v:ℝ)) (fun i=>targets (Base p) k h i-(v:ℝ))
        (centers (Base p) k h) (q-(v:ℝ)) p.1 := by
  filter_upwards [absolute_all_parameters_ae P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k]
    with h hh
  intro p q hq hqt
  have he:=ControlledProfileTimeShift.residualCovariance_translation P Λ p.1 (v:ℝ) p.2.1 p.2.2
    (q-(v:ℝ)) (fun i=>stops (Base p) k h i-(v:ℝ))
    (fun i=>targets (Base p) k h i-(v:ℝ)) (centers (Base p) k h)
    (fun j=>lower (Base p) k h j-(v:ℝ)) (fun j=>upper (Base p) k h j-(v:ℝ))
  have hceq : ControlledProfileTimeShift.oldProfile P Λ v p.2.1 p.2.2=oldProfile P Λ v p.2:=rfl
  simp only [ControlledProfileTimeShift.fixedOldProfile,hceq,sub_add_cancel] at he
  exact (hh p q hq hqt).trans he

end SHE.ControlledThetaStoppedCovariance
