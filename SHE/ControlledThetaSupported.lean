module

public import SHE.ControlledReferenceThetaGeometry
public import SHE.ControlledThetaPhysicalGeometry
public import SHE.ControlledFamilySupported
public import SHE.FullResidualChainAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledThetaSupported
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
  CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry
  ControlledOldIntervals ControlledReferenceWindows FixedOldScoreSupport ControlledFamilyProfileForest
  ProjectedUncutWord GaussianConvolution
open scoped NNReal
local instance controlledThetaSupported_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaSupported_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaSupported_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "NME" => ControlledReferenceThetaGeometry.carrier_nodeTime_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "RME" => ControlledReferenceThetaGeometry.row_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- ONE original history event supports every interpolation and every
possibly random original past-input pair. The event is selected from
the constant floor before any uncountable parameter substitution. -/
theorem supported_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,RecursiveGaussianScores.Supported (Base p)
        (profileCovariances (Base p) (oldProfile P Λ v p.2))
        (profileCovariances (Base p) (fun z=>(referenceData P A hA Λ p.1 v b hvb p.2).reference z-
          oldProfile P Λ v p.2 z)) k h := by
  let ell:=fraction P*P.lower
  have hell : 0<ell:=mul_pos (fraction_pos P) P.lower_pos
  have hold (p : Inputs) : Measurable (oldProfile P Λ v p):=
    (coefficient_section_measurable P Λ 0 v p).const_mul (fraction P)
  have hb (p : ℝ×Inputs) (z : StoppedGaussianFeatures.Domain) :
      ell≤oldProfile P Λ v p.2 z ∧ oldProfile P Λ v p.2 z≤
        (referenceData P A hA Λ p.1 v b hvb p.2).reference z := by
    have hh:=referenceProfile_bounds P Λ p.2.1 p.2.2 (z.1-(v:ℝ),z.2)
    exact ⟨hh.1,hh.2.trans ((half_le_self P.lower_pos.le).trans
      (coefficient_bounds P Λ p.1 v p.2 z).1)⟩
  have hfloor (z : StoppedGaussianFeatures.Domain) :
      ell≤(referenceData P A hA Λ 0 v b hvb (0,0)).reference z := by
    have he:=referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact (he.1.trans he.2).trans ((half_le_self P.lower_pos.le).trans
      (coefficient_bounds P Λ 0 v (0,0) z).1)
  filter_upwards [FixedOldScoreSupport.supported_ae (Base (0,(0,0))) (fun _=>ell)
    measurable_const hell (fun z=>⟨le_rfl,hfloor z⟩) hages ρ k] with h hh
  intro p
  exact HistorySupportedTransfer.supported_of_floor (Base (0,(0,0))) (Base p)
    (TME (0,(0,0)) p) (NME (0,(0,0)) p) (OME (0,(0,0)) p) (RME (0,(0,0)) p)
    (oldProfile P Λ v p.2) (hold p.2) hell (hb p) hages k h hh

theorem physical_chain_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∃ chain : Chain (Base p) k h (fun i=>i),chain.CoordinateSupport ∧
        Before (Base p) (Z:=((carrier (Base p) k).observations.observations h)) chain ∧
        Physical (Base p) ((carrier (Base p) k).observations.observations h)
          (oldProfile P Λ v p.2) chain := by
  have hell : 0<fraction P*P.lower:=mul_pos (fraction_pos P) P.lower_pos
  filter_upwards [supported_all_parameters_ae P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k]
    with h hh
  intro p
  have hc : Measurable (oldProfile P Λ v p.2):=
    (coefficient_section_measurable P Λ 0 v p.2).const_mul (fraction P)
  have hb (z : StoppedGaussianFeatures.Domain) : fraction P*P.lower≤oldProfile P Λ v p.2 z ∧
      oldProfile P Λ v p.2 z≤(referenceData P A hA Λ p.1 v b hvb p.2).reference z := by
    have he:=referenceProfile_bounds P Λ p.2.1 p.2.2 (z.1-(v:ℝ),z.2)
    exact ⟨he.1,he.2.trans ((half_le_self P.lower_pos.le).trans
      (coefficient_bounds P Λ p.1 v p.2 z).1)⟩
  apply PhysicalScoreChain.exists_chain (Base p) (oldProfile P Λ v p.2) hc hell hb hages
    ((carrier (Base p) k).observations.observations h)
    (RecursiveScoreSupport.carrier_ages (Base p) hages k h) k h (fun i=>i) _ (hh p)
  exact ⟨fun _=>rfl,fun j hj=>False.elim (hj ⟨j,rfl⟩)⟩

/-- Exact actual theta-family endpoint representation on a common
history event. It allows BOTH random past-input substitution and
arbitrary actual current means before taking any outer integral. -/
theorem full_residual_average_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,0≤q → q≤(carrier (Base p) k).terminal h →
      ∀ z : WordRecursion.State (n+k),
      gaussianAverage (WordRecursion.covariance
        (referenceData P A hA Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h) z=
      gaussianAverage (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)
        (oldAverage (Base p) (oldProfile P Λ v p.2) k h) z := by
  filter_upwards [physical_chain_all_parameters_ae P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k]
    with h hh
  intro p
  obtain ⟨chain,hs,_,hp⟩:=hh p
  exact full_residual_average_of_chain (Base p) (oldProfile P Λ v p.2) chain hs hp
    (RecursiveScoreSupport.carrier_ages (Base p) hages k h)

end SHE.ControlledThetaSupported
