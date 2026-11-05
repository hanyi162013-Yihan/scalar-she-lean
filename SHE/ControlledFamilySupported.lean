module

public import SHE.HistorySupportedTransfer
public import SHE.ControlledFamilyProfileForest
public import SHE.ControlledFamilyScoreGeometry
public import SHE.UniformPhysicalProfileForest
public import SHE.ControlledReferenceFamilyBounds
public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.ControlledReferenceFamilyLevel
public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledFamilySupported
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledFamilySupported_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilySupported_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilySupported_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v  ≤  b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)  ≤  (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)  ≤  (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))


open CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry


open ControlledOldIntervals ControlledReferenceWindows

open FixedOldScoreSupport ControlledFamilyProfileForest ProjectedUncutWord

/-- ONE actual history event supports the full old/residual Gaussian
calculus for EVERY past-input member of the literal reference family.
The fixed-floor event is chosen first; each new residual is genuinely
positive and each old range follows by covariance order. -/
theorem supported_all_inputs_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)) ρ k,
      ∀ p : Inputs,RecursiveGaussianScores.Supported ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p)
        (profileCovariances ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) (oldProfile P Λ v p))
        (profileCovariances ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) (fun z=>(ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p).reference z-oldProfile P Λ v p z)) k h := by
  let ell := fraction P*P.lower
  have hell : 0<ell := mul_pos (fraction_pos P) P.lower_pos
  have hold (p : Inputs) : Measurable (oldProfile P Λ v p) :=
    (coefficient_section_measurable P Λ 0 v p).const_mul (fraction P)
  have hb (p : Inputs) (z : Domain) : ell ≤ oldProfile P Λ v p z ∧
      oldProfile P Λ v p z ≤ (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p).reference z := by
    have hh := referenceProfile_bounds P Λ p.1 p.2 (z.1-(v:ℝ),z.2)
    exact ⟨hh.1,hh.2.trans ((half_le_self P.lower_pos.le).trans (coefficient_bounds P Λ θ v p z).1)⟩
  have hfloor (z : Domain) : ell ≤ (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)).reference z := by
    have he := referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact (he.1.trans he.2).trans ((half_le_self P.lower_pos.le).trans (coefficient_bounds P Λ θ v (0,0) z).1)
  filter_upwards [FixedOldScoreSupport.supported_ae ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) (fun _=>ell) measurable_const hell
    (fun z=>⟨le_rfl,hfloor z⟩) hages ρ k] with h hh
  intro p
  exact HistorySupportedTransfer.supported_of_floor ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p)
    (ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm (0,0) p)
    (ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm (0,0) p)
    (ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm (0,0) p)
    (ControlledReferenceFamilyBounds.row_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm (0,0) p)
    (oldProfile P Λ v p) (hold p) hell (hb p) hages k h hh

/-- All original full-final-space score chains and their triangular
support exist on that SAME actual history event, before selecting any
possibly random reference input. -/
theorem physical_chain_all_inputs_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∃ chain : Chain ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k h (fun i=>i),chain.CoordinateSupport ∧
        Before ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) (Z:=((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).observations.observations h)) chain ∧
        Physical ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).observations.observations h) (oldProfile P Λ v p) chain := by
  have hell : 0<fraction P*P.lower := mul_pos (fraction_pos P) P.lower_pos
  have hold (p : Inputs) : Measurable (oldProfile P Λ v p) :=
    (coefficient_section_measurable P Λ 0 v p).const_mul (fraction P)
  have hb (p : Inputs) (z : Domain) : fraction P*P.lower ≤ oldProfile P Λ v p z ∧
      oldProfile P Λ v p z ≤ (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p).reference z := by
    have hh := referenceProfile_bounds P Λ p.1 p.2 (z.1-(v:ℝ),z.2)
    exact ⟨hh.1,hh.2.trans ((half_le_self P.lower_pos.le).trans (coefficient_bounds P Λ θ v p z).1)⟩
  filter_upwards [supported_all_inputs_ae P A hA Λ θ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p
  apply PhysicalScoreChain.exists_chain ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) (oldProfile P Λ v p) (hold p) hell (hb p) hages
    ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).observations.observations h)
    (RecursiveScoreSupport.carrier_ages ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) hages k h) k h (fun i=>i) _ (hh p)
  exact ⟨fun _=>rfl,fun j hj=>False.elim (hj ⟨j,rfl⟩)⟩

end SHE.ControlledFamilySupported
