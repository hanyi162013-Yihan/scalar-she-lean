module

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

namespace SHE.ControlledFamilyProfileForest
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledFamilyProfileForest_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyProfileForest_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyProfileForest_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))


open CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry


open ControlledOldIntervals ControlledReferenceWindows

/-- Literal fixed old reference fraction of the past-state profile,
in absolute physical time. Its theta is fixed at zero independently of
the full controlled reference interpolation. -/
def oldProfile (p : Inputs) (z : Domain) : ℝ := fraction P*coefficient P Λ 0 v p z

/-- One actual history event controls the original parent forest and
all old ranges for EVERY member of the true random-reference family.
The deterministic envelope is anchored at zero initial data solely to
name their common geometry; no Gaussian current law is identified. -/
theorem all_inputs_forest_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)) ρ k,
      ∀ p : Inputs,
      (∀ j : Fin k,directions ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).observations.observations h) k h j∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ)
          (covariances ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).observations.observations h)
            (oldProfile P Λ v p) k h j)).range) ∧
      ∀ hp : StrictHistory ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) k h,
        SmallHistory ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) (uniformHorizon n) k h→
        scoreProduct ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).observations.observations h)
            (oldProfile P Λ v p) k h ≤ 
          timeWeight ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) (fraction P*P.lower) (uniformConstant n) k h*
            OrderedHeatForests.parentDensity 2 (by norm_num) k
              (fun i=>((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) k).observations.observations h i).target)
              (carrier_orderedTimes ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) hages k h hp)
              (fun i=>((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) k).observations.observations h i).center) := by
  let ell := fraction P*P.lower
  have hell : 0<ell := mul_pos (fraction_pos P) P.lower_pos
  have hold (p : Inputs) : Measurable (oldProfile P Λ v p) :=
    (coefficient_section_measurable P Λ 0 v p).const_mul (fraction P)
  have hb (p : Inputs) (z : Domain) : ell ≤ oldProfile P Λ v p z ∧ oldProfile P Λ v p z ≤ P.lower/2 := by
    have hh := referenceProfile_bounds P Λ p.1 p.2 (z.1-(v:ℝ),z.2)
    exact hh
  have hfloor (z : Domain) : ell ≤ (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)).reference z := by
    have he := (referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0))
    apply (he.1.trans he.2).trans
    exact (half_le_self P.lower_pos.le).trans (coefficient_bounds P Λ θ v (0,0) z).1
  filter_upwards [uniform_all_profiles_forest_ae ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) hell hfloor
    (oldProfile P Λ v) hold hb hages ρ k] with h hh
  intro p
  have hobs := (ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p (0,0) k h
  have hcov := ControlledFamilyScoreGeometry.covariances_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm
    p (0,0) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) k).observations.observations h) (oldProfile P Λ v p) k h
  have hdir := ControlledFamilyScoreGeometry.directions_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm
    p (0,0) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) k).observations.observations h) k h
  refine ⟨?_,?_⟩
  · intro j
    rw [hobs,hcov,hdir]
    exact (hh p).1 j
  · intro hp hsmall
    have hscore := ControlledFamilyScoreGeometry.scoreProduct_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm
      p (0,0) ((carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) (0,0)) k).observations.observations h) (oldProfile P Λ v p) k h
    rw [hobs,hscore]
    exact (hh p).2 hp hsmall

end SHE.ControlledFamilyProfileForest
