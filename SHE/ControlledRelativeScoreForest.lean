module

public import SHE.ControlledThetaRelativeDerivative
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledFamilyProfileForest
public import SHE.UniformPhysicalProfileForest
public import SHE.ParentHeatFields
public import SHE.ControlledThetaStoppedCovariance
public import SHE.ControlledThetaAssigned
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledRelativeScoreForest
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry PhysicalParentGeometry
open scoped NNReal
local instance controlledThetaRelativeArrays_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeArrays_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeArrays_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



local notation "Zero" => Base (0,(0,0))


/-- One original history event supplies BOTH the relative old-direction
ranges and the exact positive parent-forest score envelope for ALL past
inputs. The statement includes q equal to the physical terminal time;
all original targets, clipped stops and old fractions remain intact. -/
theorem all_inputs_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ q : ℝ,(v:ℝ)≤q → q≤(carrier Zero k).terminal h → ∀ p : Inputs,
      let σ:=fun i=>stops Zero k h i-(v:ℝ)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let center:=centers Zero k h
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      let D:=directions Zero ((carrier Zero k).observations.observations h) k h
      let A:=OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ p.1 p.2) lo hi
      (∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range) ∧
      ∀ hp : StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h →
        let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
          OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
            (carrier_orderedTimes Zero hages k h hp) center
        0≤K ∧ |∏ j,MeasurableGaussianScores.scoreVariance (A j) (D j)|≤K := by
  let ell:=fraction P*P.lower
  have hell : 0<ell := mul_pos (fraction_pos P) P.lower_pos
  have hc (a : Inputs) : Measurable (oldProfile P Λ v a) :=
    (ControlledReferenceWindows.coefficient_section_measurable P Λ 0 v a).const_mul (fraction P)
  have hcb (a : Inputs) (z : StoppedGaussianFeatures.Domain) :
      ell≤oldProfile P Λ v a z ∧ oldProfile P Λ v a z≤P.lower/2 :=
    referenceProfile_bounds P Λ a.1 a.2 (z.1-(v:ℝ),z.2)
  have hfloor (z : StoppedGaussianFeatures.Domain) :
      ell≤(referenceData P P.coefficient hA Λ 0 v b hvb (0,0)).reference z := by
    have he:=referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact ((he.1.trans he.2).trans (half_le_self P.lower_pos.le)).trans
      (ControlledReferenceWindows.coefficient_bounds P Λ 0 v (0,0) z).1
  filter_upwards [uniform_all_profiles_forest_ae Zero hell hfloor (oldProfile P Λ v) hc hcb hages ρ k]
    with h hforest
  intro q hvq hqt p σ target center lo hi D A
  have hmatrix := ControlledThetaRelativeArrays.old_covariance_relative_fixed
    P hA Λ v b hvb Z htarget hstop F hF hFm (0,p) k h hvq hqt
  have hD (j) : D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range := by
    have hh:=(hforest p).1 j
    rw [hmatrix] at hh
    exact hh
  refine ⟨hD,?_⟩
  intro hp hsmall K
  have hK : 0≤K := mul_nonneg
    (timeWeight_nonneg Zero hell (uniformConstant n) (fun j=>(uniformConstant_pos n j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  refine ⟨hK,?_⟩
  have hh:=(hforest p).2 hp hsmall
  change (∏ j,MeasurableGaussianScores.scoreVariance
    (covariances Zero ((carrier Zero k).observations.observations h) (oldProfile P Λ v p) k h j)
      (D j))≤K at hh
  rw [hmatrix] at hh
  have hgeom (i) : σ i≤target i := sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hA (j) : (A j).PosSemidef := OldIntervalCovariance.covariance_posSemidef σ target center hgeom
    (referenceProfile P Λ p.1 p.2) (referenceProfile_measurable P Λ p.1 p.2)
    (fun z=>⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans
      (referenceProfile_bounds P Λ p.1 p.2 z).1,(referenceProfile_bounds P Λ p.1 p.2 z).2⟩)
    (lo j) (hi j)
  have hnonneg : 0≤∏ j,MeasurableGaussianScores.scoreVariance (A j) (D j) :=
    Finset.prod_nonneg (fun j _=>MeasurableGaussianScores.scoreVariance_nonneg (hA j) (hD j))
  simpa only [abs_of_nonneg hnonneg] using hh

end SHE.ControlledRelativeScoreForest
