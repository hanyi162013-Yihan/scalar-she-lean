module

public import SHE.PhysicalNativeOmittedAssignments
public import SHE.ControlledThetaSupported

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SHE.ControlledThetaNativeAssignments
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord GaussianConvolution GaussianAssignmentBlocks GaussianDependentScores MeasurableGaussianScores
open scoped NNReal BigOperators
local instance controlledThetaNativeAssignments_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledThetaNativeAssignments_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledThetaNativeAssignments_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable {X:Type} [MeasurableSpace X] {n:ℕ} (Z:VariableObservations.Family X n)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State n=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

/-- ONE original-history event identifies the complete native-first
mean/covariance assigned sums for ALL interpolation and past data. The
random past covariance may therefore be evaluated after this theorem. -/
theorem score_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀(second:Bool) (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)),
      Rnative.PosSemidef→C.PosSemidef→∀(E V mean:WordRecursion.State (n+k)),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) Rnative).range→
      V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range→
      let A:=covariances (Base p) ((carrier (Base p) k).observations.observations h) (oldProfile P Λ v p.2) k h
      let D:=directions (Base p) ((carrier (Base p) k).observations.observations h) k h
      WeightedBorelAverage.average (multivariateGaussian (0:WordRecursion.State (n+k)) C)
        (factor second C V) id
        (WeightedBorelAverage.average
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
            (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
          (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,secondScore (A j) (D j) (old j)))
          (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i))) mean=
      (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
        ∫z,twoFreshWord (Base p) (oldProfile P Λ v p.2) k h second Rnative C E V mean choices z
          ∂twoFreshMeasure (Base p) (oldProfile P Λ v p.2) k h Rnative C)).sum:=by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p second Rnative C hR hC E V mean hE hV
  obtain ⟨chain,_,_,hphysical⟩:=hh p
  exact two_fresh_score_average_of_chain (Base p) (oldProfile P Λ v p.2)
    chain hphysical second Rnative C hR hC E V mean hE hV

/-- The same common-parameter discipline for every actual erased
baseline. Native first score remains present, C is unscored, and each
original normalization and baseline is preserved. -/
theorem omitted_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀(Rnative C:MeasurableGeneralizedInverse.Mat (n+k))
        (E mean:WordRecursion.State (n+k)) (j0:Fin k),
      nativeOmittedAverage (Base p) (oldProfile P Λ v p.2) k h Rnative C E mean j0=
        (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
          ∫z,nativeOmittedAssignedWord (Base p) (oldProfile P Λ v p.2) k h Rnative E mean choices j0 z
            ∂twoFreshMeasure (Base p) (oldProfile P Λ v p.2) k h Rnative C)).sum:=by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p Rnative C E mean j0
  obtain ⟨chain,_,_,hphysical⟩:=hh p
  exact native_omitted_average_of_chain (Base p) (oldProfile P Λ v p.2)
    chain hphysical Rnative C E mean j0

end SHE.ControlledThetaNativeAssignments
