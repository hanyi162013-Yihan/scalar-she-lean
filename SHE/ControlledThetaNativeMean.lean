module

public import SHE.ControlledThetaNativeGradient
public import SHE.ProfileReserveTotalMark
public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledThetaNativeAssignments
public import SHE.TwoFreshCompleteWord
public import SHE.ControlledThetaConsistentNative
public import SHE.NativeFirstWholeComplete
public import SHE.NativeFirstOmittedPointwise
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

namespace SHE.ControlledThetaNativeMean
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal BigOperators
local instance controlledThetaNativeMean_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaNativeMean_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaNativeMean_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The literal affine-current leg of the native-first-score FTC is
the COMPLETE false-score packet. One history event works for every
past input, interpolation parameter and current direction. -/
theorem affine_mean_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀(base E V:WordRecursion.State (n+k)),
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) Rnative).range→
      V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range→
      let A:=covariances (Base p) ((carrier (Base p) k).observations.observations h) (oldProfile P Λ v p.2) k h
      let D:=directions (Base p) ((carrier (Base p) k).observations.observations h) k h
      GaussianRangeSmooth.ProfileReserve.affineMeanMark
        (fun η=>fullResidualCovariance (Base (η,p.2)) (oldProfile P Λ v p.2) k h q-Rnative)
        (WeightedBorelAverage.average
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
            (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
          (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
          (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i)))
        base V p.1=
      TwoFreshCompleteWord.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) (base+p.1•V) false
        (directions Zero ((carrier Zero k).observations.observations h) k h) E V
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaNativeAssignments.score_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaRelativeNativeWord.assigned_integral_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaTwoFreshArrays.residual_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hscore hrelative hres
  intro p q hvq hqt base E V Rnative C hE hV A D
  have hage(i:Fin (n+k)):stops (Base p) k h i≤targets (Base p) k h i:=
    (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages (Base p) hages k h i)
  have hR:Rnative.PosSemidef:=NativeFirstScoreReserve.covariance_posSemidef P _ _ _ hage q
  have hage0(i:Fin (n+k)):stops Zero k h i-(v:ℝ)≤targets Zero k h i-(v:ℝ):=
    sub_le_sub_right ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hC:C.PosSemidef:=by
    rw [show C=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-
      NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q from rfl,hres p q hvq hqt]
    exact NativeFirstScoreRepresentation.residual_posSemidef P Λ p.2.1 p.2.2
      (fixedProfile P Λ p.2.1 p.2.2 (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)))
      (fixedProfile_measurable P Λ _ _ _ _)
      (fixedProfile_bounds P Λ _ _ _ _ (RelativeHistoryGeometry.relative_disjoint Zero k h))
      _ _ _ hage0 (q-(v:ℝ)) p.1
  have hs:=hscore p false Rnative C hR hC E V (base+p.1•V) hE hV
  have heq : GaussianRangeSmooth.ProfileReserve.affineMeanMark
      (fun η=>fullResidualCovariance (Base (η,p.2)) (oldProfile P Λ v p.2) k h q-Rnative)
      (WeightedBorelAverage.average
        ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
          (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
        (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
        (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i)))
      base V p.1=
      WeightedBorelAverage.average (multivariateGaussian (0:WordRecursion.State (n+k)) C)
        (GaussianDependentScores.factor false C V) id
        (WeightedBorelAverage.average
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
            (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
          (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
          (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i))) (base+p.1•V):=by
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>mul_comm _ _)
  rw [heq,hs]
  unfold TwoFreshCompleteWord.value
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices _
  exact hrelative p q hvq hqt (base+p.1•V) false E V choices

end SHE.ControlledThetaNativeMean

