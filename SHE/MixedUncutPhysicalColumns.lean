module

public import SHE.MixedUncutPhysicalGradient
public import SHE.NativeJointColumnDirections
public import SHE.MixedNativeGradientColumns
public import SHE.ActualMeanKernel
public import SHE.MixedLevelOriginalAverage
public import SHE.MixedCanonicalGradientKernel
public import SHE.TerminalItoRawAverage
public import SHE.RootHeatGradientContinuity
public import SHE.MixedHeatNoiseL2Limit
public import SHE.RootMixedNoiseL2Limit
public import SHE.TerminalItoClosedLimit
public import SHE.TerminalItoAverageWitness
public import SHE.MixedJointIntegratedLevel
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedUncutPhysicalColumns
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω P : Type} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories CutoffCarriers GaussianConvolution
variable (k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "Obs"=>(NL).observations.observations
local notation "Term"=>(NL).terminal
local notation "Raw"=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k
local notation "Mean"=>MixedLevelPhysicalGradient.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S NL
local notation "Rows"=>MixedNativeJointPhysicalRows.physicalRow
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

/-- Every coordinate of the literal uncut predictable input is the
FULL original Gaussian-word derivative, with its normalization kept
exactly once. This identity is pointwise on the original current window. -/
theorem action (ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:History P k×(ℝ≥0×Ω))
    (hq:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Term z.1):
    ℓ (Raw z)=
      fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference (Obs z.1)
        (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)) (Mean z)
        (WithLp.toLp 2 (fun i:Fin (n+k)=>ℓ (Rows (Obs z.1) z.2 i))):=by
  let w:=UncutSmoothWords.weight L k z.1
  have ha:gaussianAverage (WordRecursion.covariance R.reference (Obs z.1)
      (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)=
      w • GaussianItoTest.backward ((NL).window z.1) ((NL).test z.1) (z.2.1:ℝ):=by
    rw [UncutSmoothWords.test_eq_weight_normalized]
    change GaussianSmooth.average _ (w • (NL).test z.1)=_
    rw [NormalizedInsertion.average_smul]
    congr 1
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (WordRecursion.covariance R.reference (Obs z.1) (z.2.1:ℝ) (Term z.1))) _ =
      GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (WordRecursion.covariance R.reference (Obs z.1)
        (ClippedCovariance.clip R.base (Term z.1) (z.2.1:ℝ)) (Term z.1))) _
    rw [ClippedCovariance.clip_eq ⟨hq.1.le,hq.2.le⟩]
  rw [ha,fderiv_const_smul_field]
  rw [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,ite_eq_left hq,map_smul,map_sum]
  rw [FiniteItoGradientAction.coordinates]
  simp only [ContinuousLinearMap.smul_apply,Pi.smul_apply,map_smul,smul_eq_mul,WithLp.ofLp_toLp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original zero-extended full Gaussian derivative in a literal
physical noise-row coordinate. -/
def coordinate (ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:History P k×(ℝ≥0×Ω)):ℝ:=
  if R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Term z.1 then
    fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference (Obs z.1)
      (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)) (Mean z)
      (WithLp.toLp 2 (fun i:Fin (n+k)=>ℓ (Rows (Obs z.1) z.2 i)))
  else 0

theorem coordinate_eq (ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:History P k×(ℝ≥0×Ω)):
    ℓ (Raw z)=coordinate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k ℓ z:=by
  by_cases hq:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Term z.1
  · rw [coordinate,if_pos hq]
    exact action 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k ℓ z hq
  · simp only [coordinate,ite_eq_right hq,MixedUncutPhysicalGradient.raw,
      MixedLevelPhysicalGradient.raw,ite_eq_right hq,smul_zero,map_zero]

private theorem physical_eq (z:History P k×(ℝ≥0×Ω)):
    NativeJointColumnDirections.physical hell hκ (CU z.2) (CV z.2)
      (fun i=>(Obs z.1 i).stop) (fun i=>(Obs z.1 i).target)
      (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ) Λ=Rows (Obs z.1) z.2:=by
  funext i
  have hc:StoppedGaussianScore.nativeCenter (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) i=
      (Obs z.1 i).center:=NativeHeatSpan.scale_inverse _
  simp only [NativeJointColumnDirections.physical,MixedNativeJointPhysicalRows.physicalRow,
    MixedNativeJointPhysicalRows.additiveRow,MixedNativeJointPhysicalRows.firstRow,
    MixedNativeJointPhysicalRows.secondRow,hc]

/-- Both actual original Haar channels act on the full uncut word;
the right channel retains U plus the stopped damped V-minus-U direction. -/
theorem channels (z:History P k×(ℝ≥0×Ω))
    (hq:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Term z.1)
    (hT:∀i,(z.2.1:ℝ)<(Obs z.1 i).target)(j:HaarNode):
    let D:=fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference (Obs z.1)
      (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)) (Mean z)
    NativeJointColumnDirections.left j (Raw z)=D
      (PhysicalMeanRange.currentDirection (fun i=>(Obs z.1 i).target)
        (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1))) ∧
    NativeJointColumnDirections.right j (Raw z)=D
      (PhysicalMeanRange.currentDirection (fun i=>(Obs z.1 i).target)
        (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (CU z.2).1))+
      PhysicalMeanRange.dampedDirection (fun i=>(Obs z.1 i).stop) (fun i=>(Obs z.1 i).target)
        (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ) Λ
        (CircleNormalization.push (globalHaarColumn j (CV z.2).1)-
         CircleNormalization.push (globalHaarColumn j (CU z.2).1))):=by
  intro D
  constructor
  · rw [action 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k _ z hq]
    rw [←physical_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z]
    rw [NativeJointColumnDirections.left_direction hell hκ (CU z.2) (CV z.2)
      (fun i=>(Obs z.1 i).stop) (fun i=>(Obs z.1 i).target)
      (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ) Λ hT j]
  · rw [action 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k _ z hq]
    rw [←physical_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z]
    rw [NativeJointColumnDirections.right_direction hell hκ (CU z.2) (CV z.2)
      (fun i=>(Obs z.1 i).stop) (fun i=>(Obs z.1 i).target)
      (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ) Λ hT j]

end SHE.MixedUncutPhysicalColumns
