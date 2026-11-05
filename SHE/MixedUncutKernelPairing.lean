module

public import SHE.MixedUncutPhysicalColumns
public import SHE.StopWeightedInput
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

namespace SHE.MixedUncutKernelPairing
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

/-- Exact native L2 kernel pairing for an arbitrary real Gaussian
functional in an original current heat direction. -/
theorem functional_current {m:ℕ}(D:WordRecursion.State m→L[ℝ]ℝ)
    (Z:Fin m→WordRecursion.Observation)(q:ℝ)(hT:∀i,q<(Z i).target)(f:CircleL2):
    D (PhysicalMeanRange.currentDirection (fun i=>(Z i).target)
      (fun i=>NativeHeatSpan.unitCenter (Z i).center) q f)=
      (FiniteHeatRows.functional D Z q f).re:=by
  rw [FiniteHeatRows.apply_eq_sum]
  change (∑i:Fin m,FiniteHeatRows.coefficient D i*
    PhysicalProfile.physicalHeatMean f ((Z i).target-q,
      StoppedGaussianScore.nativeCenter (fun i=>NativeHeatSpan.unitCenter (Z i).center) i))=_
  change _=(inner ℂ (FiniteHeatRows.kernel D Z q) f).re
  rw [FiniteHeatRows.kernel,sum_inner,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left,Complex.conj_ofReal,PhysicalProfile.physicalHeatMean_eq (sub_pos.mpr (hT i))]
  have hc:StoppedGaussianScore.nativeCenter (fun i=>NativeHeatSpan.unitCenter (Z i).center) i=(Z i).center:=
    NativeHeatSpan.scale_inverse _
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- The actual uncut SAME-J rows are the exact signed native current
and stop-weighted kernel pairings. In particular the V-minus-U Haar
column is not replaced by an effective coefficient or a proxy law. -/
theorem channels (z:History P k×(ℝ≥0×Ω))
    (hq:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Term z.1)
    (hT:∀i,(z.2.1:ℝ)<(Obs z.1 i).target)(j:HaarNode):
    let D:=fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference (Obs z.1)
      (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)) (Mean z)
    NativeJointColumnDirections.left j (Raw z)=
      (FiniteHeatRows.functional D (Obs z.1) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1))).re ∧
    NativeJointColumnDirections.right j (Raw z)=
      (FiniteHeatRows.functional D (Obs z.1) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (CU z.2).1))).re+
      (FiniteHeatRows.functional (D.comp (StopWeightedRows.diagonal (StopWeightedRows.weights Λ (Obs z.1) (z.2.1:ℝ))))
        (Obs z.1) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (CV z.2).1)-
          CircleNormalization.push (globalHaarColumn j (CU z.2).1))).re:=by
  intro D
  obtain ⟨hL,hR⟩:=MixedUncutPhysicalColumns.channels
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z hq hT j
  constructor
  · exact hL.trans (functional_current _ _ _ hT _)
  · rw [hR,map_add,functional_current D (Obs z.1) (z.2.1:ℝ) hT]
    rw [StopWeightedInput.functional_dampedDirection D Λ (z.2.1:ℝ) (Obs z.1) hT]

end SHE.MixedUncutKernelPairing
