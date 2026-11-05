module

public import SHE.NativeJointColumnDirections
public import SHE.FiniteItoGradientAction
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeGradientColumns
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeGradientColumns_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeGradientColumns_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeGradientColumns_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeGradientColumns_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeGradientColumns_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeGradientColumns_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "σ"=>(fun i=>(Z i).stop)
local notation "Target"=>(fun i=>(Z i).target)
local notation "Center"=>(fun i=>NativeHeatSpan.unitCenter (Z i).center)

private theorem physical_eq (p:ℝ≥0×Ω):
    NativeJointColumnDirections.physical hell hκ (CU p) (CV p) σ Target Center (p.1:ℝ) Λ=
      MixedNativeJointPhysicalRows.physicalRow
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p:=by
  funext i
  have hc:StoppedGaussianScore.nativeCenter Center i=(Z i).center:=NativeHeatSpan.scale_inverse _
  simp only [NativeJointColumnDirections.physical,MixedNativeJointPhysicalRows.physicalRow,
    MixedNativeJointPhysicalRows.additiveRow,MixedNativeJointPhysicalRows.firstRow,
    MixedNativeJointPhysicalRows.secondRow,hc]

variable (hΛ:0≤Λ)(b:ℝ≥0)(hgap:∀i,(b:ℝ)<(Z i).target)
local notation "Rows"=>MixedNativeJointObservations.rows
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ

/-- On one original time/sample event, EVERY Haar coordinate of the
full finite-Ito gradient is exactly its actual native physical column
direction. The residual keeps every original stopping weight. -/
theorem gradient_columns_ae:
    ∀ᵐp∂energyMeasure μ H,p.1<b→
      ∀(Y:ℝ≥0×Ω→WordRecursion.State n)(G:ℝ→WordRecursion.State n→ℝ)(j:HaarNode),
      NativeJointColumnDirections.left j (FiniteItoNoise.gradientRow 𝓕 μ H Y Rows G p)=
        fderiv ℝ (G (p.1:ℝ)) (Y p)
          (PhysicalMeanRange.currentDirection Target Center (p.1:ℝ)
            (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1))) ∧
      NativeJointColumnDirections.right j (FiniteItoNoise.gradientRow 𝓕 μ H Y Rows G p)=
        fderiv ℝ (G (p.1:ℝ)) (Y p)
          (PhysicalMeanRange.currentDirection Target Center (p.1:ℝ)
              (CircleNormalization.push (globalHaarColumn j (CU p).1))+
            PhysicalMeanRange.dampedDirection σ Target Center (p.1:ℝ) Λ
              (CircleNormalization.push (globalHaarColumn j (CV p).1)-
                CircleNormalization.push (globalHaarColumn j (CU p).1))):=by
  filter_upwards [MixedNativeJointPhysicalRows.rows_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b hgap] with p hp hpb Y G j
  have hpbR:(p.1:ℝ)<(b:ℝ):=by exact_mod_cast hpb
  have hq:∀i,(p.1:ℝ)<Target i:=fun i=>hpbR.trans (hgap i)
  have hL:FiniteItoGradientAction.direction 𝓕 μ H Rows (NativeJointColumnDirections.left j) p=
      PhysicalMeanRange.currentDirection Target Center (p.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)):=by
    unfold FiniteItoGradientAction.direction
    simp_rw [hp hpb]
    rw [←physical_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p]
    exact NativeJointColumnDirections.left_direction hell hκ (CU p) (CV p) σ Target Center (p.1:ℝ) Λ hq j
  have hR:FiniteItoGradientAction.direction 𝓕 μ H Rows (NativeJointColumnDirections.right j) p=
      PhysicalMeanRange.currentDirection Target Center (p.1:ℝ)
          (CircleNormalization.push (globalHaarColumn j (CU p).1))+
        PhysicalMeanRange.dampedDirection σ Target Center (p.1:ℝ) Λ
          (CircleNormalization.push (globalHaarColumn j (CV p).1)-
            CircleNormalization.push (globalHaarColumn j (CU p).1)):=by
    unfold FiniteItoGradientAction.direction
    simp_rw [hp hpb]
    rw [←physical_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p]
    exact NativeJointColumnDirections.right_direction hell hκ (CU p) (CV p) σ Target Center (p.1:ℝ) Λ hq j
  constructor
  · rw [FiniteItoGradientAction.action,hL]
  · rw [FiniteItoGradientAction.action,hR]

end SHE.MixedNativeGradientColumns
