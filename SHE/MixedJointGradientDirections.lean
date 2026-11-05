module
public import SHE.NativeJointColumnDirections
public import SHE.MixedJointNamedIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MixedJointGradientDirections
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open MixedNativeJointObservations PhysicalMeanRange StoppedGaussianScore
open NativeJointColumnDirections
open scoped NNReal ENNReal
local instance mixedNativeJointPastIto_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeJointPastIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeJointPastIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeJointPastIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeJointPastIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeJointPastIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ)
variable {n:ℕ} (Z:Fin n→WordRecursion.Observation) (b:ℝ≥0)
variable (hgap:∀i,(b:ℝ)<(Z i).target) (hbH:b≤H)

local notation "Rows"=>rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ
local notation "Y"=>MixedJointNamedIto.path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b
local notation "Target"=>(fun i=>(Z i).target)
local notation "Stop"=>(fun i=>(Z i).stop)
local notation "Center"=>(fun i=>NativeHeatSpan.unitCenter (Z i).center)
local notation "cU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "cV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "ColU"=>(fun p k=>CircleNormalization.push (globalHaarColumn k (cU p).1))
local notation "ColV"=>(fun p k=>CircleNormalization.push (globalHaarColumn k (cV p).1))
local notation "Col0"=>(fun k=>CircleNormalization.push (globalHaarColumn k (AdditiveHaarForcing.constantField κ hκ).1))

/-- Both actual original-joint Haar directions, on one original energy
measure event. The residual direction retains its original stop damping. -/
theorem directions_ae:
    ∀ᵐp∂energyMeasure μ H,p.1<b → ∀k:HaarNode,
      FiniteItoGradientAction.direction 𝓕 μ H Rows (left k) p=
        currentDirection Target Center p.1 (Col0 k) ∧
      FiniteItoGradientAction.direction 𝓕 μ H Rows (right k) p=
        currentDirection Target Center p.1 (ColU p k)+
          dampedDirection Stop Target Center p.1 Λ (ColV p k-ColU p k):=by
  have hr:=MixedNativeJointPhysicalRows.rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b hgap
  filter_upwards [hr] with p hp hpb k
  have hpb':(p.1:ℝ)<(b:ℝ):=by exact_mod_cast hpb
  have hq:∀i,(p.1:ℝ)<(Z i).target:=fun i=>hpb'.trans (hgap i)
  have he:∀i,Rows i p=physical hell hκ (cU p) (cV p) Stop Target Center p.1 Λ i:=by
    intro i
    rw [hp hpb i]
    simp only [MixedNativeJointPhysicalRows.physicalRow,MixedNativeJointPhysicalRows.additiveRow,
      MixedNativeJointPhysicalRows.firstRow,MixedNativeJointPhysicalRows.secondRow,
      physical,nativeCenter,NativeHeatSpan.scale_inverse]
  constructor
  · change WithLp.toLp 2 (fun i=>left k (Rows i p))=_
    simp_rw [he]
    exact left_direction hell hκ (cU p) (cV p) Stop Target Center p.1 Λ hq k
  · change WithLp.toLp 2 (fun i=>right k (Rows i p))=_
    simp_rw [he]
    exact right_direction hell hκ (cU p) (cV p) Stop Target Center p.1 Λ hq k

/-- The FULL actual finite-Ito gradient row evaluates on these exact
physical directions; no separate noise witness or derivative block. -/
theorem gradient_actions_ae (G:ℝ→WordRecursion.State n→ℝ):
    ∀ᵐp∂energyMeasure μ H,p.1<b → ∀k:HaarNode,
      left k (FiniteItoNoise.gradientRow 𝓕 μ H Y Rows G p)=
        fderiv ℝ (G (p.1:ℝ)) (Y p) (currentDirection Target Center p.1 (Col0 k)) ∧
      right k (FiniteItoNoise.gradientRow 𝓕 μ H Y Rows G p)=
        fderiv ℝ (G (p.1:ℝ)) (Y p)
          (currentDirection Target Center p.1 (ColU p k)+
            dampedDirection Stop Target Center p.1 Λ (ColV p k-ColU p k)):=by
  filter_upwards [directions_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ Z b hgap] with p hp hpb k
  constructor
  · rw [FiniteItoGradientAction.action,(hp hpb k).1]
  · rw [FiniteItoGradientAction.action,(hp hpb k).2]
end SHE.MixedJointGradientDirections
