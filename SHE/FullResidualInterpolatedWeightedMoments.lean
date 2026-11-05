module

public import SHE.FullResidualJointWeightedMoments
public import SHE.MixedJointInterpolationMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace SHE.FullResidualInterpolatedWeightedMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance fullResidualInterpolatedWeightedLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance fullResidualInterpolatedWeightedLocal12 : MeasurableSpace RealL2 := borel _
local instance fullResidualInterpolatedWeightedLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal14 : MeasurableSpace CircleL2 := borel _
local instance fullResidualInterpolatedWeightedLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance fullResidualInterpolatedWeightedLocal17 : MeasurableSpace RealHaarInput := borel _
local instance fullResidualInterpolatedWeightedLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullResidualInterpolatedWeightedLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) X 1)


def actualMean (k : ℕ) (q : ℝ≥0) (ω : Ω) (p : History X k) : WordRecursion.State (1+k) :=
  MixedJointInterpolationMoments.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    ((carrier L k).observations.observations p) q θ ω

include hIJ₀ hIJ₁ in
/-- Literal stop-weighted kernel moments along the ACTUAL controlled
joint interpolation path for every |theta|≤1. Every root keeps its original stop, native rough leaves have their
honest full-age BDG gain, and the Gaussian q-law is distinct from row-time
r. No uniform-theta future mean is substituted for this joint flow. -/
theorem weighted_point_even_moment_ae (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (hstop : ∀ p i,(L.observations.observations p i).stop≤L.terminal p)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ Hf Cf : ℝ,0<Hf ∧ 0<Cf ∧
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) ρ k,
      ∀ q : ℝ≥0,q≤H → (q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ r : ℝ,(q:ℝ)≤r → r<(carrier L k).terminal p →
      (∀ i,((carrier L k).observations.observations p i).target-r≤Hf) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
      let F := fun ω => ActualMeanKernel.weightedPoint L k Λ q r
        (actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q ω) p y
      let c := referenceProfile P Λ (embed u₀) (embed (v₀-u₀))
      let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
      Integrable (fun ω => |F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        FullResidualPointMoments.momentConstant P k b C0*
          (Real.sqrt (2*Cf/(P.lower*((carrier L k).terminal p-r)))*
            SharpWordTimeScale.total L P k p q A0 ν*
              ScalarMeanEnvelope.globalDensity L c k p r y)^(2*b) := by
  obtain ⟨Hf,Cf,hHf,hCf,he⟩ := FullResidualWeightedPointMoments.weighted_point_even_moment_ae μ P haP Λ
    (embed u₀) (embed (v₀-u₀)) θ L hΛ hages hstop ρ k
  refine ⟨Hf,Cf,hHf,hCf,?_⟩
  filter_upwards [he] with p hp
  intro q hqH hq hstrict r hqr hr hsmall
  filter_upwards [hp q hq hstrict r hqr hr hsmall] with y hy
  intro A0 ν hA0 hν hjet b hb0 B0 hBDG
  let Z := (carrier L k).observations.observations p
  let mean := fun ω => actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q ω p
  have hgap : ∀ i,(q:ℝ)<(Z i).target := carrier_targets_after L p hages hq
  have hm : Measurable mean := by
    exact MixedJointInterpolationMoments.mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q θ
  let p0 := b*(k+2)
  let C0 := (NativeHybridMoments.momentConstant p0 B0 κ M)^P.exponent
  have hC0 : 0≤C0 := Real.rpow_nonneg (by
    have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
    dsimp [NativeHybridMoments.momentConstant]
    exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)) _
  have hoffset (j : Fin k) : Integrable (fun ω => |mean ω (leafIndex k (fun i => i) j)-
      ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
        (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
        (((2*p0:ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
        (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
        (((2*p0:ℕ):ℝ)*P.exponent) ∂μ)≤C0*(targets L k p (leafIndex k (fun i => i) j))^((p0:ℝ)*P.exponent/2) := by
    have hnative : (Z (leafIndex k (fun i => i) j)).stop=(Z (leafIndex k (fun i => i) j)).target := by
      dsimp only [Z]
      rw [CoveredHistoryGeometry.leaf_observation L k p j]
    have hh := MixedJointInterpolationMoments.native_leaf_fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z q hΛ hgap hqH
      (hq.le.trans (((carrier L k).terminal_horizon p).trans P.horizon_le_one))
      hθ (leafIndex k (fun i => i) j) hnative p0 B0 hBDG P.exponent_pos.le P.exponent_le_one
    have hi (ω : Ω) : mean ω (leafIndex k (fun i=>i) j)=
        MixedJointInterpolationMoments.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q θ ω (leafIndex k (fun i=>i) j) := rfl
    simp_rw [hi]
    refine ⟨hh.1,hh.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow q.2 (hgap _).le
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) P.exponent_pos.le) (by norm_num))) hC0
  have hh := hy mean hm A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  have heq (ω : Ω) : ActualMeanKernel.weightedPoint L k Λ q r
      (actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q ω) p y=
      ActualMeanKernel.weightedPoint L k Λ q r (fun _ => mean ω) p y := by
    rw [ActualMeanKernel.weightedPoint_of_active L k Λ q r _ p y hq hr,
      ActualMeanKernel.weightedPoint_of_active L k Λ q r _ p y hq hr]
  exact ⟨hh.1.congr (ae_of_all _ (fun ω => congrArg (fun z : ℝ => |z|^(2*b)) (heq ω).symm)),
    (integral_congr_ae (ae_of_all _ (fun ω => congrArg (fun z : ℝ => |z|^(2*b)) (heq ω)))).trans_le hh.2⟩

end SHE.FullResidualInterpolatedWeightedMoments
