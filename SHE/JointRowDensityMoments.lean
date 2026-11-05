module

public import SHE.OffsetRowDensityMoments
public import SHE.JointMeanDisplacement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace SHE.NativeJointRowDensityMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance jointRowDensityLocal1 : Fact (0<2*π) := ⟨by positivity⟩
local instance jointRowDensityLocal2 : MeasurableSpace RealL2 := borel _
local instance jointRowDensityLocal3 : BorelSpace RealL2 := ⟨rfl⟩
local instance jointRowDensityLocal4 : MeasurableSpace CircleL2 := borel _
local instance jointRowDensityLocal5 : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointRowDensityLocal6 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance jointRowDensityLocal7 : MeasurableSpace RealHaarInput := borel _
local instance jointRowDensityLocal8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointRowDensityLocal9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointRowDensityLocal10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1) X 1)

def actualMean (k : ℕ) (q : ℝ≥0) (ω : Ω) (p : History X k) : WordRecursion.State (1+k) :=
  NativeJointHistory.evaluate 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    ((carrier L k).observations.observations p) ω (q:ℝ)

include hIJ₀ hIJ₁ in
/-- Literal separated-row kernel moments at the ACTUAL joint stopped
flow. Every root keeps its original stop, native rough leaves have their
honest full-age BDG gain, and the Gaussian q-law is distinct from row-time
r. No uniform-theta future mean is substituted for this joint flow. -/
theorem row_point_even_moment_ae (hΛ : 0≤Λ)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ Hf Cf : ℝ,0<Hf ∧ 0<Cf ∧
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1) ρ k,
      ∀ q : ℝ≥0,q≤H → (q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ r : ℝ,(q:ℝ)≤r → r<(carrier L k).terminal p →
      (∀ i,((carrier L k).observations.observations p i).target-r≤Hf) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
      let F := fun ω => ActualMeanKernel.rowPoint L k q r
        (actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP L k q ω) p y
      let c := referenceProfile P Λ (embed u₀) (embed (v₀-u₀))
      let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
      Integrable (fun ω => |F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        PhysicalOffsetPointMoments.momentConstant P k b C0*
          (Real.sqrt (Cf/(fraction P*P.lower*((carrier L k).terminal p-r)))*
            PhysicalWordTimeScale.total L P k p q A0 ν*
              ScalarMeanEnvelope.globalDensity L c k p r y)^(2*b) := by
  obtain ⟨Hf,Cf,hHf,hCf,he⟩ := OffsetRowDensityMoments.row_point_even_moment_ae μ P haP Λ
    (embed u₀) (embed (v₀-u₀)) 1 L hages ρ k
  refine ⟨Hf,Cf,hHf,hCf,?_⟩
  filter_upwards [he] with p hp
  intro q hqH hq hstrict r hqr hr hsmall
  filter_upwards [hp q hq hstrict r hqr hr hsmall] with y hy
  intro A0 ν hA0 hν hjet b hb0 B0 hBDG
  let Z := (carrier L k).observations.observations p
  let mean := fun ω => actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP L k q ω p
  have hgap : ∀ i,(q:ℝ)<(Z i).target := carrier_targets_after L p hages hq
  have hmean (ω : Ω) : NativeJointMeanDisplacement.current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q ω=mean ω :=
    NativeJointMeanDisplacement.current_eq_evaluate 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q hgap ω
  have hm : Measurable mean := by
    have hefun := funext hmean
    rw [←hefun]
    exact NativeJointMeanDisplacement.current_measurable 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q
  let p0 := b*(k+2)
  let C0 := (NativeHybridMoments.momentConstant p0 B0 κ M)^P.exponent
  have hC0 : 0≤C0 := Real.rpow_nonneg (by
    have hM : 0≤M := hell.le.trans ((hb 0).1.trans (hb 0).2)
    dsimp [NativeHybridMoments.momentConstant]
    exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)) _
  have hoffset (j : Fin k) : Integrable (fun ω => |mean ω (leafIndex k (fun i => i) j)-
      ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
        (1,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
        (((2*p0:ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
        (1,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
        (((2*p0:ℕ):ℝ)*P.exponent) ∂μ)≤C0*(targets L k p (leafIndex k (fun i => i) j))^((p0:ℝ)*P.exponent/2) := by
    have hnative : (Z (leafIndex k (fun i => i) j)).stop=(Z (leafIndex k (fun i => i) j)).target := by
      dsimp only [Z]
      rw [CoveredHistoryGeometry.leaf_observation L k p j]
    have hh := NativeJointMeanDisplacement.native_leaf_fractional_moment 𝓕 μ H Λ κ hκ ha hell hb
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z q hΛ hgap hqH
      (hq.le.trans (((carrier L k).terminal_horizon p).trans P.horizon_le_one))
      (leafIndex k (fun i => i) j) hnative p0 B0 hBDG P.exponent_pos.le P.exponent_le_one
    have hi (ω : Ω) : mean ω (leafIndex k (fun i => i) j)=
        NativeJointMeanDisplacement.current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q ω (leafIndex k (fun i => i) j) :=
      congrArg (fun z : WordRecursion.State (1+k) => z (leafIndex k (fun i => i) j)) (hmean ω).symm
    simp_rw [hi]
    refine ⟨hh.1,hh.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow q.2 (hgap _).le
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) P.exponent_pos.le) (by norm_num))) hC0
  have hh := hy mean hm A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  have heq (ω : Ω) : ActualMeanKernel.rowPoint L k q r
      (actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP L k q ω) p y=
      ActualMeanKernel.rowPoint L k q r (fun _ => mean ω) p y := by
    rw [ActualMeanKernel.rowPoint_of_active L k q r _ p y hq hr,
      ActualMeanKernel.rowPoint_of_active L k q r _ p y hq hr]
  exact ⟨hh.1.congr (ae_of_all _ (fun ω => congrArg (fun z : ℝ => |z|^(2*b)) (heq ω).symm)),
    (integral_congr_ae (ae_of_all _ (fun ω => congrArg (fun z : ℝ => |z|^(2*b)) (heq ω)))).trans_le hh.2⟩

end SHE.NativeJointRowDensityMoments

namespace SHE.MixedNativeJointRowDensityMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance jointRowDensityLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance jointRowDensityLocal12 : MeasurableSpace RealL2 := borel _
local instance jointRowDensityLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance jointRowDensityLocal14 : MeasurableSpace CircleL2 := borel _
local instance jointRowDensityLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointRowDensityLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance jointRowDensityLocal17 : MeasurableSpace RealHaarInput := borel _
local instance jointRowDensityLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointRowDensityLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointRowDensityLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1) X 1)

def actualMean (k : ℕ) (q : ℝ≥0) (ω : Ω) (p : History X k) : WordRecursion.State (1+k) :=
  MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    ((carrier L k).observations.observations p) ω (q:ℝ)

include hIJ₀ hIJ₁ in
/-- Literal separated-row kernel moments at the ACTUAL joint stopped
flow. Every root keeps its original stop, native rough leaves have their
honest full-age BDG gain, and the Gaussian q-law is distinct from row-time
r. No uniform-theta future mean is substituted for this joint flow. -/
theorem row_point_even_moment_ae (hΛ : 0≤Λ)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ Hf Cf : ℝ,0<Hf ∧ 0<Cf ∧
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1) ρ k,
      ∀ q : ℝ≥0,q≤H → (q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ r : ℝ,(q:ℝ)≤r → r<(carrier L k).terminal p →
      (∀ i,((carrier L k).observations.observations p i).target-r≤Hf) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
      let F := fun ω => ActualMeanKernel.rowPoint L k q r
        (actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP L k q ω) p y
      let c := referenceProfile P Λ (embed u₀) (embed (v₀-u₀))
      let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
      Integrable (fun ω => |F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        PhysicalOffsetPointMoments.momentConstant P k b C0*
          (Real.sqrt (Cf/(fraction P*P.lower*((carrier L k).terminal p-r)))*
            PhysicalWordTimeScale.total L P k p q A0 ν*
              ScalarMeanEnvelope.globalDensity L c k p r y)^(2*b) := by
  obtain ⟨Hf,Cf,hHf,hCf,he⟩ := OffsetRowDensityMoments.row_point_even_moment_ae μ P haP Λ
    (embed u₀) (embed (v₀-u₀)) 1 L hages ρ k
  refine ⟨Hf,Cf,hHf,hCf,?_⟩
  filter_upwards [he] with p hp
  intro q hqH hq hstrict r hqr hr hsmall
  filter_upwards [hp q hq hstrict r hqr hr hsmall] with y hy
  intro A0 ν hA0 hν hjet b hb0 B0 hBDG
  let Z := (carrier L k).observations.observations p
  let mean := fun ω => actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP L k q ω p
  have hgap : ∀ i,(q:ℝ)<(Z i).target := carrier_targets_after L p hages hq
  have hmean (ω : Ω) : MixedNativeJointMeanDisplacement.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q ω=mean ω :=
    MixedNativeJointMeanDisplacement.current_eq_evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q hgap ω
  have hm : Measurable mean := by
    have hefun := funext hmean
    rw [←hefun]
    exact MixedNativeJointMeanDisplacement.current_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q
  let p0 := b*(k+2)
  let C0 := (NativeHybridMoments.momentConstant p0 B0 κ M)^P.exponent
  have hC0 : 0≤C0 := Real.rpow_nonneg (by
    have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
    dsimp [NativeHybridMoments.momentConstant]
    exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)) _
  have hoffset (j : Fin k) : Integrable (fun ω => |mean ω (leafIndex k (fun i => i) j)-
      ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
        (1,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
        (((2*p0:ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
        (1,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
        (((2*p0:ℕ):ℝ)*P.exponent) ∂μ)≤C0*(targets L k p (leafIndex k (fun i => i) j))^((p0:ℝ)*P.exponent/2) := by
    have hnative : (Z (leafIndex k (fun i => i) j)).stop=(Z (leafIndex k (fun i => i) j)).target := by
      dsimp only [Z]
      rw [CoveredHistoryGeometry.leaf_observation L k p j]
    have hh := MixedNativeJointMeanDisplacement.native_leaf_fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z q hΛ hgap hqH
      (hq.le.trans (((carrier L k).terminal_horizon p).trans P.horizon_le_one))
      (leafIndex k (fun i => i) j) hnative p0 B0 hBDG P.exponent_pos.le P.exponent_le_one
    have hi (ω : Ω) : mean ω (leafIndex k (fun i => i) j)=
        MixedNativeJointMeanDisplacement.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q ω (leafIndex k (fun i => i) j) :=
      congrArg (fun z : WordRecursion.State (1+k) => z (leafIndex k (fun i => i) j)) (hmean ω).symm
    simp_rw [hi]
    refine ⟨hh.1,hh.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow q.2 (hgap _).le
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) P.exponent_pos.le) (by norm_num))) hC0
  have hh := hy mean hm A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  have heq (ω : Ω) : ActualMeanKernel.rowPoint L k q r
      (actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP L k q ω) p y=
      ActualMeanKernel.rowPoint L k q r (fun _ => mean ω) p y := by
    rw [ActualMeanKernel.rowPoint_of_active L k q r _ p y hq hr,
      ActualMeanKernel.rowPoint_of_active L k q r _ p y hq hr]
  exact ⟨hh.1.congr (ae_of_all _ (fun ω => congrArg (fun z : ℝ => |z|^(2*b)) (heq ω).symm)),
    (integral_congr_ae (ae_of_all _ (fun ω => congrArg (fun z : ℝ => |z|^(2*b)) (heq ω)))).trans_le hh.2⟩

end SHE.MixedNativeJointRowDensityMoments
