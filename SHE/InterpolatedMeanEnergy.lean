module

public import SHE.WeightedMeanInputEnergy
public import SHE.MixedCurrentInputMoments
public import SHE.InterpolatedWeightedSpatialSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.InterpolatedMeanEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance interpolatedMeanEnergy_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance interpolatedMeanEnergy_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance interpolatedMeanEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance interpolatedMeanEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance interpolatedMeanEnergy_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance interpolatedMeanEnergy_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance interpolatedMeanEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance interpolatedMeanEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance interpolatedMeanEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance interpolatedMeanEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (u₀-u₀)) θ) HeatCircle 1)

open HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope HistoryQuarterFields QuarterSpatialEvent
  FullResidualInterpolatedWeightedMoments NormalizedKernelSplit NativeRandomKernel
local notation "R₀" => ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (u₀-u₀)) θ

include hIJ₀ hIJ₁ in
/-- Actual all-depth current mean-input energy for the genuine mixed
pair and theta-interpolated Gaussian word. Every Gaussian, normalized
kernel, spatial section, input moment, and finite-energy applicability
condition is proved. The input remains correlated with every word
factor; its original global L² smallness is retained. -/
theorem actual_mean_input_energy (hΛ : 0≤Λ) (hθ : |θ|≤1) (T : ℝ)
    (hT : ∀ x,L.terminal x=T) (hroot : ∀ x,(L.observations.observations x 0).target=T)
    (hx : ∀ x,(L.observations.observations x 0).center=x)
    (hT1 : T≤1)
    (hages : ∀ x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target)
    (hstop : ∀ x i,(L.observations.observations x i).stop≤L.terminal x) (k : ℕ) :
    ∃ Hf Cf : ℝ,∃ Hs Cs : ℕ→ℝ,0<Hf ∧ 0<Cf ∧ (∀ j,0<Hs j) ∧ (∀ j,0<Cs j) ∧
    ∀ _hTHf : T≤Hf,(∀ j,j<k → T≤Hs j) →
    ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
    (∀ x j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test x) z‖≤A0*ν^j) →
    ∀ χ : ℝ,0≤χ → χ<1 → ∀ p : ℕ,0<p → 1≤(p:ℝ)*(1-χ) →
    ∀ B : ℝ≥0,StandardTerminalBDGPower ((2*p)*(k+2)) J B →
    ∀ (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ),ρ<1/2 →
    ∀ q : ℝ≥0,q≤H →
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (R₀).base (R₀).horizon)),
      active L T k q t →
      let m := actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP θ L k q
      let δ := quarterTraceTime (R:=R₀) T k q t
      let D := amplitude L P k q Cf (fraction P*P.lower) A0 ν Cs t
      let A := heatAmplitude D δ (T-q)
      let N := (2*p)*(k+2)
      let C0 := (NativeHybridMoments.momentConstant N B κ M)^P.exponent
      let CG := FullResidualPointMoments.momentConstant P k (2*p) C0
      let CD := MixedHeatedDifferenceMoments.momentConstant N B κ M^((1-χ)/(k+2:ℝ))
      let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock (T-q))^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
      Integrable (fun ω=>‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (integralOperator (weightedField L k Λ q q m t) ω (embed (S.second q ω-S.first q ω)))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (integralOperator (weightedField L k Λ q q m t) ω (embed (S.second q ω-S.first q ω)))‖^2 ∂μ)≤
        C*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)^χ := by
  obtain ⟨Hf,Cf,Hs,Cs,hHf,hCf,hHs,hCs,hspatial⟩ :=
    InterpolatedWeightedSpatialSections.normalized_quarter_moment
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P haP θ L
      hΛ hθ T hT hages hstop k
  refine ⟨Hf,Cf,Hs,Cs,hHf,hCf,hHs,hCs,?_⟩
  intro hTHf hTHs A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B hBDG mass ρ hmass hρ hρhalf q hqH
  have hp2 : 0<2*p := by omega
  have hN : 0<(2*p)*(k+2) := Nat.mul_pos hp2 (by omega)
  have hβ0 : 0≤(1-χ)/(k+2:ℝ) := div_nonneg (sub_pos.mpr hχ1).le (by positivity)
  have hβ1 : (1-χ)/(k+2:ℝ)≤1 := (div_le_one (by positivity : (0:ℝ)<k+2)).mpr (by linarith)
  have hMom := hspatial T hroot hx hTHf hTHs A0 ν hA0 hν hjet (2*p) hp2 B hBDG q hqH
  filter_upwards [hMom] with t ht
  intro ha m δ D A N C0 CG CD C
  have hqT : (q:ℝ)<T := ha.2.trans_le (by
    rw [←terminal_separated L T hT k t (0:HeatCircle) (fun _=>0)]
    exact (terminal_le_initial L k _).trans (le_of_eq (hT _)))
  have hq1 : (q:ℝ)≤1 := hqT.le.trans hT1
  have hw : 0<T-(q:ℝ) := sub_pos.mpr hqT
  have hw1 : T-(q:ℝ)≤1 := by linarith [q.2]
  obtain ⟨_,hqr,hr,hδ,_,_⟩ := quarter_geometry (R:=R₀) T k q t ha.2
  let r := quarterRowTime (R:=R₀) T k q t
  have hD0 : 0≤D := quarterAmplitude_nonneg k
    (SharpWordTimeScale.total_nonneg L P k (anchor k t) q A0 ν)
    (timeWeight_nonneg L (mul_pos (fraction_pos P) P.lower_pos) Cs (fun j=>(hCs j).le)
      k (anchor k t) ha.1)
  have hA : 0≤A := by
    change 0≤D*δ^(-(1/2:ℝ))*(T-(q:ℝ))^(1/4:ℝ)
    exact mul_nonneg (mul_nonneg hD0 (rpow_nonneg hδ.le _)) (rpow_nonneg hw.le _)
  have hm := ActualInterpolatedMeanFields.actual_mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S P haP θ L k q
  have hV := MixedHeatedDifferenceMoments.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q
  have hiV := MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ q hqH hq1 ((2*p)*(k+2)) hN B hBDG
  have hCD : 0≤CD := rpow_nonneg
    (MixedHeatedDifferenceMoments.momentConstant_nonneg (κ:=κ) hκ.le
      (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) N B) _
  have hCG : 0≤CG := FullResidualPointMoments.momentConstant_nonneg P k (2*p) C0
  have hhigh (y : HeatCircle) := MixedHeatedDifferenceMoments.fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ q hqH hq1 (sub_pos.mpr hqr) y ((2*p)*(k+2)) B hBDG hβ0 hβ1
  have hexp : (((2*((2*p)*(k+2)):ℕ):ℝ))*((1-χ)/(k+2:ℝ))=(4*(p:ℝ))*(1-χ) := by
    push_cast
    field_simp
    <;> ring
  have hhigh' (y : HeatCircle) : Integrable
      (fun ω=>|functional (r-(q:ℝ)) y (S.second q ω-S.first q ω)|^((4*(p:ℝ))*(1-χ))) μ ∧
      (∫ ω,|functional (r-(q:ℝ)) y (S.second q ω-S.first q ω)|^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD := by
    simpa only [hexp,CD,N,r] using hhigh y
  have hrel : ∀ᵐ z : HeatCircle×HeatCircle ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω,‖weightedField L k Λ q r m t (ω,z)‖^(4*p) ∂μ)≤
        CG*(A*‖ProfileVariance.heatPhysical (8*(T-q)) z.1 z.2‖)^(4*p) := by
    filter_upwards [ht ha] with z hz
    have hpow : 2*(2*p)=4*p := by omega
    simpa only [WeightedQuarterSpatialEvent.timeMoment,weightedField,hpow,heatEnvelope,CG,C0,N,A,δ,D,r] using hz
  have hh := weighted_mean_input_energy L μ T hT Λ hΛ k q r t hqr hr m hm
    (fun ω=>S.second q ω-S.first q ω) hV hiV.1 hmass hρ hρhalf hw hw1 hA hχ0 hχ1 hCD hCG
    p hp horder (fun y=>(hhigh' y).1) (fun y=>(hhigh' y).2) hrel
  exact hh

end SHE.InterpolatedMeanEnergy
