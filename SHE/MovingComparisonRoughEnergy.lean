module

public import SHE.MovingComparisonCutoffConvergence
public import SHE.MovingComparisonDecay
public import SHE.MovingComparisonCutoffIdentity
public import SHE.HilbertCutoffIdentification
public import SHE.ScalarRootBands
public import SHE.DyadicBandEnergy
public import SHE.HilbertBandTails
public import SHE.MovingComparisonFrequency
public import SHE.MovingComparisonGlobal
public import SHE.MovingComparisonField
public import SHE.ThreeLegEnergyIntegration
public import SHE.MovingComparisonSection
public import SHE.MovingMarkRootGlobalEnergy
public import SHE.MovingMeanGlobalL2
public import SHE.NegativeThreeLeg
public import SHE.MixedPastMeanRootL1
public import SHE.MovingRootThreeLeg
public import SHE.MovingMeanRootRealization
public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingComparisonRoughEnergy
open Filter
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonRoughEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonRoughEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonRoughEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonRoughEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonRoughEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonRoughEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonRoughEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonRoughEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonRoughEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonRoughEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

local notation "End"=>MovingComparisonSection.endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "CF"=>MovingMarkRootTheta.covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BF"=>MovingMarkRootTheta.baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "MF"=>MovingMeanPhysicalField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

variable {a : ℝ→ℝ} (ha : Continuous a) {B K β : ℝ} (hB : ∀ x,|a x|≤B)
variable (hK : 0≤K) (hβ : 0<β) (hβ1 : β≤1)
variable (hholder : ∀ x y,|a x-a y|≤K*|x-y|^β)
variable (ψ : HeatCircle→ℝ) (hψm : Measurable ψ) {W0 : ℝ} (hW : 0≤W0) (hψ : ∀ x,|ψ x|≤W0)

local instance movingComparisonRoughEnergy_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

def bandField (k : ℕ) (mass ρ : ℝ) (j : ℕ) : ℝ×(ℝ×Ω)→CircleL2 :=
  MovingComparisonHilbert.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop (ScalarRootBands.test a ψ j)
      (ScalarRootBands.test_uniform ha hB ψ hW hψ j)
      (ScalarRootBands.test_measurable ha hB ψ hψm j) k mass ρ

local notation "V"=>bandField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop ha hB ψ hψm hW hψ


def cutoffField (k : ℕ) (mass ρ : ℝ) (J0 : ℕ) : ℝ×(ℝ×Ω)→CircleL2:=
  MovingComparisonHilbert.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop (RootSmoothSums.rootSum (ScalarRootBands.test a ψ) (Finset.range J0))
      (RootSmoothSums.rootSum_uniform _ (ScalarRootBands.test_uniform ha hB ψ hW hψ) _)
      (RootSmoothSums.rootSum_measurable _ (ScalarRootBands.test_measurable ha hB ψ hψm) _) k mass ρ
local notation "Cut"=>cutoffField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop ha hB ψ hψm hW hψ

include hIJ₀ hIJ₁ hK hβ hβ1 hholder in
theorem actual_rough_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1) (hh : 0<h)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0 : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (ρ : ℝ) (hmass : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ε : ℝ) (hε : 0≤ε) (hερ : 2*ε<ρ) :
    let σ:=(volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod ((volume.restrict (Ioc (0:ℝ) (h:ℝ))).prod μ)
    let E:=MovingComparisonDecay.decayCost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
      k ρ χ p Babs B0 ε β
    ∃ (hm : ∀ j,Measurable (V k Λ ρ j))
      (hi : ∀ j,Integrable (fun z=>‖V k Λ ρ j z‖^2) σ)
      (he : ∀ J0,Cut k Λ ρ J0=ᵐ[σ](fun z=>∑ j∈Finset.range J0,V k Λ ρ j z)),
      Tendsto (HilbertBandTails.cutoffVector σ (V k Λ ρ) hm hi (Cut k Λ ρ) he)
        Filter.atTop (nhds (∑' j,HilbertBandTails.vector σ (V k Λ ρ) hm hi j)) ∧
      ‖∑' j,HilbertBandTails.vector σ (V k Λ ρ) hm hi j‖^2≤
        Λ^(-2*ε)*(W0*ScalarBandBernstein.amplitude B K k)^2*(2:ℝ)^β*
          (StateBands.geometricConstant (β/2))^2*E := by
  intro σ E
  obtain ⟨hm,hi,he,hconv,htail⟩:=MovingComparisonCutoffConvergence.actual_cutoff_convergence
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop
    J hIJ₀ hIJ₁ ha hB hK hβ hβ1 hholder ψ hψm hW hψ
    hlocal hΛ hH hh hsmallPoint hsmallL2 hages hrootStop hrootTarget hcenter hspan k hfresh hold
    χ hχ0 hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG Λ ρ hmass hρ hρhalf ε hε hερ
  refine ⟨hm,hi,he,hconv,?_⟩
  let A:=W0*ScalarBandBernstein.amplitude B K k
  let C:=MovingComparisonL2.cost 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h k Λ ρ χ p Babs B0 ε β
  let D:=DyadicBandEnergy.scale β 0 1 C A
  let G:=StateBands.geometricConstant (β/2)
  have hA : 0≤A:=mul_nonneg hW (ScalarBandBernstein.amplitude_nonneg hK k)
  have hC : 0≤C:=abs_nonneg _
  have hD : 0≤D:=DyadicBandEnergy.scale_nonneg (by norm_num) hA
  have hG : 0≤G:=inv_nonneg.mpr (by linarith [(StateBands.geometric_ratio (show 0<β/2 by linarith)).2])
  have hn : ‖∑' j,HilbertBandTails.vector σ (V k Λ ρ) hm hi j‖≤D*G := by
    have ht:=htail 0
    rw [HilbertBandTails.cutoffVector_eq] at ht
    simp only [Finset.range_zero,Finset.sum_empty,sub_zero,pow_zero,Real.one_rpow,mul_one] at ht
    convert! ht using 1 <;> rfl
  have hDs : D^2=A^2*((2:ℝ)^β*C) := by
    dsimp only [D,DyadicBandEnergy.scale]
    rw [Real.one_rpow,mul_one,mul_pow,Real.sq_sqrt (by positivity)]
    rw [abs_of_nonneg hC]
  have hc:=MovingComparisonDecay.cost_decay 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
    hmass k ρ χ p Babs B0 ε β hερ.le
  calc
    _≤(D*G)^2:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hG)).mpr hn
    _=A^2*(2:ℝ)^β*G^2*C:=by rw [mul_pow,hDs];ring
    _≤A^2*(2:ℝ)^β*G^2*(Λ^(-2*ε)*E):=mul_le_mul_of_nonneg_left hc (by positivity)
    _=_:=by ring

end SHE.MovingComparisonRoughEnergy
