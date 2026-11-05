module

public import SHE.MixedNativeEndpointRootSums
public import SHE.RootSmoothSums
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

namespace SHE.MovingComparisonRootSums
open RootSmoothSums
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonRootSums_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonRootSums_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonRootSums_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonRootSums_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonRootSums_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonRootSums_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonRootSums_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonRootSums_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonRootSums_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonRootSums_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : ℕ→HeatCircle→WordRecursion.State 1→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
variable (hFm : ∀ j,Measurable (fun z : HeatCircle×WordRecursion.State 1=>F j z.1 z.2))




variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
theorem section_sum_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hH : (H:ℝ)≤1)
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
    (Bpast Babs : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) (a : Finset ℕ) :
    (fun z : Ω×HeatCircle=>MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a)
        k ((v:ℝ),((s:ℝ),z)))=ᵐ[μ.prod haarAddCircle]
      fun z=>∑ j∈a,MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop (F j) (hF j) (hFm j) k ((v:ℝ),((s:ℝ),z)) := by
  let ZT:=ObservationFamilyTimeShift.family (v:ℝ) Z
  let HT:=ControlledWordTimeShift.translatedTargets h Z htarget v
  let HS:=ControlledWordTimeShift.translatedStops h Z hstop v
  have he (G : HeatCircle→WordRecursion.State 1→ℝ) (hg : UniformBoundedSmooth G)
      (hgm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>G z.1 z.2)) :
      (fun z : Ω×HeatCircle=>MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop G hg hgm k ((v:ℝ),((s:ℝ),z)))=ᵐ[μ.prod haarAddCircle]
        MovingComparisonSection.endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP h Z htarget hstop G hg hgm k v s := by
    obtain ⟨A,hA,hjet⟩:=hg.finite_jet_bound k
    exact MovingComparisonField.field_eq_endpoint_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop G hg hgm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
      hages hrootStop hrootTarget hcenter hspan k hfresh hold A 1 hA (by norm_num) hjet
      Bpast Babs hBDGpast hBDGabs v s hvH hs hsh
  have h0:=MixedNativeEndpointRootSums.endpoint_sum_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) ZT HT HS F hF hFm a k 0 (v+s)
  have h1:=MixedNativeEndpointRootSums.endpoint_sum_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) ZT HT HS F hF hFm a k 1 (v+s)
  filter_upwards [he (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a),
    ae_all_iff.2 (fun j=>he (F j) (hF j) (hFm j)),h0,h1] with z hz hj h0 h1
  rw [hz]
  unfold MovingComparisonSection.endpointDifference
  rw [h1,h0,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _=>(hj j).symm)


include hIJ₀ hIJ₁ in
theorem section_integrable (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hH : (H:ℝ)≤1)
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
    (Bpast Babs : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) (j : ℕ) :
    Integrable (fun z : Ω×HeatCircle=>MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop (F j) (hF j) (hFm j) k ((v:ℝ),((s:ℝ),z))) (μ.prod haarAddCircle) := by
  obtain ⟨A,hA,hjet⟩:=(hF j).finite_jet_bound k
  have he:=MovingComparisonField.field_eq_endpoint_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop (F j) (hF j) (hFm j) J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A 1 hA (by norm_num) hjet
    Bpast Babs hBDGpast hBDGabs v s hvH hs hsh
  let ZT:=ObservationFamilyTimeShift.family (v:ℝ) Z
  let HT:=ControlledWordTimeShift.translatedTargets h Z htarget v
  let HS:=ControlledWordTimeShift.translatedStops h Z hstop v
  have h0:=MixedNativeEndpointRootSums.endpoint_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) ZT HT HS F hF hFm j k 0 (v+s)
  have h1:=MixedNativeEndpointRootSums.endpoint_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) ZT HT HS F hF hFm j k 1 (v+s)
  exact (h1.sub h0).congr (he.mono (fun _ hz=>hz.symm))

end SHE.MovingComparisonRootSums



