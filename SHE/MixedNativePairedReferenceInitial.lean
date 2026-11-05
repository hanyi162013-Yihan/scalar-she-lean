module

public import SHE.MixedNativePairedReferenceEnergy
public import SHE.InitialNativeColumnEnergy
public import SHE.PastReferenceEnergy
public import SHE.MixedNativePairedReferenceHilbert
public import SHE.PastReferenceComparisonSection
public import SHE.PastReferenceMeanTheta
public import SHE.PastReferenceThreeLeg
public import SHE.PastReferenceMeanRealization
public import SHE.PastReferenceCovarianceSection
public import SHE.PastReferenceBaselineSection
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

namespace SHE.MixedNativePairedReferenceInitial
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonSection_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonSection_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonSection_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonSection_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonSection_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonSection_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonSection_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonSection_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonSection_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonSection_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

def endpointDifference (k : ℕ) (v s : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 1 (v+s) z-
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 0 (v+s) z

local notation "End"=>endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x i,(Z.observations x i).stop≤(h:ℝ))
variable (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
local notation "RS" v=>(fun x=>by
  change (Z.observations x 0).stop+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [le_antisymm (hrootStop x 0) (hstop x 0),NNReal.coe_add,add_comm] <;> simp only [NNReal.coe_zero])
local notation "RT" v=>(fun x=>by
  change (Z.observations x 0).target+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [hrootTarget x 0,NNReal.coe_add,add_comm] <;> simp only [NNReal.coe_zero])
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Ref"=>MixedNativePairedReferenceEnergy.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ
include haP htarget hnull hJ hAs hL in
/-- The actual past endpoint is included in the sharp three-leg energy
bound. Only the positive root span is used; there is no singular
current-increment estimate at zero. -/
theorem reference_zero (hA:P.coefficient=(fun z=>κ+aV z))(hlocal:StandardTerminalPastLocality J)
    (hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(k:ℕ)
    (hfresh:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ:ℝ)(hχpos:0<χ)(hχ1:χ<1)(p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (hρpos:0<ρ)(hρhalf:ρ<1/2)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)
    (hhH:h≤H)(hh:0<h):
    ∀ᵐω∂μ,Ref k (0,ω)=0:=by
  have he:=MixedNativePairedReferenceEnergy.actual_past_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ hA hlocal hH hsmallPoint hsmallL2
    hages hcenter hspan k hfresh hold A0 ν hA0 hν hjet χ hχpos.le hχ1 p hp horder
    Bpast Babs B0 hBDGpast hBDGabs hBDG hρpos hρhalf ε hε hεhalf 0
    (by simpa only [zero_add] using hhH) hh
  have hE: (∫ω,‖S.second 0 ω-S.first 0 ω‖^2 ∂μ)=0:=
    InitialNativeColumnEnergy.initial_energy_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hz:(∫⁻ω,ENNReal.ofReal (‖Ref k (0,ω)‖^2) ∂μ)=0:=by
    have hle:(∫⁻ω,ENNReal.ofReal (‖Ref k (0,ω)‖^2) ∂μ)≤0:=by
      simpa only [hE,Real.zero_rpow (div_ne_zero hχpos.ne' (by norm_num:(2:ℝ)≠0)),
        mul_zero,zero_mul,zero_add,add_zero,zero_pow (by norm_num:(2:ℕ)≠0),ENNReal.ofReal_zero] using he
    exact nonpos_iff_eq_zero.mp hle
  have hjm:=MixedCanonicalRootHilbertExpansion.term_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1
    0 (0+h) (show (0:ℝ≥0)≤0+h from bot_le) (ZT 0) (HT 0) (HS 0) F hF hFm
    hsmallPoint hL hρ 1 k
  have hom:=MixedOrdinaryRootHilbertExpansion.term_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0
    0 (0+h) (show (0:ℝ≥0)≤0+h from bot_le) (ZT 0) (RS 0) (RT 0) F hF hFm
    hsmallPoint hL hρ 1 k
  have hm:Measurable (fun ω=>Ref k (0,ω)):=by
    convert! hjm.sub hom using 1 <;> rfl
  have he0:∀ᵐω∂μ,ENNReal.ofReal (‖Ref k (0,ω)‖^2)=0:=
    (lintegral_eq_zero_iff ((hm.norm.pow_const 2).ennreal_ofReal)).mp hz
  filter_upwards [he0] with ω hω
  have hh0:‖Ref k (0,ω)‖^2=0:=le_antisymm ((ENNReal.ofReal_eq_zero).mp hω) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh0)

end SHE.MixedNativePairedReferenceInitial
