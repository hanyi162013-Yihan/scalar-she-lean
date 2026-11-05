module
public import SHE.MixedPastNativeHaarSupport
public import SHE.MixedPastNativeQuarterRMS
public import SHE.NativeHigherOldTimeEnergy
public import SHE.MixedPastNativeTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false

namespace SHE.MixedPastNativeOldTimeEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeOldTimeEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeOldTimeEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeOldTimeEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeOldTimeEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeOldTimeEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeOldTimeEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativeOldTimeEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeOldTimeEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeOldTimeEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total

local instance mixedPastNativeOldTimeEnergy_spaceSigma : MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedPastNativeOldTimeEnergy_spaceBorel : BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
local instance mixedPastNativeOldTimeEnergy_nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

local notation "Columns"=>MixedPastNativeHaarFields.columns
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def additive (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    ((Fin k→ℝ)×Ω)→NativeKernelHaarColumns.Space:=
  Columns k q hmass hρ hκ (fun _=>AdditiveHaarForcing.constantField κ hκ)

def base (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    ((Fin k→ℝ)×Ω)→NativeKernelHaarColumns.Space:=
  Columns k q hmass hρ hell (fun z=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,z.2))

local notation "Add"=>additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "BaseCols"=>base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

theorem additive_measurable (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (Add k q hmass hρ):=
  MixedPastNativeHaarFields.columns_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k q hmass hρ hκ _ measurable_const

theorem base_measurable (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (BaseCols k q hmass hρ):=by
  have hc:Measurable (fun z:(Fin k→ℝ)×Ω=>
      ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,z.2)):=
    (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_snd)
  exact MixedPastNativeHaarFields.columns_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k q hmass hρ hell _ hc

/-- Actual old-time averaged additive columns are jointly Borel in
the original current clock and sample. -/
theorem additive_average_time_measurable (k:ℕ)(old:Measure (Fin k→ℝ))[SFinite old]
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (fun z:ℝ≥0×Ω=>∫t,Add k z.1 hmass hρ (t,z.2) ∂old):=by
  unfold additive
  exact MixedPastNativeTimeFields.average_columns_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k old hmass hρ hκ (fun _=>AdditiveHaarForcing.constantField κ hκ) measurable_const

/-- The genuine rough first-process coefficient is retained inside
the jointly Borel old-time averaged common-noise columns. -/
theorem base_average_time_measurable (k:ℕ)(old:Measure (Fin k→ℝ))[SFinite old]
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (fun z:ℝ≥0×Ω=>∫t,BaseCols k z.1 hmass hρ (t,z.2) ∂old):=by
  have hc:Measurable (fun z:(ℝ≥0×(Fin k→ℝ))×Ω=>
      ContinuousHeatMild.coefficientFunction haU hell hbU S.first (z.1.1,z.2)):=
    (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_fst.fst.prodMk measurable_snd)
  have hh:=MixedPastNativeTimeFields.average_columns_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k old hmass hρ hell _ hc
  unfold base
  exact hh

include hIJ₀ hIJ₁ in
/-- Genuine native additive/base-U countable columns are integrated
over original old times BEFORE squaring. All actual kernel, Gaussian,
Haar and conditional-moment applicability comes from the constructed pair. -/
theorem energy (k:ℕ)
    (hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hrootStop:∀x i,(Z.observations x i).stop=(b:ℝ))(hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (hspanF:(b:ℝ)-(v:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(b:ℝ)-(v:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hHistory:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (q:ℝ≥0)(hvq:v<q)(hqb:q<b)(hqH:q≤H)(hq1:(q:ℝ)≤1)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (mass ρ:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2):
    let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) P k Cf ρ
    let Ccur:=sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
    let Cpast:=sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) P k Bword)
    let Eq:=∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ
    let Ev:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
    let budget:=((b:ℝ)-(q:ℝ))^(ρ/2)*(Ccur*Eq^(χ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
        ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) ((2-χ)/4) A0 ν+
      Cpast*sqrt Ev*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*
      QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
        ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν)
    Integrable (Add k q hmass hρ.le) (old.prod μ) ∧
      Integrable (BaseCols k q hmass hρ.le) (old.prod μ) ∧
      Integrable (fun ω=>‖∫t,Add k q hmass hρ.le (t,ω) ∂old‖^2) μ ∧
      Integrable (fun ω=>‖∫t,BaseCols k q hmass hρ.le (t,ω) ∂old‖^2) μ ∧
      (∫ω,‖∫t,Add k q hmass hρ.le (t,ω) ∂old‖^2 ∂μ)+
        (∫ω,‖∫t,BaseCols k q hmass hρ.le (t,ω) ∂old‖^2 ∂μ)≤2*budget^2:=by
  intro old Cf Cdim C Ccur Cpast Eq Ev budget
  have hCf:0<Cf:=NativeUniversalConstants.rowConstant_pos (1+k)
  have hCdim:0<Cdim:=NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega)
  have hEq:0≤Eq:=integral_nonneg (fun _=>sq_nonneg _)
  have hEv:0≤Ev:=integral_nonneg (fun _=>sq_nonneg _)
  have he:=MixedPastNativeHaarEnergy.actual_energy_fixed
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k
    hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC hHistory
    q hvq hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder mass ρ hmass hρ hρhalf
  let env:=fun t=>(((b:ℝ)-(q:ℝ))^(ρ/2)*(Ccur*Eq^(χ/2)*
    PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower) (uniformConstant 1) k q ((2-χ)/4) A0 ν (QuarterSpatialEvent.anchor k t)+
    Cpast*sqrt Ev*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*
    PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower) (uniformConstant 1) k q (1/2:ℝ) A0 ν (QuarterSpatialEvent.anchor k t)))^2
  have hsec:∀ᵐt∂old,QuarterSpatialEvent.active Zero (b:ℝ) k q t→
      Integrable (fun ω=>‖Add k q hmass hρ.le (t,ω)‖^2) μ ∧
      Integrable (fun ω=>‖BaseCols k q hmass hρ.le (t,ω)‖^2) μ ∧
      (∫ω,‖Add k q hmass hρ.le (t,ω)‖^2 ∂μ)≤env t ∧
      (∫ω,‖BaseCols k q hmass hρ.le (t,ω)‖^2 ∂μ)≤env t:=by
    filter_upwards [he] with t ht
    intro ha
    let a:=QuarterSpatialEvent.anchor k t
    let δ:=(carrier Zero k).terminal a-(q:ℝ)
    let r:=(q:ℝ)+δ/4
    have hterm:=ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    have hδ:0<δ:=by dsimp only [δ,a,QuarterSpatialEvent.anchor];rw [hterm];exact sub_pos.mpr ha.2
    have hh:=ht ha r (by dsimp only [r];linarith) (by dsimp only [r,δ];linarith)
    have hc:=MixedPastNativeQuarterRMS.cap
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k q t A0 ν ρ Cf Cdim χ p Bcur Bword hCf.le hCdim.le hρ.le hρhalf hA0 hν hvq
      (by exact_mod_cast hqb) hq1 ha
    have hid0(ω:Ω):‖Add k q hmass hρ.le (t,ω)‖^2=∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (NativeRandomKernel.integralOperator (Spatial k q q t) ω
          (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)))‖^2:=
      MixedPastNativeHaarFields.columns_norm_sq
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ.le hκ _ _
    have hid1(ω:Ω):‖BaseCols k q hmass hρ.le (t,ω)‖^2=∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (NativeRandomKernel.integralOperator (Spatial k q q t) ω
          (CircleNormalization.push (globalHaarColumn j (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)).1)))‖^2:=
      MixedPastNativeHaarFields.columns_norm_sq
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ.le hell _ _
    have hsum:(∫ω,‖Add k q hmass hρ.le (t,ω)‖^2 ∂μ)+
        (∫ω,‖BaseCols k q hmass hρ.le (t,ω)‖^2 ∂μ)≤env t:=by
      simp only [hid0,hid1]
      exact hh.2.2.trans hc
    refine ⟨by simpa only [hid0] using hh.1,by simpa only [hid1] using hh.2.1,?_,?_⟩
    · exact (le_add_of_nonneg_right (integral_nonneg (fun _=>sq_nonneg _))).trans hsum
    · exact (le_add_of_nonneg_left (integral_nonneg (fun _=>sq_nonneg _))).trans hsum
  have hz0(t)(ha:¬QuarterSpatialEvent.active Zero (b:ℝ) k q t)(ω:Ω):Add k q hmass hρ.le (t,ω)=0:=
    MixedPastNativeHaarSupport.columns_zero
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q t hvq.le ha hmass hρ.le hκ _ ω
  have hz1(t)(ha:¬QuarterSpatialEvent.active Zero (b:ℝ) k q t)(ω:Ω):BaseCols k q hmass hρ.le (t,ω)=0:=
    MixedPastNativeHaarSupport.columns_zero
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q t hvq.le ha hmass hρ.le hell _ ω
  have H0:=NativeHigherOldTimeEnergy.energy Zero μ P (b:ℝ) (fun _=>rfl)
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k
    (by exact_mod_cast hvq.le) (by exact_mod_cast hqb) (by rfl) hA0 hν hρ.le hχ hχ1
    (sqrt_nonneg _) (sqrt_nonneg _) hEq hEv (Add k q hmass hρ.le)
    (additive_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ.le)
    (hsec.mono (fun _ h ha=>⟨(h ha).1,(h ha).2.2.1⟩)) hz0
  have H1:=NativeHigherOldTimeEnergy.energy Zero μ P (b:ℝ) (fun _=>rfl)
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k
    (by exact_mod_cast hvq.le) (by exact_mod_cast hqb) (by rfl) hA0 hν hρ.le hχ hχ1
    (sqrt_nonneg _) (sqrt_nonneg _) hEq hEv (BaseCols k q hmass hρ.le)
    (base_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ.le)
    (hsec.mono (fun _ h ha=>⟨(h ha).2.1,(h ha).2.2.2⟩)) hz1
  have he0:(∫ω,‖∫t,Add k q hmass hρ.le (t,ω) ∂old‖^2 ∂μ)≤budget^2:=H0.2.2
  have he1:(∫ω,‖∫t,BaseCols k q hmass hρ.le (t,ω) ∂old‖^2 ∂μ)≤budget^2:=H1.2.2
  exact ⟨H0.1,H1.1,H0.2.1,H1.2.1,by nlinarith only [he0,he1]⟩

end SHE.MixedPastNativeOldTimeEnergy

