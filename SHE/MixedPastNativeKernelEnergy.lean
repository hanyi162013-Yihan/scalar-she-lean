module

public import SHE.MixedPastNativeKernelTrace
public import SHE.MixedPastNativeMeanFTCClip
public import SHE.NativeCurrentCoordinates
public import SHE.NativeCurrentOutputRMS
public import SHE.NativeReserveTranslatedEnvelope
public import SHE.MixedPastNativeKernelAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.NativeParentOutputEnergyAE
public import SHE.ControlledThetaNativePointFields
public import SHE.MixedPastLiteralFields
public import SHE.ControlledFamilyKernelBounds
public import SHE.NativeKernelParameterAverage
public import SHE.ControlledFamilyNativePacketFTC
public import SHE.MixedPastNativeLegIdentity
public import SHE.MixedPastNativeMeanClip
public import SHE.MixedPastNativeMeanCap
public import SHE.NativeCarrierGeometry
public import SHE.ControlledRelativeScoreForest
public import SHE.ControlledThetaNativeGradient
public import SHE.MixedPastNativeConsistentPoint
public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanFTCClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanFTCClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanFTCClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanFTCClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastNativeMeanFTCClip_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeMeanFTCClip_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeMeanFTCClip_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- Literal additive covariance/baseline residual of the ORIGINAL
complete endpoint kernel. It is never realized as a bounded kernel. -/
def residual (k:ℕ)(q:ℝ≥0)(h:History HeatCircle k)(E:WordRecursion.State (1+k))(ω:Ω):ℝ:=
  ∫θ in (0:ℝ)..1,
    ControlledFamilyNativeLegs.covarianceLeg P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E θ+
    ControlledFamilyNativeLegs.baselineLeg P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E θ

local notation "Residual"=>residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

private theorem clipped_rms (f g a:Ω→ℝ)(hf:MemLp f 2 μ)(hg:MemLp g 2 μ)(ha:MemLp a 2 μ)
    (C:ℝ)(hC:0≤C)(hbound:∀ᵐω∂μ,|f ω|≤C*|g ω|+|a ω|):
    ProfileL2.normTwo μ f≤C*ProfileL2.normTwo μ g+ProfileL2.normTwo μ a:=by
  have hm:=ProfileL2.normTwo_mono hf ((hg.norm.const_mul C).add ha.norm)
    (hbound.mono (fun ω hω=>by
      simpa only [Real.norm_eq_abs,Pi.add_apply,abs_of_nonneg
        (add_nonneg (mul_nonneg hC (abs_nonneg (g ω))) (abs_nonneg (a ω)))] using hω))
  have hs:=ProfileL2.normTwo_add (hg.norm.const_mul C) ha.norm
  rw [ProfileL2.normTwo_const_mul hg.norm C,abs_of_nonneg hC] at hs
  have hgn:ProfileL2.normTwo μ (fun ω=>‖g ω‖)=ProfileL2.normTwo μ g:=by
    simp only [ProfileL2.normTwo,Real.norm_eq_abs,sq_abs]
  have han:ProfileL2.normTwo μ (fun ω=>‖a ω‖)=ProfileL2.normTwo μ a:=by
    simp only [ProfileL2.normTwo,Real.norm_eq_abs,sq_abs]
  rw [hgn,han] at hs
  exact hm.trans hs

/-- The actual correlated current factor in the relative original frame. -/
def current (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(p:ℕ)(χ:ℝ)
    (z:Ω×HeatCircle):ℝ:=
  let h:=QuarterSpatialEvent.anchor k t
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let a:=fun i=>NativeHeatSpan.unitCenter (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
  (MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P v q target a (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
    (z.1,NativeHeatSpan.unitCenter z.2))^χ*
  MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (r:=k)
    P v q target target a (leafIndex k (fun i=>i)) p (z.1,NativeHeatSpan.unitCenter z.2)

local notation "Current"=>current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The native score energy of the ORIGINAL physical row, retaining
the original law-q and its independent physical row-r. -/
def rowVariance (k:ℕ)(q r:ℝ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(yx:HeatCircle×HeatCircle):ℝ:=
  let h:=separated k (yx.2,t,fun i=>w i+yx.2)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  scoreVariance (NativeFirstScoreReserve.covariance P target target (centers Zero k h) (q-(v:ℝ)))
    (heatRow ((carrier Zero k).observations.observations h) r yx.1)

local notation "RowVariance"=>rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm

/-- The true covariance-plus-baseline FTC residual in the physical row. -/
def rowResidual (k:ℕ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)
    (yx:HeatCircle×HeatCircle)(ω:Ω):ℝ:=
  let h:=separated k (yx.2,t,fun i=>w i+yx.2)
  Residual k q h (heatRow ((carrier Zero k).observations.observations h) r yx.1) ω

local notation "RowResidual"=>rowResidual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

attribute [local irreducible] current rowVariance rowResidual MixedPastNativeKernel.field
  MixedPastNativeKernel.difference MixedPastJointData.pastU MixedPastJointData.pastD

/-- The complete bounded endpoint kernel is the sole realized kernel.
The true correlated current RMS and the literal additive FTC residual
are combined before the native negative-output trace. The residual
contract is local; it is furnished by the actual covariance/baseline
theta estimates, with their full original leaf ages. -/
theorem energy_of_actual_rms
    (k:ℕ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(p:ℕ)(χ:ℝ)
    (K T c:ℝ)(hK:0≤K)(hT:0≤T)(hc:0≤c)
    (aCur aA:HeatCircle→ℝ)(hCm:Measurable aCur)(hAm:Measurable aA)
    (hC0:∀x,0≤aCur x)(hA0:∀x,0≤aA x)
    (hCi:Integrable (fun x=>aCur x^2) haarAddCircle)
    (hAi:Integrable (fun x=>aA x^2) haarAddCircle)
    (EC EA:ℝ)(hEC:(∫x,aCur x^2 ∂haarAddCircle)≤EC)
    (hEA:(∫x,aA x^2 ∂haarAddCircle)≤EA)
    (hcurrent:∀ᵐx:HeatCircle∂haarAddCircle,
      MemLp (fun ω=>Current k q t w p χ (ω,x)) 2 μ ∧
      ProfileL2.normTwo μ (fun ω=>Current k q t w p χ (ω,x))≤aCur x)
    (hresidual:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      MemLp (RowResidual k q r t w yx) 2 μ ∧
      ProfileL2.normTwo μ (RowResidual k q r t w yx)≤
        K*Real.sqrt (RowVariance k q r t w yx)*aA yx.2)
    (hclip:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,∀ω:Ω,
      |(Field k q r t w (ω,yx)).re|≤
        (2*(K*Real.sqrt (RowVariance k q r t w yx)*T))*
          |Current k q t w p χ (ω,yx.2)|+|RowResidual k q r t w yx ω|)
    (hage:∀i,0<(Frame k t w i).target-(r-(v:ℝ)))
    {width:ℝ}(hw:0<width)(hw1:width≤1)
    (hmax:∀i,(Frame k t w i).target-(r-(v:ℝ))≤width)
    (hrow:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      Real.sqrt (RowVariance k q r t w yx)≤c*∑i,
        ((Frame k t w i).target-(r-(v:ℝ)))^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*((Frame k t w i).target-(r-(v:ℝ))))
            (by have := hage i;positivity) yx.1 (yx.2+(Frame k t w i).center)‖)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Field k q r t w) ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Field k q r t w) ω‖^2 ∂μ)≤
        ((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
          (NativeHeatSpan.clock width)^ρ*((c*K)^2*(8*T^2*EC+2*EA)):=by
  let aout:HeatCircle→ℝ:=fun x=>(c*K)*(2*T*aCur x+aA x)
  have hao:Measurable aout:=measurable_const.mul
    ((measurable_const.mul hCm).add hAm)
  have ha0(x:HeatCircle):0≤aout x:=mul_nonneg (mul_nonneg hc hK)
    (add_nonneg (mul_nonneg (by positivity) (hC0 x)) (hA0 x))
  have hC2:MemLp aCur 2 haarAddCircle:=
    (memLp_two_iff_integrable_sq hCm.aestronglyMeasurable).mpr hCi
  have hA2:MemLp aA 2 haarAddCircle:=
    (memLp_two_iff_integrable_sq hAm.aestronglyMeasurable).mpr hAi
  have ha2:MemLp aout 2 haarAddCircle:=((hC2.const_mul (2*T)).add hA2).const_mul (c*K)
  have hbound(x:HeatCircle):aout x^2≤(c*K)^2*(8*T^2*aCur x^2+2*aA x^2):=by
    dsimp only [aout]
    have hs:0≤(2*T*aCur x-aA x)^2:=sq_nonneg _
    nlinarith [mul_nonneg (sq_nonneg (c*K)) hs]
  have haE:(∫x,aout x^2 ∂haarAddCircle)≤(c*K)^2*(8*T^2*EC+2*EA):=by
    calc
      _≤∫x,(c*K)^2*(8*T^2*aCur x^2+2*aA x^2) ∂haarAddCircle:=by
        have hRi:Integrable (fun x:HeatCircle=>(c*K)^2*(8*T^2*aCur x^2+2*aA x^2)) haarAddCircle:=by
          convert! (((hCi.const_mul (8*T^2)).add (hAi.const_mul 2)).const_mul ((c*K)^2)) using 1
        exact integral_mono ha2.integrable_sq hRi hbound
      _=(c*K)^2*(8*T^2*(∫x,aCur x^2 ∂haarAddCircle)+2*(∫x,aA x^2 ∂haarAddCircle)):=by
        rw [integral_const_mul,integral_add (hCi.const_mul _) (hAi.const_mul _),
          integral_const_mul,integral_const_mul]
      _≤_:=mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hEC (by positivity)) (mul_le_mul_of_nonneg_left hEA (by norm_num)))
          (sq_nonneg _)
  have hFm0:=MixedPastNativeKernel.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t w
  obtain ⟨B,hB,hFb⟩:=MixedPastNativeKernel.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t
  have hsample:∀yx:HeatCircle×HeatCircle,MemLp (fun ω=>(Field k q r t w (ω,yx)).re) 2 μ:=by
    intro yx
    apply MemLp.of_bound ((Complex.measurable_re.comp hFm0).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
    filter_upwards with ω
    exact (Complex.abs_re_le_norm _).trans (hFb w ω yx.1 yx.2)
  have hcurJoint:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      MemLp (fun ω=>Current k q t w p χ (ω,yx.2)) 2 μ ∧
      ProfileL2.normTwo μ (fun ω=>Current k q t w p χ (ω,yx.2))≤aCur yx.2:=
    (Measure.quasiMeasurePreserving_snd (μ:=haarAddCircle) (ν:=haarAddCircle)).ae hcurrent
  have hsharp:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      ProfileL2.normTwo μ (fun ω=>‖Field k q r t w (ω,yx)‖)≤aout yx.2*∑i,
        ((Frame k t w i).target-(r-(v:ℝ)))^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*((Frame k t w i).target-(r-(v:ℝ))))
            (by have := hage i;positivity) yx.1 (yx.2+(Frame k t w i).center)‖:=by
    filter_upwards [hcurJoint,hresidual,hclip,hrow] with yx hyC hyA hyclip hyrow
    have hcoef:0≤2*(K*Real.sqrt (RowVariance k q r t w yx)*T):=by positivity
    have hn:=clipped_rms μ (fun ω=>(Field k q r t w (ω,yx)).re)
      (fun ω=>Current k q t w p χ (ω,yx.2)) (RowResidual k q r t w yx)
      (hsample yx) hyC.1 hyA.1 _ hcoef (ae_of_all _ hyclip)
    have hR:ProfileL2.normTwo μ (fun ω=>(Field k q r t w (ω,yx)).re)≤
        K*Real.sqrt (RowVariance k q r t w yx)*(2*T*aCur yx.2+aA yx.2):=by
      calc
        _≤(2*(K*Real.sqrt (RowVariance k q r t w yx)*T))*aCur yx.2+
          K*Real.sqrt (RowVariance k q r t w yx)*aA yx.2:=
          hn.trans (add_le_add (mul_le_mul_of_nonneg_left hyC.2 hcoef) hyA.2)
        _=_:=by ring
    have hR':ProfileL2.normTwo μ (fun ω=>(Field k q r t w (ω,yx)).re)≤
        aout yx.2*∑i,((Frame k t w i).target-(r-(v:ℝ)))^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*((Frame k t w i).target-(r-(v:ℝ))))
            (by have := hage i;positivity) yx.1 (yx.2+(Frame k t w i).center)‖:=by
      calc
        _≤(K*(2*T*aCur yx.2+aA yx.2))*Real.sqrt (RowVariance k q r t w yx):=by nlinarith only [hR]
        _≤_:=by
          have hfac:0≤K*(2*T*aCur yx.2+aA yx.2):=
            mul_nonneg hK (add_nonneg (mul_nonneg (by positivity : 0≤2*T) (hC0 yx.2)) (hA0 yx.2))
          have hh:=mul_le_mul_of_nonneg_left hyrow hfac
          dsimp only [aout]
          convert! hh using 1 <;> ring
    have he:(fun ω=>‖Field k q r t w (ω,yx)‖)=(fun ω=>|(Field k q r t w (ω,yx)).re|):=by
      funext ω
      simp only [MixedPastNativeKernel.field,Complex.norm_real,Complex.ofReal_re,Real.norm_eq_abs]
    rw [he,ProfileL2.normTwo_abs]
    exact hR'
  exact NativeParentOutputEnergyAE.energy μ hFm0 hB (hFb w) aout hao ha0 ha2.integrable_sq haE
    (1+k) (by omega) (fun i=>(Frame k t w i).target-(r-(v:ℝ)))
    (fun i=>(Frame k t w i).center) hage hw hw1 hmax hmass hρ hρhalf hsharp


end SHE.MixedPastNativeKernelEnergy
