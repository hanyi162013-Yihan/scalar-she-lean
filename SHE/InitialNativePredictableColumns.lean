module
public import SHE.InitialNativePredictableKernel
public import SHE.NativeKernelCongruence
public import SHE.NativeKernelFiber
public import SHE.InitialNativeColumnAverages
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.InitialNativePredictableColumns
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  Set WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories HistoryProductMeasure AddCircle
open scoped NNReal ENNReal
local instance initialNativePredictableColumns_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance initialNativePredictableColumns_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance initialNativePredictableColumns_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance initialNativePredictableColumns_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance initialNativePredictableColumns_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance initialNativePredictableColumns_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance initialNativePredictableColumns_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance initialNativePredictableColumns_realSigma:MeasurableSpace RealL2:=borel _
local instance initialNativePredictableColumns_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance initialNativePredictableColumns_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance initialNativePredictableColumns_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
abbrev Param(k:ℕ):Type:=InitialNativePredictableKernel.Param Λ u₀ P haP h (Ω:=Ω) k
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "Common"=>InitialNativePredictableKernel.common
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Endpoint"=>InitialNativePredictableKernel.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldCommon"=>InitialNativeColumns.common
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldEndpoint"=>InitialNativeColumns.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldAdd"=>InitialNativeColumns.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldBase"=>InitialNativeColumns.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldSigned"=>InitialNativeColumns.signed
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

def additive(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):NativeKernelHaarColumns.Space:=
  OldAdd hΛ k hmass hρ ((z.2.1,z.2.2.1),(z.1,z.2.2.2))
def base(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):NativeKernelHaarColumns.Space:=
  OldBase hΛ k hmass hρ ((z.2.1,z.2.2.1),(z.1,z.2.2.2))
def signed(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):NativeKernelHaarColumns.Space:=
  OldSigned k hmass hρ ((z.2.1,z.2.2.1),(z.1,z.2.2.2))
local notation "Add"=>additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Base"=>base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Signed"=>signed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem additive_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω) k) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace (Icc (R).base (R).horizon)).prod 𝓕.predictable)) _ (Add hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hk:=InitialNativePredictableKernel.common_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k
  have hb(z:Param Λ u₀ P haP h (Ω:=Ω) k):∃B:ℝ,∀y x,‖Common k (z,(y,x))‖≤B:=by
    obtain ⟨B,_,hB⟩:=InitialNativePredictableKernel.common_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k z
    exact ⟨B,hB⟩
  apply HilbertColumns.measurable_of_columns
  intro j
  have hf:Measurable (fun _:Param Λ u₀ P haP h (Ω:=Ω) k=>CircleNormalization.push
      (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)):=measurable_const
  have hm:=(OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
    (NativeRandomKernel.action_measurable hk hb _ hf)
  convert! hm using 1

theorem base_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω) k) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace (Icc (R).base (R).horizon)).prod 𝓕.predictable)) _ (Base hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hk:=InitialNativePredictableKernel.common_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k
  have hb(z:Param Λ u₀ P haP h (Ω:=Ω) k):∃B:ℝ,∀y x,‖Common k (z,(y,x))‖≤B:=by
    obtain ⟨B,_,hB⟩:=InitialNativePredictableKernel.common_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k z
    exact ⟨B,hB⟩
  have hc:Measurable (fun z:Param Λ u₀ P haP h (Ω:=Ω) k=>CU z.2.2):=S.first_coefficient.measurable.comp measurable_snd.snd
  apply HilbertColumns.measurable_of_columns
  intro j
  have hf:Measurable (fun z:Param Λ u₀ P haP h (Ω:=Ω) k=>CircleNormalization.push (globalHaarColumn j (CU z.2.2).1)):=by
    simpa only [NativeHaarKernel.factor_basis] using NativeHaarKernel.factor_column_measurable ell M hell _ hc j
  have hm:=(OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
    (NativeRandomKernel.action_measurable hk hb _ hf)
  convert! hm using 1

theorem signed_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω) k) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace (Icc (R).base (R).horizon)).prod 𝓕.predictable)) _ (Signed k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hk:=InitialNativePredictableKernel.endpoint_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k
  have hb(z:Param Λ u₀ P haP h (Ω:=Ω) k):∃B:ℝ,∀y x,‖Endpoint k (z,(y,x))‖≤B:=by
    obtain ⟨B,_,hB⟩:=InitialNativePredictableKernel.endpoint_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k z
    exact ⟨B,hB⟩
  have hc:Measurable (fun z:Param Λ u₀ P haP h (Ω:=Ω) k=>CU z.2.2):=S.first_coefficient.measurable.comp measurable_snd.snd
  have hd:Measurable (fun z:Param Λ u₀ P haP h (Ω:=Ω) k=>CV z.2.2):=S.second_coefficient.measurable.comp measurable_snd.snd
  apply HilbertColumns.measurable_of_columns
  intro j
  have hf:Measurable (fun z:Param Λ u₀ P haP h (Ω:=Ω) k=>CircleNormalization.push
      (globalHaarColumn j (CV z.2.2).1-globalHaarColumn j (CU z.2.2).1)):=by
    have hh:=(NativeHaarKernel.factor_column_measurable ell M hell _ hd j).sub
      (NativeHaarKernel.factor_column_measurable ell M hell _ hc j)
    convert! hh using 1
    funext z
    simp only [map_sub,NativeHaarKernel.factor_basis,Pi.sub_apply]
  have hm:=(OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
    (NativeRandomKernel.action_measurable hk hb _ hf)
  convert! hm using 1
  funext z
  have he:=NativeKernelCongruence.operator_congr (Endpoint k) (OldEndpoint k) z
    ((z.2.1,z.2.2.1),(z.1,z.2.2.2)) (fun y x=>rfl)
  simp only [signed,InitialNativeColumns.signed,SignedKernelColumns.rawColumns_apply,
    InitialNativeColumns.coefficientU,InitialNativeColumns.coefficientV,Function.comp_def,he]

end SHE.InitialNativePredictableColumns
