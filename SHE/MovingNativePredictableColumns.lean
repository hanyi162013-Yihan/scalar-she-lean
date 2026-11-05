module
public import SHE.MovingNativePredictableKernel
public import SHE.NativeKernelCongruence
public import SHE.NativeKernelFiber
public import SHE.MovingNativeColumnAverages
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MovingNativePredictableColumns
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  Set WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories HistoryProductMeasure AddCircle
open scoped NNReal ENNReal
local instance movingNativePredictableColumns_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingNativePredictableColumns_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingNativePredictableColumns_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance movingNativePredictableColumns_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativePredictableColumns_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance movingNativePredictableColumns_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingNativePredictableColumns_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingNativePredictableColumns_realSigma:MeasurableSpace RealL2:=borel _
local instance movingNativePredictableColumns_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance movingNativePredictableColumns_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance movingNativePredictableColumns_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
abbrev Param(k:ℕ):Type:=MovingNativePredictableKernel.Param (Ω:=Ω) k
local notation "Common"=>MovingNativePredictableKernel.common
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Endpoint"=>MovingNativePredictableKernel.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldCommon"=>MovingNativeColumns.common
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldEndpoint"=>MovingNativeColumns.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldAdd"=>MovingNativeColumns.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldBase"=>MovingNativeColumns.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldSigned"=>MovingNativeColumns.signed
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

def additive(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω) k):NativeKernelHaarColumns.Space:=
  if z.2.1<z.2.2.1∧z.2.2.1<z.2.1+h then
    OldAdd hΛ k hmass hρ ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)) else 0
def base(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω) k):NativeKernelHaarColumns.Space:=
  if z.2.1<z.2.2.1∧z.2.2.1<z.2.1+h then
    OldBase hΛ k hmass hρ ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)) else 0
def signed(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω) k):NativeKernelHaarColumns.Space:=
  if z.2.1<z.2.2.1∧z.2.2.1<z.2.1+h then
    OldSigned k hmass hρ ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)) else 0
local notation "Add"=>additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Base"=>base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Signed"=>signed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem additive_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param (Ω:=Ω) k) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)) _ (Add hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hk:=MovingNativePredictableKernel.common_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k
  have hb(z:Param (Ω:=Ω) k):∃B:ℝ,∀y x,‖Common k (z,(y,x))‖≤B:=by
    obtain ⟨B,_,hB⟩:=MovingNativePredictableKernel.common_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k z
    exact ⟨B,hB⟩
  apply HilbertColumns.measurable_of_columns
  intro j
  have hf:Measurable (fun _:Param (Ω:=Ω) k=>CircleNormalization.push
      (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)):=measurable_const
  have hm:=(OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
    (NativeRandomKernel.action_measurable hk hb _ hf)
  convert! hm using 1
  funext z
  by_cases hz:z.2.1<z.2.2.1∧z.2.2.1<z.2.1+h
  · have he:=NativeKernelCongruence.operator_congr (Common k) (OldCommon k) z
      ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)) (fun y x=>by
        rw [MovingNativePredictableKernel.common_eq,if_pos hz])
    simp only [additive,if_pos hz,MovingNativeColumns.additive,NativeKernelHaarColumns.columns_apply,
      NativeKernelHaarColumns.column,Function.comp_def,he]
  · have he:=NativeRandomKernel.integralOperator_eq_zero_of_fiber (Common k) z
      (fun y x=>by rw [MovingNativePredictableKernel.common_eq,if_neg hz])
    simp only [additive,if_neg hz,lp.coeFn_zero,Pi.zero_apply,Function.comp_def,he,ContinuousLinearMap.zero_apply,map_zero]

theorem base_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param (Ω:=Ω) k) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)) _ (Base hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hk:=MovingNativePredictableKernel.common_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k
  have hb(z:Param (Ω:=Ω) k):∃B:ℝ,∀y x,‖Common k (z,(y,x))‖≤B:=by
    obtain ⟨B,_,hB⟩:=MovingNativePredictableKernel.common_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k z
    exact ⟨B,hB⟩
  have hc:Measurable (fun z:Param (Ω:=Ω) k=>CU z.2.2):=S.first_coefficient.measurable.comp measurable_snd.snd
  apply HilbertColumns.measurable_of_columns
  intro j
  have hf:Measurable (fun z:Param (Ω:=Ω) k=>CircleNormalization.push (globalHaarColumn j (CU z.2.2).1)):=by
    simpa only [NativeHaarKernel.factor_basis] using NativeHaarKernel.factor_column_measurable ell M hell _ hc j
  have hm:=(OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
    (NativeRandomKernel.action_measurable hk hb _ hf)
  convert! hm using 1
  funext z
  by_cases hz:z.2.1<z.2.2.1∧z.2.2.1<z.2.1+h
  · have hsum:z.2.1+(z.2.2.1-z.2.1)=z.2.2.1:=add_tsub_cancel_of_le hz.1.le
    have he:=NativeKernelCongruence.operator_congr (Common k) (OldCommon k) z
      ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)) (fun y x=>by
        rw [MovingNativePredictableKernel.common_eq,if_pos hz])
    simp only [base,if_pos hz,MovingNativeColumns.base,NativeKernelHaarColumns.columns_apply,
      NativeKernelHaarColumns.column,MovingNativeColumns.coefficientU,Function.comp_def,hsum,he]
  · have he:=NativeRandomKernel.integralOperator_eq_zero_of_fiber (Common k) z
      (fun y x=>by rw [MovingNativePredictableKernel.common_eq,if_neg hz])
    simp only [base,if_neg hz,lp.coeFn_zero,Pi.zero_apply,Function.comp_def,he,ContinuousLinearMap.zero_apply,map_zero]

theorem signed_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param (Ω:=Ω) k) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)) _ (Signed k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hk:=MovingNativePredictableKernel.endpoint_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k
  have hb(z:Param (Ω:=Ω) k):∃B:ℝ,∀y x,‖Endpoint k (z,(y,x))‖≤B:=by
    obtain ⟨B,_,hB⟩:=MovingNativePredictableKernel.endpoint_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k z
    exact ⟨B,hB⟩
  have hc:Measurable (fun z:Param (Ω:=Ω) k=>CU z.2.2):=S.first_coefficient.measurable.comp measurable_snd.snd
  have hd:Measurable (fun z:Param (Ω:=Ω) k=>CV z.2.2):=S.second_coefficient.measurable.comp measurable_snd.snd
  apply HilbertColumns.measurable_of_columns
  intro j
  have hf:Measurable (fun z:Param (Ω:=Ω) k=>CircleNormalization.push
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
  by_cases hz:z.2.1<z.2.2.1∧z.2.2.1<z.2.1+h
  · have hsum:z.2.1+(z.2.2.1-z.2.1)=z.2.2.1:=add_tsub_cancel_of_le hz.1.le
    have he:=NativeKernelCongruence.operator_congr (Endpoint k) (OldEndpoint k) z
      ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)) (fun y x=>by
        rw [MovingNativePredictableKernel.endpoint_eq,if_pos hz])
    simp only [signed,if_pos hz,MovingNativeColumns.signed,SignedKernelColumns.rawColumns_apply,
      MovingNativeColumns.coefficientU,MovingNativeColumns.coefficientV,Function.comp_def,hsum,he]
  · have he:=NativeRandomKernel.integralOperator_eq_zero_of_fiber (Endpoint k) z
      (fun y x=>by rw [MovingNativePredictableKernel.endpoint_eq,if_neg hz])
    simp only [signed,if_neg hz,lp.coeFn_zero,Pi.zero_apply,Function.comp_def,he,ContinuousLinearMap.zero_apply,map_zero]
end SHE.MovingNativePredictableColumns
