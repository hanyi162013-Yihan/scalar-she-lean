module
public import SHE.MovingNativePredictableColumns
public import SHE.MovingNativeAverageTranslation
public import SHE.MixedNativeOriginalFourierRows
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativePredictableAverages
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  Set WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories HistoryProductMeasure AddCircle
open scoped NNReal ENNReal
local instance movingNativePredictableAverages_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingNativePredictableAverages_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance movingNativePredictableAverages_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativePredictableAverages_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance movingNativePredictableAverages_realSigma:MeasurableSpace RealL2:=borel _
local instance movingNativePredictableAverages_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance movingNativePredictableAverages_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance movingNativePredictableAverages_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
local instance movingNativePredictableAverages_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance movingNativePredictableAverages_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingNativePredictableAverages_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance movingNativePredictableAverages_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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
local notation "Add"=>MovingNativePredictableColumns.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Base"=>MovingNativePredictableColumns.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Signed"=>MovingNativePredictableColumns.signed
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldLeft"=>MovingNativeColumnAverages.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldRight"=>MovingNativeColumnAverages.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

def left(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:ℝ≥0×(ℝ≥0×Ω)):NativeKernelHaarColumns.Space:=
  ∫t:Fin k→ℝ,Add hΛ k hmass hρ (t,z) ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ)))
def right(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:ℝ≥0×(ℝ≥0×Ω)):NativeKernelHaarColumns.Space:=
  (∫t:Fin k→ℝ,Base hΛ k hmass hρ (t,z) ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ))))+
  (∫t:Fin k→ℝ,Signed k hmass hρ (t,z) ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ))))
local notation "Left"=>left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Right"=>right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "Source0" v:max=>MixedNativeOriginalFourierRows.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm
local notation "Source1" v:max=>MixedNativeOriginalFourierRows.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm

theorem left_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (ℝ≥0×(ℝ≥0×Ω)) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable) _ (Left hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hm:=(MovingNativePredictableColumns.additive_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ).comp measurable_swap
  exact hm.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable

theorem right_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (ℝ≥0×(ℝ≥0×Ω)) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable) _ (Right hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hb:=(MovingNativePredictableColumns.base_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ).comp measurable_swap
  have hs:=(MovingNativePredictableColumns.signed_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ).comp measurable_swap
  exact (hb.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable).add
    (hs.stronglyMeasurable.integral_prod_right'
      (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable)

theorem left_eq(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:ℝ≥0×(ℝ≥0×Ω)):
    Left hΛ k hmass hρ z=if z.1<z.2.1∧z.2.1<z.1+h then
      OldLeft hΛ k hmass hρ ((z.1,z.2.1-z.1),z.2.2) else 0:=by
  by_cases hz:z.1<z.2.1∧z.2.1<z.1+h
  · simp only [left,MovingNativePredictableColumns.additive,if_pos hz,MovingNativeColumnAverages.left]
  · simp only [left,MovingNativePredictableColumns.additive,if_neg hz,integral_zero]

theorem right_eq(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:ℝ≥0×(ℝ≥0×Ω)):
    Right hΛ k hmass hρ z=if z.1<z.2.1∧z.2.1<z.1+h then
      OldRight hΛ k hmass hρ ((z.1,z.2.1-z.1),z.2.2) else 0:=by
  by_cases hz:z.1<z.2.1∧z.2.1<z.1+h
  · simp only [right,MovingNativePredictableColumns.base,MovingNativePredictableColumns.signed,
      if_pos hz,MovingNativeColumnAverages.right]
  · simp only [right,MovingNativePredictableColumns.base,MovingNativePredictableColumns.signed,
      if_neg hz,integral_zero,add_zero]

/-- Exact pointwise identification with the guarded ORIGINAL-clock
complete columns, preserving every translated original old-time measure. -/
theorem original_left(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (v q:ℝ≥0)(ω:Ω):
    (Source0 v) k hmass hρ (q,ω)=Left hΛ k hmass hρ (v,(q,ω)):=by
  rw [MixedNativeOriginalFourierRows.left,left_eq]
  by_cases hz:v<q∧q<v+h
  · rw [if_pos hz,if_pos hz]
    have he:=MovingNativeAverageTranslation.left_translation
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      hΛ k v (q-v) ω hmass hρ
    rwa [add_tsub_cancel_of_le hz.1.le] at he
  · rw [if_neg hz,if_neg hz]

theorem original_right(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (v q:ℝ≥0)(ω:Ω):
    (Source1 v) k hmass hρ (q,ω)=Right hΛ k hmass hρ (v,(q,ω)):=by
  rw [MixedNativeOriginalFourierRows.right,right_eq]
  by_cases hz:v<q∧q<v+h
  · rw [if_pos hz,if_pos hz]
    have he:=MovingNativeAverageTranslation.right_translation
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      hΛ k v (q-v) ω hmass hρ
    rwa [add_tsub_cancel_of_le hz.1.le] at he
  · rw [if_neg hz,if_neg hz]

def row(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)
    (z:ℝ≥0×(ℝ≥0×Ω)):Both RealHaarInput:=
  WithLp.toLp 2
    (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Left hΛ k hmass hρ z),
     HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Right hΛ k hmass hρ z))

theorem row_original(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)
    (v q:ℝ≥0)(ω:Ω):
    row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      hΛ k hmass hρ a l (v,(q,ω))=WithLp.toLp 2
        (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) ((Source0 v) k hmass hρ (q,ω)),
         HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) ((Source1 v) k hmass hρ (q,ω))):=by
  rw [row,original_left,original_right]

/-- Both real and imaginary complete native Fourier inputs are genuinely
jointly predictable in the moving past and the ORIGINAL noise clock. -/
theorem row_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(a:ℂ→L[ℝ]ℝ)(l:ℤ):
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)]
      (row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
        hΛ k hmass hρ a l):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have h0:=(HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))).continuous.measurable.comp
    (left_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ)
  have h1:=(HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))).continuous.measurable.comp
    (right_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ)
  exact ((WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp
    (h0.prodMk h1)).stronglyMeasurable
end SHE.MovingNativePredictableAverages
