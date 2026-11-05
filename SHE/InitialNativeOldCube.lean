module
public import SHE.InitialNativeKernelFields
public import SHE.ControlledScalarReference
public import SHE.MixedPastNativeHaarSupport
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.PhysicalGapIntegration

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.InitialNativeOldCube
open Set MeasureTheory OrderedGapCoordinates

/-- The actual ordered support makes old-cube enlargement exact for Hilbert-valued rows. -/
theorem integral_eq {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
    {base q T horizon:ℝ}(hq:base≤q)(hT:T≤horizon)(k:ℕ)(F:(Fin k→ℝ)→E)
    (hz:∀t,¬ordered q T k t→F t=0):
    (∫t,F t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc base T)))=
      ∫t,F t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc base horizon)):=by
  classical
  have he(U:ℝ)(hTU:T≤U):
      (∫t,F t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc base U)))=
        ∫t,if ordered q T k t then F t else 0:=by
    let box:=Set.univ.pi (fun _:Fin k=>Ioc base U)
    have hb:MeasurableSet box:=MeasurableSet.univ_pi (fun _=>measurableSet_Ioc)
    have hm:Measure.pi (fun _:Fin k=>volume.restrict (Ioc base U))=
        (volume:Measure (Fin k→ℝ)).restrict box:=
      (Measure.restrict_pi_pi (μ:=fun _:Fin k=>(volume:Measure ℝ)) (fun _=>Ioc base U)).symm
    rw [hm,←integral_indicator hb]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ho:ordered q T k t
    · have ht:=PhysicalOrderedGaps.ordered_mem_timeBox hq hTU k t ho
      simp only [box,indicator_apply,if_pos ht,if_pos ho]
    · simp only [indicator_apply,if_neg ho,hz t ho,ite_self]
  exact (he T le_rfl).trans (he horizon hT).symm

open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance movingNativeKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeKernelFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "ZZ" T:max=>ControlledScalarReference.observations (⟨T,T.2.1⟩:ℝ≥0)
local notation "Zero" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,(0,0))
local notation "Add" T:max=>MixedPastNativeOldTimeEnergy.additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "BaseCols" T:max=>MixedPastNativeOldTimeEnergy.base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Signed" T:max=>MixedPastSignedEndpointFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

private theorem not_active (T:Icc (0:ℝ) (h:ℝ))(k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)
    (hn:¬ordered (q:ℝ) (T:ℝ) k t):¬QuarterSpatialEvent.active (Zero T) T k q t:=by
  intro ha
  apply hn
  apply (PhysicalOrderedGaps.strict_active_iff_ordered (Zero T) (T:ℝ) (fun _=>rfl)
    (q:ℝ) q.2 k t (0:HeatCircle) (fun _=>0)).mp
  refine ⟨ha.1,?_⟩
  simpa only [ActualMeanKernel.terminal_separated (Zero T) (T:ℝ) (fun _=>rfl)] using ha.2

theorem additive_integral (T:Icc (0:ℝ) (h:ℝ))(k:ℕ)(q:ℝ≥0)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (∫t,(Add T) k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (T:ℝ))))=
      ∫t,(Add T) k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ))):=by
  apply integral_eq q.2 T.2.2 k
  intro t hn
  exact MixedPastNativeHaarSupport.columns_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
    k q t bot_le (not_active (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (F:=F) (hF:=hF) (hFm:=hFm) T k q t hn)
    hmass hρ hκ _ ω

theorem base_integral (T:Icc (0:ℝ) (h:ℝ))(k:ℕ)(q:ℝ≥0)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (∫t,(BaseCols T) k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (T:ℝ))))=
      ∫t,(BaseCols T) k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ))):=by
  apply integral_eq q.2 T.2.2 k
  intro t hn
  exact MixedPastNativeHaarSupport.columns_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
    k q t bot_le (not_active (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (F:=F) (hF:=hF) (hFm:=hFm) T k q t hn)
    hmass hρ hell _ ω

theorem signed_integral (T:Icc (0:ℝ) (h:ℝ))(k:ℕ)(q:ℝ≥0)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (∫t,(Signed T) k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (T:ℝ))))=
      ∫t,(Signed T) k q hmass hρ (t,ω) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ))):=by
  apply integral_eq q.2 T.2.2 k
  intro t hn
  exact MixedPastSignedEndpointFields.raw_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
    k q t bot_le (not_active (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (F:=F) (hF:=hF) (hFm:=hFm) T k q t hn)
    hmass hρ ω

end SHE.InitialNativeOldCube
