module

public import SHE.MixedNativePastHybridIdentity
public import SHE.MixedNativePastThetaCentering
public import SHE.HeatPhysicalSubsequence
public import SHE.ObservationTargetContinuity
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

namespace SHE.MixedNativeEndpointLimit
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeEndpointLimit_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeEndpointLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeEndpointLimit_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeEndpointLimit_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeEndpointLimit_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeEndpointLimit_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open Filter Topology Set AddCircle
local instance mixedNativeEndpointLimit_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- The actual zero-heat-age physical field, centered at the random-past
native controlled profile. Both original current fields use the checked
joint spatial representative. -/
def offset (θ : ℝ) (v q : ℝ≥0) (x : HeatCircle) (ω : Ω) : ℝ :=
  PredictableScalarField.wordField (Function.uncurry S.first) ω ((q:ℝ),x)+
    θ*(PredictableScalarField.wordField (Function.uncurry S.second) ω ((q:ℝ),x)-
      PredictableScalarField.wordField (Function.uncurry S.first) ω ((q:ℝ),x))-
    ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω))
      (θ,((q:ℝ)-(v:ℝ),x))

/-- One spatial exceptional set supports the heat-to-field limit and is
independent of every subsequently chosen past event. In particular this
is an actual endpoint bridge, rather than a positive-age convention. -/
theorem exists_offset_subsequence (θ : ℝ) (v q : ℝ≥0) (hvq : v<q) :
    ∃ ε : ℕ → ℝ,(∀ n,0<ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ᵐ ω ∂μ,
        Tendsto (fun n =>
          MixedNativePastThetaCentering.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            θ ((q:ℝ)+ε n) q ((q:ℝ)+ε n) x ω-
          ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω))
            (θ,((q:ℝ)+ε n-(v:ℝ),x)))
          atTop (𝓝 (offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q x ω)) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_id))
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_id))
  obtain ⟨ε,hε,hε0,hboth⟩ := HeatPhysicalSubsequence.exists_common_subsequence
    (S.first q) (S.second q) hU hV μ
  have hs := (Measure.measurePreserving_swap (μ:=haarAddCircle (T:=2*Real.pi)) (ν:=μ)).quasiMeasurePreserving.ae hboth
  refine ⟨ε,hε,hε0,?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with x hx
  filter_upwards [hx] with ω hω
  have hUlim : Tendsto (fun n => functional (ε n) x (S.first q ω)) atTop
      (𝓝 (PredictableScalarField.wordField (Function.uncurry S.first) ω ((q:ℝ),x))) := by
    simpa only [functional_physical (hε _),PredictableScalarField.wordField,Real.toNNReal_coe,PredictableScalarField.nativeField,
      PredictableScalarField.unitField,Function.uncurry,Prod.swap,Prod.fst,Prod.snd] using hω.1
  have hVlim : Tendsto (fun n => functional (ε n) x (S.second q ω)) atTop
      (𝓝 (PredictableScalarField.wordField (Function.uncurry S.second) ω ((q:ℝ),x))) := by
    simpa only [functional_physical (hε _),PredictableScalarField.wordField,Real.toNNReal_coe,PredictableScalarField.nativeField,
      PredictableScalarField.unitField,Function.uncurry,Prod.swap,Prod.fst,Prod.snd] using hω.2
  have hDlim := hVlim.sub hUlim
  have hexp : Tendsto (fun n => Real.exp (-Λ*ε n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [mul_zero,Real.exp_zero,Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_const_nhds (x:= -Λ)).mul hε0)
  have hage : 0<(q:ℝ)-(v:ℝ) := sub_pos.mpr (by exact_mod_cast hvq)
  have harg : Tendsto (fun n => (q:ℝ)+ε n-(v:ℝ)) atTop (𝓝 ((q:ℝ)-(v:ℝ))) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x:=(q:ℝ))).add hε0).sub_const (v:ℝ)
  have hbaseU := (ObservationTargetContinuity.continuousAt_heatMean_age hage
    (embed (S.first v ω)) x).tendsto.comp harg
  have hbaseD := (ObservationTargetContinuity.continuousAt_heatMean_age hage
    (embed (S.second v ω-S.first v ω)) x).tendsto.comp harg
  have hbaseExp := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x:= -Λ)).mul harg)
  have hlim := (hUlim.add (((tendsto_const_nhds (x:=θ)).mul hexp).mul hDlim)).sub
    (hbaseU.add (((tendsto_const_nhds (x:=θ)).mul hbaseExp).mul hbaseD))
  simpa only [MixedNativePastThetaCentering.current,add_sub_cancel_left,map_sub,
    ControlledProfile.mean,offset,mul_one,Function.comp_def] using hlim

end SHE.MixedNativeEndpointLimit
