module
public import SHE.MixedJointUncutDefectTrace

public import SHE.MixedJointUncutMark
public import SHE.NativeDefectHaarAction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedJointActiveVolume
open Set MeasureTheory Real StoppedFourier OrthogonalItoChannels FiniteHaar PredictableL2 NativeHeatObservation
  DyadicApproximation
  CutoffWordLevel CutoffWordHistories CutoffCarriers UncutWordEvaluation GaussianItoTest
  GaussianTaylorAverage JointWordAnalytic
open scoped NNReal
local instance mixedJointUncutDefectTrace_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedJointUncutDefectTrace_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedJointUncutDefectTrace_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedJointUncutDefectTrace_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω X:Type}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R:ReferenceData}{n:ℕ}(L:Level R X n)
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U"=>(dU).physicalState
local notation "V"=>(dV).physicalState
local notation "XU"=>(dU).physicalField
local notation "XV"=>(dV).physicalField


/-- The literal full mark equals the full-volume integral of its
active current point. Only the lower endpoint singleton is discarded. -/
theorem mark_eq (k:ℕ)(h:History X k)(ω:Ω):
    MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω=
      ∫q:ℝ,MixedJointUncutDefectTrace.activePoint
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k ((h,ω),q):=by
  rw [MixedJointUncutDefectTrace.mark_eq_active_integral,
    intervalIntegral.integral_of_le ((carrier L k).terminal_base h),
    ←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne R.base] with q hq
  by_cases hz:R.base≤q ∧ q≤(carrier L k).terminal h
  · have hqi:q∈Ioc R.base ((carrier L k).terminal h):=
      ⟨lt_of_le_of_ne hz.1 hq.symm,hz.2⟩
    rw [Set.indicator_of_mem hqi]
  · have hqi:q∉Ioc R.base ((carrier L k).terminal h):=fun h=>hz ⟨h.1.le,h.2⟩
    rw [Set.indicator_of_notMem hqi]
    simp only [MixedJointUncutDefectTrace.activePoint,if_neg hz]
end SHE.MixedJointActiveVolume
