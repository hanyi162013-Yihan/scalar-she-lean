module

public import SHEStochastic.HolderLpComposition
public import SHEStochastic.CompactUniformComposition
public import SHEStochastic.StateDriverCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.CutoffNoiseCovarianceConvergence
open MeasureTheory Filter HolderCoefficientIntegrability
open scoped NNReal Topology
variable {X E V : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {G K : E → V} {C D β : ℝ≥0} (hG : HolderWith C β G) (hK : HolderWith D β K)
    (hβ : 0<β) (hβ1 : β≤1) {s : Set (Lp E 2 ν)} (hs : IsCompact s)

include hs in
/-- Literal weighted noise rows converge uniformly on compact L2 state
sets, with no artificial uniform bound on the original coefficient. -/
theorem row (k : C(X,ℝ)) :
    TendstoUniformlyOn
      (fun m : ℕ => StateNoiseCovariance.row ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) k)
      (StateNoiseCovariance.row ν hβ hβ1 hG k) atTop s := by
  simpa only [TendstoUniformlyOn,StateNoiseCovariance.row,Function.comp_def] using
    CompactUniformComposition.postcompose hs
      (fun (m : ℕ) => HolderCoefficientContinuity.continuous ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)))
      (HolderCoefficientContinuity.continuous ν hβ hβ1 hG)
      (HolderLpComposition.cutoff_uniformly_on_compact ν hG hβ hβ1 hs)
      (fun g : Lp V 2 ν => ContinuousKernelLpAction.operator ν g k)
      (HolderRowCovariance.continuous_coefficient ν k)

include hs in
/-- Every component cross covariance has the correct compact-uniform
limit. Distinct G and K retain off-diagonal matrix brackets. -/
theorem covariance (k l : C(X,ℝ)) :
    TendstoUniformlyOn
      (fun m : ℕ => StateNoiseCovariance.value ν hβ hβ1
        (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0))
        (UnboundedCoefficientCutoff.holder hK (m : ℝ≥0)) k l)
      (StateNoiseCovariance.value ν hβ hβ1 hG hK k l) atTop s := by
  have hGlim := HolderLpComposition.cutoff_uniformly_on_compact ν hG hβ hβ1 hs
  have hKlim := HolderLpComposition.cutoff_uniformly_on_compact ν hK hβ hβ1 hs
  have hc : Continuous (fun z : Lp V 2 ν×Lp V 2 ν =>
      inner ℝ (ContinuousKernelLpAction.operator ν z.1 k) (ContinuousKernelLpAction.operator ν z.2 l)) :=
    ((HolderRowCovariance.continuous_coefficient ν k).comp continuous_fst).inner
      ((HolderRowCovariance.continuous_coefficient ν l).comp continuous_snd)
  simpa only [TendstoUniformlyOn,StateNoiseCovariance.value,StateNoiseCovariance.row,Function.comp_def] using
    CompactUniformComposition.postcompose hs
      (fun (m : ℕ) => (HolderCoefficientContinuity.continuous ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0))).prodMk
        (HolderCoefficientContinuity.continuous ν hβ hβ1 (UnboundedCoefficientCutoff.holder hK (m : ℝ≥0))))
      ((HolderCoefficientContinuity.continuous ν hβ hβ1 hG).prodMk
        (HolderCoefficientContinuity.continuous ν hβ hβ1 hK))
      (by
        intro V hV
        have hd : Tendsto (fun m : ℕ => (m,m)) atTop (atTop ×ˢ atTop) := tendsto_id.prodMk tendsto_id
        exact hd ((hGlim.prodMk hKlim) V hV)) _ hc

include hs in
/-- The mixed state/driver brackets converge for the same retained
noise direction. This does not replace the driver by one with equal law. -/
theorem mixed (k : C(X,ℝ)) (b : Lp V 2 ν) :
    TendstoUniformlyOn
      (fun m : ℕ => StateDriverCovariance.value ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) k b)
      (StateDriverCovariance.value ν hβ hβ1 hG k b) atTop s := by
  have hc : Continuous (fun g : Lp V 2 ν => inner ℝ (ContinuousKernelLpAction.operator ν g k) b) :=
    (HolderRowCovariance.continuous_coefficient ν k).inner continuous_const
  simpa only [TendstoUniformlyOn,StateDriverCovariance.value,StateNoiseCovariance.row,Function.comp_def] using
    CompactUniformComposition.postcompose hs
      (fun (m : ℕ) => HolderCoefficientContinuity.continuous ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)))
      (HolderCoefficientContinuity.continuous ν hβ hβ1 hG)
      (HolderLpComposition.cutoff_uniformly_on_compact ν hG hβ hβ1 hs) _ hc

end SHEStochastic.CutoffNoiseCovarianceConvergence
