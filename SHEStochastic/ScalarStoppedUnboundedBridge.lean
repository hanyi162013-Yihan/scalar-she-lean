module

public import SHEStochastic.ScalarStoppedFourierLocality
public import SHEStochastic.ScalarStoppedZeroEndpoint
public import SHEStochastic.ScalarStoppedDriftAlgebra
public import SHEStochastic.UnboundedGlobalFourierEquation
public import SHEStochastic.NativeFourierStateSeparation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedUnboundedBridge
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
  HeatParameterCover HeatParameterCoordinates GlobalHeatRowPhysicalIntegration
  UnboundedNativeHeatEquation
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ Noise)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)

local notation "J" => FiniteCylindricalIto.terminalIto P.toCoordinates e
local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁.le
local notation "S" => NativeHeatObservation.heat
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "u" => UnboundedGlobalFourierEquation.growingInput F μ H W hW hg hβ hβ₁
local notation "τ" => ContinuousNormExit.exit W

include hc in
private theorem growing_before (N : ℕ) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∀ᵐ p ∂energyMeasure μ H,(p.1 : WithTop ℝ≥0)<τ N p.2 →
      u N ψ n p=FourierHeatInput.multiplier H n p •
        StateNoiseCovariance.row ν hβ hβ₁.le hg (NativeFourierHeatCoordinate.weight ψ n) (physical W p) := by
  let V := UnboundedL2Localization.state (physical W) N
  let hV := UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N
  let hbound := UnboundedL2Localization.history_bound (physical W) μ H N
  have he := ae_eq_of_ae_eq_trim (FourierHeatInput.growing_ae_trim F V hV hg hβ hβ₁ μ H hbound ψ n)
  filter_upwards [he] with p he hp
  have hp' : (p.1 : WithTop ℝ≥0)<exit W N p.2 := by
    rwa [ScalarStoppedFourierLocality.exit_eq W N]
  change (u N ψ n) p=_ at he ⊢
  rw [he]
  apply congrArg (fun x => FourierHeatInput.multiplier H n p • x)
  let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [FourierHeatRowAverage.row,HolderStateRows.row_operator]
  dsimp only [V]
  rw [    UnboundedL2Localization.agrees_before_exit (physical W) (physical_continuous W hc) N p hp']
  rfl

/-- The actual unbounded scalar native solution gives the closed
localized Fourier equations for the original coefficient. -/
theorem of_native (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (heq : UnboundedGlobalNativeEquation.Equation F μ H W hW hg hβ hβ₁ P e u₀) :
    ScalarStoppedMildMoment.Equation F μ H W hW hc hg hβ hβ₁.le J b (fun _ _ => 0) u₀ := by
  intro N t ht ψ n
  have h := ScalarStoppedZeroEndpoint.closed F μ H W hW hc hg hβ hβ₁.le J u₀ hH
    (FiniteCylindricalIto.continuousStoppedVersions P e) N ψ n ?_ t ht
  · filter_upwards [h] with ω hω hbefore
    rw [ScalarStoppedDriftAlgebra.zero,sub_zero]
    exact hω hbefore
  · intro r hr
    have h₁ := UnboundedGlobalFourierEquation.coordinate F μ H hH W hW hg hβ hβ₁ P e u₀ hc heq N ψ n r hr
    have h₂ := ScalarStoppedFourierLocality.compare F μ H W hW hc hg hβ hβ₁.le N ψ n P e hn
      (u N ψ n) (growing_before F μ H W hW hc hg hβ hβ₁ N ψ n) r hr.le
    filter_upwards [h₁,h₂] with ω h₁ h₂ hω
    have hω' : (r : WithTop ℝ≥0)<exit W N ω := by
      rwa [ScalarStoppedFourierLocality.exit_eq W N]
    rw [map_sub,NativeFourierHeatCoordinate.coordinate_heat ψ n (t := (r : ℝ)) r.property,h₁ hω',h₂ hω]
    ring

/-- The original positive-heat mild tests follow from the same stopped
Fourier identity. This supplies the drift-free uniqueness entry point. -/
theorem to_native (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (heq : ScalarStoppedMildMoment.Equation F μ H W hW hc hg hβ hβ₁.le J b (fun _ _ => 0) u₀) :
    UnboundedGlobalNativeEquation.Equation F μ H W hW hg hβ hβ₁ P e u₀ := by
  intro N T δ hTH hδ hTD x
  let V := UnboundedL2Localization.state (physical W) N
  let hV := UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N
  let hv := UnboundedL2Localization.history_bound (physical W) μ H N
  obtain ⟨Y,hYm,hYe,hYc⟩ := UnboundedGlobalHeatContinuity.exists_native_continuous_modification
    F V hV hg hβ hβ₁ μ H hv P e
  let R (ω : Ω) := NativeRemainderObservation.remainder
    ⟨fun p => Y p ω,hYc ω⟩ (unitTime H hH T hTH)
  have hm (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) : ∀ᵐ ω ∂μ,(T : WithTop ℝ≥0)<τ N ω →
      φ ψ n (W T ω)=φ ψ n (S (T : ℝ) u₀+R ω) := by
    have hC := ScalarStoppedFourierLocality.compare F μ H W hW hc hg hβ hβ₁.le N ψ n P e hn
      (u N ψ n) (growing_before F μ H W hW hc hg hβ hβ₁ N ψ n) T hTH
    filter_upwards [heq N T hTH ψ n,hC,GlobalNativeFourierRemainder.coordinate
      F V hV hg hβ hβ₁ μ H hH hv J ψ n T hTH Y hYm hYc hYe] with ω he hi hr hω
    have h := he hω
    rw [ScalarStoppedDriftAlgebra.zero,sub_zero,map_sub,hi hω] at h
    change φ ψ n (R ω) =
      Real.exp (-(T : ℝ)*(n : ℝ)^2)*(J).integral (StoppedItoInputs.stop F μ H T (u N ψ n)) ω at hr
    rw [map_add,hr]
    linarith only [h]
  have hs : ∀ᵐ ω ∂μ,(T : WithTop ℝ≥0)<τ N ω → W T ω=S (T : ℝ) u₀+R ω := by
    filter_upwards [ae_all_iff.mpr (hm Complex.reCLM),ae_all_iff.mpr (hm Complex.imCLM)] with ω hr hi hω
    exact NativeFourierStateSeparation.ext (fun n => hr n hω) (fun n => hi n hω)
  have ho := GlobalRemainderObservation.stochastic_observation F V hV hg hβ hβ₁ μ H hH hv J
    T δ hTH hδ hTD x Y hYm hYc hYe
  filter_upwards [hs,ho] with ω hs ho hω
  rw [ScalarStoppedFourierLocality.exit_eq W N] at hω
  change NativeHeatObservation.functional (δ : ℝ) x (R ω) = _ at ho
  rw [hs hω,map_add,ho]
  have hmean := NativeHeatObservation.functional_heat hδ T.property x u₀
  have hmean' : NativeHeatObservation.functional (δ : ℝ) x (S (T : ℝ) u₀) =
      NativeHeatObservation.functional ((T+δ : ℝ≥0) : ℝ) x u₀ := by
    exact hmean.trans (congrArg (fun r : ℝ => NativeHeatObservation.functional r x u₀)
      (add_comm (δ : ℝ) (T : ℝ)))
  exact congrArg (fun y : ℝ => y + (J).integral
    (StoppedItoInputs.stop F μ H T (UnboundedFiniteHorizonInput.input F V hV hg hβ hβ₁ μ H
      (T+δ) hTD x hv)) ω) hmean'

end SHEStochastic.ScalarStoppedUnboundedBridge
