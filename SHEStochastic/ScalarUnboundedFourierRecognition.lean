module

public import SHEStochastic.ScalarUnboundedFourierProjection
public import SHEStochastic.GlobalBoundedFourierRecognition
public import SHEStochastic.GlobalRemainderObservation
public import SHEStochastic.UnboundedGlobalFourierEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnboundedFourierRecognition
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar
  MatrixInfiniteHaar AddCircle HeatParameterCover HeatParameterCoordinates HeatParameterPullback
  GlobalHeatRowPhysicalIntegration UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)
local notation "Vec" => Physical (d := Fin 1)
local notation "Noise" => Lp ℝ 2 ν₂
local notation "Input₁" => Input (d := Fin 1)
local notation "comp₀" => VectorHeatObservation.component (0 : Fin 1)
local notation "L" => ScalarUnboundedFourierRow.noiseEquiv
local notation "G" => ScalarUnboundedOneDimensional.coefficient
local instance : SecondCountableTopology Vec := Lp.SecondCountableTopology
local instance : MeasurableSpace Vec := borel _
local instance : BorelSpace Vec := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise := (L).toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Input₁ := borel _
local instance : BorelSpace Input₁ := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
  (U : ℝ≥0 × Ω → Vec) (hU : StronglyMeasurable[F.predictable] U)
  (hEnergy : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))

def state (t : ℝ≥0) (ω : Ω) : RealL2 := comp₀ (U (t,ω))

include hU in
theorem predictable : StronglyMeasurable[F.predictable] (Function.uncurry (state U)) :=
  (comp₀).continuous.comp_stronglyMeasurable hU

local notation "W" => state U
local notation "e" => ScalarUnboundedFourierProjection.basis
local notation "projInput" => ScalarUnboundedFourierProjection.input hg hβ hβ₁.le U hU hEnergy

private theorem integrals_agree (P : FiniteScalarIto.Family F μ H (Fin 1 × HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T
          (UnboundedGlobalFourierEquation.growingInput F μ H W (predictable U hU) hg hβ hβ₁ N a n)) ω =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (projInput a n)) ω := by
  let u := UnboundedGlobalFourierEquation.growingInput F μ H W (predictable U hU) hg hβ hβ₁ N a n
  let v := projInput a n
  have he := NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hnull
    (StoppedItoInputs.stop F μ H T u) (StoppedItoInputs.stop F μ H T v) T
  refine (he ?_ ?_ (exit W N) (exit_stopping F W (predictable U hU) hc N) ?_).mono ?_
  · rw [StoppedInputAlgebra.stop_stop,min_self]
  · rw [StoppedInputAlgebra.stop_stop,min_self]
  · have hu := ae_eq_of_ae_eq_trim (FourierHeatInput.growing_ae_trim F
      (UnboundedL2Localization.state (physical W) N)
      (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W (predictable U hU)) N)
      hg hβ hβ₁ μ H (UnboundedL2Localization.history_bound (physical W) μ H N) a n)
    filter_upwards [StoppedItoInputs.stop_ae F μ H T u,StoppedItoInputs.stop_ae F μ H T v,hu,
      ScalarUnboundedFourierProjection.input_ae hg hβ hβ₁.le U hU hEnergy a n]
      with p hsu hsv hu hv hbefore
    rw [hsu,hsv]
    by_cases ht : p ∈ StoppedItoInputs.before (Ω := Ω) T
    · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
      change u p = _ at hu
      change v p = _ at hv
      rw [hu,hv]
      apply congrArg (fun z => FourierHeatInput.multiplier H n p • z)
      let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      rw [FourierHeatRowAverage.row,HolderStateRows.row_operator,
        UnboundedL2Localization.agrees_before_exit (physical W) (physical_continuous W hc) N p hbefore]
      rfl
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht]
  · intro ω h ht
    exact h (le_of_lt ht)

/-- The projected Fourier identities give the original localized
positive-heat scalar equation with its actual native Brownian driver. -/
theorem equation (hH : 0<H) (P : FiniteScalarIto.Family F μ H (Fin 1 × HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (Z : Ω → Vec)
    (heq : MatrixUnboundedFourierPullback.Equation (F := F) (μ := μ) (H := H)
      (G g) (ScalarUnboundedOneDimensional.holder hg) hβ hβ₁.le U hU hEnergy P Z) :
    UnboundedGlobalNativeEquation.RandomEquation F μ H W (predictable U hU) hg hβ hβ₁ P e
      (fun ω => comp₀ (Z ω)) := by
  intro N T δ hTH hδ hTD x
  let V := UnboundedL2Localization.state (physical W) N
  let hV := UnboundedL2Localization.predictable F (physical W) (physical_predictable F W (predictable U hU)) N
  let hv := UnboundedL2Localization.history_bound (physical W) μ H N
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨Y,hYm,hYe,hYc⟩ := UnboundedGlobalHeatContinuity.exists_native_continuous_modification
    F V hV hg hβ hβ₁ μ H hv P e
  let R (ω : Ω) := NativeRemainderObservation.remainder
    ⟨fun p => Y p ω,hYc ω⟩ (unitTime H hH T hTH)
  have hm (a : ℂ →L[ℝ] ℝ) (n : ℤ) : ∀ᵐ ω ∂μ,
      (T : WithTop ℝ≥0) < exit W N ω →
      NativeFourierHeatCoordinate.coordinate a n (W T ω) =
      NativeFourierHeatCoordinate.coordinate a n (NativeHeatObservation.heat T (comp₀ (Z ω))+R ω) := by
    filter_upwards [ScalarUnboundedFourierProjection.equation hg hβ hβ₁.le U hU hEnergy P Z heq a n T hTH,
      integrals_agree hg hβ hβ₁ U hU hEnergy P hnull hc N a n T,
      GlobalNativeFourierRemainder.coordinate F V hV hg hβ hβ₁ μ H hH hv J a n T hTH Y hYm hYc hYe]
      with ω he hi hr hω
    change _ = _ + J.integral (StoppedItoInputs.stop F μ H T (projInput a n)) ω at he
    rw [←hi hω] at he
    change Real.exp ((T : ℝ)*(n : ℝ)^2)*NativeFourierHeatCoordinate.coordinate a n (W T ω) =
      NativeFourierHeatCoordinate.coordinate a n (comp₀ (Z ω)) +
        J.integral (StoppedItoInputs.stop F μ H T (FourierHeatInput.growingInput F V hV hg hβ hβ₁ μ H hv a n)) ω at he
    rw [map_add,NativeFourierHeatCoordinate.coordinate_heat a n (t := (T : ℝ)) (show 0 ≤ (T : ℝ) from T.property)]
    change NativeFourierHeatCoordinate.coordinate a n (R ω) = _ at hr
    rw [hr,←mul_add,←he,←mul_assoc,←Real.exp_add]
    rw [show -(T : ℝ)*(n : ℝ)^2+(T : ℝ)*(n : ℝ)^2 = 0 by ring,Real.exp_zero,one_mul]
  have hs : ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      W T ω = NativeHeatObservation.heat T (comp₀ (Z ω))+R ω := by
    filter_upwards [ae_all_iff.mpr (hm Complex.reCLM),ae_all_iff.mpr (hm Complex.imCLM)] with ω hr hi hω
    exact NativeFourierStateSeparation.ext (fun n => hr n hω) (fun n => hi n hω)
  have ho := GlobalRemainderObservation.stochastic_observation F V hV hg hβ hβ₁ μ H hH hv J
    T δ hTH hδ hTD x Y hYm hYc hYe
  filter_upwards [hs,ho] with ω hs ho hω
  change NativeHeatObservation.functional δ x (R ω) = _ at ho
  rw [hs hω,map_add,ho]
  have hmean := NativeHeatObservation.functional_heat hδ T.property x (comp₀ (Z ω))
  have hmean' : NativeHeatObservation.functional (δ : ℝ) x
      (NativeHeatObservation.heat (T : ℝ) (comp₀ (Z ω))) =
      NativeHeatObservation.functional ((T+δ : ℝ≥0) : ℝ) x (comp₀ (Z ω)) := by
    exact hmean.trans (congrArg (fun r : ℝ => NativeHeatObservation.functional r x (comp₀ (Z ω)))
      (add_comm (δ : ℝ) (T : ℝ)))
  exact congrArg (fun v : ℝ => v + J.integral
    (StoppedItoInputs.stop F μ H T (UnboundedFiniteHorizonInput.input F V hV hg hβ hβ₁ μ H
      (T+δ) hTD x hv)) ω) hmean'

end SHEStochastic.ScalarUnboundedFourierRecognition
