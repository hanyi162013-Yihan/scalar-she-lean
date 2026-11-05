module

public import SHE.NativeObservationProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Bounded-linear naturality of ordinary Hilbert Itô integration is
kept within stochastic package 1. The heat-specific integrand identity
and the resulting physical observation of a mild convolution are proved.
An actual mild-solution identity is an explicit model premise here. -/
noncomputable section
namespace SHE.NativeObservationNaturality
open Set MeasureTheory ProbabilityTheory StoppedFourier
open FiniteHaar DyadicApproximation NativeHeatObservation NativeObservationProcess PredictableL2
open scoped NNReal ENNReal
local instance nativeObservationNaturality_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeObservationNaturality_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance nativeObservationNaturality_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nativeObservationNaturality_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeObservationNaturality_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeObservationNaturality_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance nativeObservationNaturality_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance nativeObservationNaturality_rowSigma : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance nativeObservationNaturality_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {h : ℝ≥0}

/-- Ordinary stochastic-input package 1: scalar and Hilbert Itô
integrals driven by the same cylindrical noise commute with every
bounded real linear functional. No heat-specific statement occurs here. -/
structure StandardScalarNaturality
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h) : Prop where
  commutes : ∀ (L : RealL2 →L[ℝ] ℝ) (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h),
    (L.compLpL 2 μ) (I.integral v) = J.integral
      (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕))) v)

theorem observed_input_eq {ell M T t : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (ht : t < T) (x : HeatCircle) (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : v =ᵐ[energyMeasure μ h] (fun p => NativeHeatObservation.kernel ell M hell (t-(p.1:ℝ),f p))) :
    (((columnFunctional (T-t) x).compLpL 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕))) v)=
      NativeObservationProcess.process 𝓕 μ h hell hM f hf ht x := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hc := ae_eq_of_ae_eq_trim ((columnFunctional (T-t) x).coeFn_compLpL v)
  filter_upwards [hc,hv,NativeObservationProcess.process_ae 𝓕 μ h hell hM f hf ht x] with p hp hvp hr
  rw [hp,hvp,hr]
  rfl

theorem observe_terminal_integral
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J)
    {ell M T t : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (ht : t < T) (x : HeatCircle) (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : v =ᵐ[energyMeasure μ h] (fun p => NativeHeatObservation.kernel ell M hell (t-(p.1:ℝ),f p))) :
    (fun ω => functional (T-t) x (I.integral v ω)) =ᵐ[μ]
      J.integral (NativeObservationProcess.process 𝓕 μ h hell hM f hf ht x) := by
  have he := hIJ.commutes (functional (T-t) x) v
  change ((functional (T-t) x).compLpL 2 μ) (I.integral v) = J.integral
    (((columnFunctional (T-t) x).compLpL 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕))) v) at he
  rw [observed_input_eq hell hM f hf ht x v hv] at he
  have hc := (functional (T-t) x).coeFn_compLpL (I.integral v)
  rw [he] at hc
  exact hc.symm

/-- The actual physical heat observation of a native mild solution is
the ordinary scalar stochastic integral of its original-target Haar row.
The observation identity is derived from genuine column naturality and
heat propagation; it is not a stochastic black-box assumption. -/
theorem observe_mild_solution
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J)
    {ell M T t : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (ht : t < T) (ht0 : 0 ≤ t) (x : HeatCircle) (u : RealL2)
    (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : v =ᵐ[energyMeasure μ h] (fun p => NativeHeatObservation.kernel ell M hell (t-(p.1:ℝ),f p)))
    (U : Ω → RealL2) (hU : ∀ᵐ ω ∂μ,U ω=NativeHeatObservation.heat t u+I.integral v ω) :
    (fun ω => PhysicalProfile.physicalHeatMean (embed (U ω)) (T-t,x)) =ᵐ[μ]
      (fun ω => functional T x u+J.integral (NativeObservationProcess.process 𝓕 μ h hell hM f hf ht x) ω) := by
  filter_upwards [hU,observe_terminal_integral I J hIJ hell hM f hf ht x v hv] with ω hω hobs
  rw [← functional_physical (sub_pos.mpr ht),hω,map_add,functional_heat (sub_pos.mpr ht) ht0,hobs]
  rw [show T-t+t=T by ring]

end SHE.NativeObservationNaturality
