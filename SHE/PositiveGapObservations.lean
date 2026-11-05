module

public import SHE.StandardFiniteIto
public import SHE.NativeObservationNaturality
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual finite physical heat observations on a positive-gap window.
Their continuity, predictability, and scalar-integral representations
are derived from the native mild solution and literal Haar columns. -/
noncomputable section
namespace SHE.PositiveGapObservations
open MeasureTheory Set PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open NativeObservationNaturality StoppedItoInputs
open DyadicApproximation WordRecursion
open scoped NNReal ENNReal
local instance positiveGapObservations_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance positiveGapObservations_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance positiveGapObservations_realBorel : BorelSpace RealL2 := ⟨rfl⟩

theorem continuous_heat_action : Continuous (fun p : ℝ × RealL2 => heat p.1 p.2) := by
  have hp : Continuous (fun p : ℝ × RealL2 => (p.1/timeScale,p.2)) :=
    (continuous_fst.div_const timeScale).prodMk continuous_snd
  have hc := RealHeat.continuous_realHeat_action.comp hp
  exact hc

variable {Ω : Type*} [MeasurableSpace Ω]

def coordinate (δ T : ℝ) (x : HeatCircle) (U : ℝ≥0 × Ω → RealL2) (p : ℝ≥0 × Ω) : ℝ :=
  functional δ x (heat (T-(p.1:ℝ)-δ) (U p))

def value {n : ℕ} (δ : ℝ) (Z : Fin n → Observation) (U : ℝ≥0 × Ω → RealL2)
    (p : ℝ≥0 × Ω) : WordRecursion.State n :=
  WithLp.toLp 2 (fun i => coordinate δ (Z i).target (Z i).center U p)

theorem coordinate_continuous (δ T : ℝ) (x : HeatCircle) (U : ℝ≥0 × Ω → RealL2)
    {ω : Ω} (hU : Continuous (fun t => U (t,ω))) :
    Continuous (fun t => coordinate δ T x U (t,ω)) := by
  have ht : Continuous (fun t : ℝ≥0 => T-(t:ℝ)-δ) := by fun_prop
  have hp : Continuous (fun t : ℝ≥0 => (T-(t:ℝ)-δ,U (t,ω))) := ht.prodMk hU
  have hh := continuous_heat_action.comp hp
  have hc := (functional δ x).continuous.comp hh
  exact hc

theorem value_continuous {n : ℕ} (δ : ℝ) (Z : Fin n → Observation) (U : ℝ≥0 × Ω → RealL2)
    {ω : Ω} (hU : Continuous (fun t => U (t,ω))) :
    Continuous (fun t => value δ Z U (t,ω)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  exact continuous_pi (fun i => coordinate_continuous δ (Z i).target (Z i).center U hU)

theorem coordinate_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (δ T : ℝ) (x : HeatCircle) (U : ℝ≥0 × Ω → RealL2)
    (hU : StronglyMeasurable[𝓕.predictable] U) :
    StronglyMeasurable[𝓕.predictable] (coordinate δ T x U) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have ht := ((measurable_const (a := T)).sub (PredictableClock.real_time_measurable 𝓕)).sub_const δ
  have hp : @Measurable (ℝ≥0 × Ω) (ℝ × RealL2) 𝓕.predictable _
      (fun p => (T-(p.1:ℝ)-δ,U p)) := ht.prodMk hU.measurable
  have hh := continuous_heat_action.measurable.comp hp
  have hc := (functional δ x).continuous.comp_stronglyMeasurable hh.stronglyMeasurable
  exact hc

theorem value_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {n : ℕ} (δ : ℝ) (Z : Fin n → Observation) (U : ℝ≥0 × Ω → RealL2)
    (hU : StronglyMeasurable[𝓕.predictable] U) :
    StronglyMeasurable[𝓕.predictable] (value δ Z U) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  apply Measurable.stronglyMeasurable
  have hm : @Measurable (ℝ≥0 × Ω) (Fin n → ℝ) 𝓕.predictable _
      (fun p i => coordinate δ (Z i).target (Z i).center U p) :=
    measurable_pi_iff.mpr (fun i => (coordinate_predictable 𝓕 δ (Z i).target (Z i).center U hU).measurable)
  exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp hm

theorem coordinate_eq_functional {δ T : ℝ} (hδ : 0 < δ) (U : ℝ≥0 × Ω → RealL2)
    (x : HeatCircle) (p : ℝ≥0 × Ω) (ht : δ ≤ T-(p.1:ℝ)) :
    coordinate δ T x U p=functional (T-(p.1:ℝ)) x (U p) := by
  rw [coordinate,functional_heat hδ (sub_nonneg.mpr ht)]
  rw [show δ+(T-(p.1:ℝ)-δ)=T-(p.1:ℝ) by ring]

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n → Observation)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(h:ℝ))

def rows : Fin n → Process (E := RealHaarInput) 𝓕 μ h := fun i =>
  NativeObservationEndpoint.process 𝓕 μ h hell hM f hf
    (show (h:ℝ) ≤ (Z i).target by have := hgap i; linarith) (Z i).center

def initial (u : RealL2) : WordRecursion.State n :=
  WithLp.toLp 2 (fun i => functional (Z i).target (Z i).center u)

/-- Every coordinate has its true original-target scalar stochastic
integral representation. Ordinary bounded-linear naturality is the only
stochastic ingredient beyond the explicit native mild-solution identity. -/
theorem integral_representation
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J) (u : RealL2)
    (U : ℝ≥0 × Ω → RealL2) (v : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : ∀ t : ℝ≥0,t ≤ h → v t =ᵐ[energyMeasure μ h]
      (fun p => kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)))
    (hmild : ∀ (t : ℝ≥0),t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=heat t u+I.integral (v t) ω)
    (t : ℝ≥0) (ht : t ≤ h) :
    (fun ω => value δ Z U (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ h J (initial Z u) (rows 𝓕 μ h hell hM f hf Z hδ hgap) t := by
  have htarget (i : Fin n) : (t:ℝ) < (Z i).target := by
    have hth : (t:ℝ) ≤ h := by exact_mod_cast ht
    have := hgap i
    linarith
  have he (i : Fin n) := observe_mild_solution I J hIJ hell hM f hf (htarget i) t.2 (Z i).center u
    (v t) (hv t ht) (fun ω => U (t,ω)) (hmild t ht)
  filter_upwards [ae_all_iff.mpr he] with ω hω
  ext i
  change coordinate δ (Z i).target (Z i).center U (t,ω)=
    functional (Z i).target (Z i).center u+
      J.integral (stop 𝓕 μ h t (rows 𝓕 μ h hell hM f hf Z hδ hgap i)) ω
  have hg : δ ≤ (Z i).target-(t:ℝ) := (hgap i).trans (sub_le_sub_left (by exact_mod_cast ht) _)
  rw [coordinate_eq_functional hδ U _ _ hg,functional_physical (sub_pos.mpr (htarget i))]
  rw [rows,stop_endpoint_process 𝓕 μ h hell hM f hf _ (htarget i)]
  exact hω i

end SHE.PositiveGapObservations
