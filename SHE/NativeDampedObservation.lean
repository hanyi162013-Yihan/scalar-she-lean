module

public import SHE.NativeObservationNaturality
public import SHE.PredictableDamping

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeDampedObservation
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier DyadicApproximation
open scoped NNReal ENNReal
local instance nativeDampedObservation_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance nativeDampedObservation_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance nativeDampedObservation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeDampedObservation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def damped {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ)
    (v : Process (E := RealHaarInput) 𝓕 μ H) : Process (E := RealHaarInput) 𝓕 μ H :=
  PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ t)
    (PredictableDamping.weight_predictable 𝓕 Λ t) (PredictableDamping.weight_bound hΛ t) v

theorem observed_input_eq {Λ ell M T t : ℝ} (hΛ : 0≤Λ) (hell : 0<ell) (hM : 0≤M)
    (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (ht : t<T) (x : HeatCircle) (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ H)
    (hv : v=ᵐ[energyMeasure μ H] fun p => Real.exp (-Λ*(t-(p.1:ℝ))) • kernel ell M hell (t-(p.1:ℝ),f p)) :
    ((columnFunctional (T-t) x).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) v=
      damped 𝓕 μ H hΛ t (NativeObservationProcess.process 𝓕 μ H hell hM f hf ht x) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hc := ae_eq_of_ae_eq_trim ((columnFunctional (T-t) x).coeFn_compLpL v)
  filter_upwards [hc,hv,PredictableContraction.weighted_ae 𝓕 μ H (PredictableDamping.weight Λ t)
    (PredictableDamping.weight_predictable 𝓕 Λ t) (PredictableDamping.weight_bound hΛ t)
    (NativeObservationProcess.process 𝓕 μ H hell hM f hf ht x),
    NativeObservationProcess.process_ae 𝓕 μ H hell hM f hf ht x] with p hc hv hd hp
  change damped 𝓕 μ H hΛ t (NativeObservationProcess.process 𝓕 μ H hell hM f hf ht x) p=
    PredictableDamping.weight Λ t p • NativeObservationProcess.process 𝓕 μ H hell hM f hf ht x p at hd
  rw [hc,hv,hd,hp,map_smul]
  change Real.exp (-Λ*(t-(p.1:ℝ))) • NativeObservationProcess.integrand hell f T t x p=
    PredictableDamping.weight Λ t p • NativeObservationProcess.integrand hell f T t x p
  by_cases hs : (p.1:ℝ)<t
  · rw [PredictableDamping.weight_eq hs.le]
  · rw [NativeObservationProcess.integrand_eq hell f ht x p,ite_eq_right hs,smul_zero,smul_zero]

theorem observe_terminal
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ H)
    (hIJ : StandardScalarNaturality I J)
    {Λ ell M T t : ℝ} (hΛ : 0≤Λ) (hell : 0<ell) (hM : 0≤M)
    (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (ht : t<T) (x : HeatCircle) (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ H)
    (hv : v=ᵐ[energyMeasure μ H] fun p => Real.exp (-Λ*(t-(p.1:ℝ))) • kernel ell M hell (t-(p.1:ℝ),f p)) :
    (fun ω => functional (T-t) x (I.integral v ω))=ᵐ[μ]
      J.integral (damped 𝓕 μ H hΛ t (NativeObservationProcess.process 𝓕 μ H hell hM f hf ht x)) := by
  have he := hIJ.commutes (functional (T-t) x) v
  change ((functional (T-t) x).compLpL 2 μ) (I.integral v)=J.integral
    (((columnFunctional (T-t) x).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) v) at he
  rw [observed_input_eq 𝓕 μ H hΛ hell hM f hf ht x v hv] at he
  have hc := (functional (T-t) x).coeFn_compLpL (I.integral v)
  rw [he] at hc
  exact hc.symm

end SHE.NativeDampedObservation
