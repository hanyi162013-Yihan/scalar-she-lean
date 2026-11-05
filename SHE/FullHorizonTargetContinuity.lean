module

public import SHE.FullHorizonEndpointVersion
public import SHE.NativeRowTargetContinuity
public import SHE.PredictableSquareDominatedLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.FullHorizonTargetContinuity
open Set MeasureTheory PredictableL2 StoppedItoInputs FiniteHaar StoppedFourier NativeHeatObservation
open NativeObservationEndpoint NativeObservationProcess Filter Topology
open scoped NNReal ENNReal
local instance fullHorizonTargetContinuity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance fullHorizonTargetContinuity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f) (hbH : b≤H)

def majorant (p : ℝ≥0×Ω) : ℝ:=
  (before (b:ℝ)).indicator (fun p=>M*(1+heatConstant*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))) p

include 𝓕 hbH in
theorem majorant_integrable : Integrable (majorant (Ω:=Ω) (M:=M) b) (energyMeasure μ H) := by
  change Integrable ((before (b:ℝ)).indicator (fun p=>M*(1+heatConstant*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ))))) (energyMeasure μ H)
  rw [integrable_indicator_iff ((predictable_le_product 𝓕) _ (before_measurable 𝓕 (b:ℝ))),IntegrableOn,
    FullHorizonEndpoint.energy_before μ H b hbH]
  exact NativeObservationEndpoint.majorant_integrable μ b M b le_rfl

theorem process_bound {T : ℝ} (hT : (b:ℝ)≤T) (x : HeatCircle) :
    ∀ᵐ p∂energyMeasure μ H,‖FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf hT x hbH p‖^2≤majorant (M:=M) b p := by
  filter_upwards [FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf hT x hbH] with p hp
  rw [hp]
  by_cases hpb : (p.1:ℝ)<(b:ℝ)
  · simp only [FullHorizonEndpoint.raw,majorant,indicator_of_mem (show p∈before (Ω:=Ω) (b:ℝ) from hpb),
      fullIntegrand,ite_eq_left (hpb.trans_le hT)]
    have hh:=row_norm_sq_bound hell (f p)
      (show (p.1:ℝ)+T-(b:ℝ)<T by linarith) (show (p.1:ℝ)≤(p.1:ℝ)+T-(b:ℝ) by linarith) x
    simpa only [show T-((p.1:ℝ)+T-(b:ℝ))=(b:ℝ)-(p.1:ℝ) by ring] using hh
  · simp only [FullHorizonEndpoint.raw,majorant,indicator_of_notMem (show p∉before (Ω:=Ω) (b:ℝ) from hpb),
      norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),le_refl]

/-- Changing the original heat target continuously, including a target
that reaches the stop b, converges in the SAME original predictable L²
space. The actual singular row majorant is integrable. -/
theorem tendsto {T : ℝ} (hT : (b:ℝ)≤T) (Tn : ℕ→ℝ) (hTn : ∀ n,(b:ℝ)≤Tn n)
    (hlim : Tendsto Tn atTop (𝓝 T)) (x : HeatCircle) :
    Tendsto (fun n=>FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf (hTn n) x hbH) atTop
      (𝓝 (FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf hT x hbH)) := by
  apply PredictableSquareDominatedLimit.tendsto 𝓕 μ H _ _ (majorant (M:=M) b)
    (majorant_integrable 𝓕 μ H b hbH)
    (fun n=>process_bound 𝓕 μ H b hell hM f hf hbH (hTn n) x)
    (process_bound 𝓕 μ H b hell hM f hf hbH hT x)
  filter_upwards [ae_all_iff.mpr (fun n=>FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf (hTn n) x hbH),
    FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf hT x hbH] with p hn hp
  rw [hp]
  have he : (fun n=>FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf (hTn n) x hbH p)=
      (fun n=>FullHorizonEndpoint.raw (T:=Tn n) b hell f x p):=funext hn
  rw [he]
  by_cases hpb : (p.1:ℝ)<(b:ℝ)
  · have hpt : (p.1:ℝ)<T:=hpb.trans_le hT
    have hptn (n:ℕ) : (p.1:ℝ)<Tn n:=hpb.trans_le (hTn n)
    simp only [FullHorizonEndpoint.raw,indicator_of_mem (show p∈before (Ω:=Ω) (b:ℝ) from hpb),
      fullIntegrand,ite_eq_left hpt,ite_eq_left (hptn _)]
    exact (NativeRowTargetContinuity.row_continuousAt_target hell (f p) hpt x).tendsto.comp hlim
  · simp only [FullHorizonEndpoint.raw,indicator_of_notMem (show p∉before (Ω:=Ω) (b:ℝ) from hpb)]
    exact tendsto_const_nhds

end SHE.FullHorizonTargetContinuity
