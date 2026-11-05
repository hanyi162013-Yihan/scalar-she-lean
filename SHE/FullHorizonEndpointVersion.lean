module

public import SHE.FullHorizonEndpoint
public import SHE.SingularStoppedVersion
public import SHE.StoppedInputAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FullHorizonEndpointVersion
open Set MeasureTheory PredictableL2 StoppedItoInputs FiniteHaar StoppedFourier NativeHeatObservation
open NativeObservationEndpoint NativeObservationProcess
open scoped NNReal ENNReal
local instance fullHorizonEndpointVersion_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance fullHorizonEndpointVersion_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b : ℝ≥0)
variable {ell M T : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (hT : (b:ℝ)≤T) (x : HeatCircle) (hbH : b≤H)
local notation "u" => FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf hT x hbH

/-- Prefix observations are restrictions of ONE original full-horizon
endpoint input, rather than integrals restarted on a new horizon. -/
theorem stop_eq_prefix (c : ℝ≥0) (hcb : c≤b) (hcT : (c:ℝ)<T) :
    stop 𝓕 μ H c u=NativeObservationProcess.process 𝓕 μ H hell hM f hf hcT x := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [stop_ae 𝓕 μ H c u,
    FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf hT x hbH,
    NativeObservationProcess.process_ae 𝓕 μ H hell hM f hf hcT x] with p hs hu hp
  rw [hs,hp,integrand_eq hell f hcT]
  by_cases hpc : (p.1:ℝ)<(c:ℝ)
  · have hpb : (p.1:ℝ)<(b:ℝ):=hpc.trans_le (by exact_mod_cast hcb)
    have hpT : (p.1:ℝ)<T:=hpc.trans hcT
    rw [Set.indicator_of_mem (show p∈before (Ω:=Ω) (c:ℝ) from hpc),hu]
    simp only [
      FullHorizonEndpoint.raw,Set.indicator_of_mem (show p∈before (Ω:=Ω) (b:ℝ) from hpb),
      fullIntegrand,if_pos hpT,if_pos hpc]
  · simp only [Set.indicator_of_notMem (show p∉before (Ω:=Ω) (c:ℝ) from hpc),if_neg hpc]

/-- The true singular endpoint row has a deterministic inverse-root cap,
sufficient for the already proved dyadic continuous-version theorem. -/
theorem singular_bound (hb1 : (b:ℝ)≤1) :
    ∀ᵐ p∂energyMeasure μ H,p.1≤b→‖u p‖^2≤
      (M*(1+heatConstant))*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) := by
  filter_upwards [FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf hT x hbH] with p hp hpb
  rw [hp]
  by_cases hlt : (p.1:ℝ)<(b:ℝ)
  · have hpT : (p.1:ℝ)<T:=hlt.trans_le hT
    simp only [FullHorizonEndpoint.raw,indicator_of_mem (show p∈before (Ω:=Ω) (b:ℝ) from hlt),
      fullIntegrand,if_pos hpT]
    have ha : 0<(b:ℝ)-(p.1:ℝ):=sub_pos.mpr hlt
    have ha1 : (b:ℝ)-(p.1:ℝ)≤1:=(sub_le_self _ p.1.2).trans hb1
    have hpow:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by norm_num : -(1/2:ℝ)≤0)
    have hh:=row_norm_sq_bound hell (f p)
      (show (p.1:ℝ)+T-(b:ℝ)<T by linarith)
      (show (p.1:ℝ)≤(p.1:ℝ)+T-(b:ℝ) by linarith) x
    have he : T-((p.1:ℝ)+T-(b:ℝ))=(b:ℝ)-(p.1:ℝ):=by ring
    rw [he] at hh
    calc
      _≤M*(1+heatConstant*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ))):=hh
      _≤_:=by nlinarith [mul_nonneg hM (sub_nonneg.mpr hpow)]
  · simp only [FullHorizonEndpoint.raw,indicator_of_notMem (show p∉before (Ω:=Ω) (b:ℝ) from hlt),norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact mul_nonneg (mul_nonneg hM (add_nonneg zero_le_one heatConstant_pos.le)) (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hpb)) _)

variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)

def version : ℝ≥0→Ω→ℝ:=SingularStoppedVersion.version 𝓕 μ H b J u

theorem continuous_version (hb0 : 0<b) (ω : Ω) :
    Continuous (fun t=>version 𝓕 μ H b hell hM f hf hT x hbH J t ω) :=
  SingularStoppedVersion.continuous_version 𝓕 μ H b J u hb0 ω

theorem version_ae (hb0 : 0<b) (hb1 : (b:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B) (t : ℝ≥0) :
    version 𝓕 μ H b hell hM f hf hT x hbH J t=ᵐ[μ] J.integral (stop 𝓕 μ H (min t b) u) :=
  SingularStoppedVersion.version_ae 𝓕 μ H b J u hbH hb0 B hBDG
    (mul_nonneg hM (add_nonneg zero_le_one heatConstant_pos.le)) (singular_bound 𝓕 μ H b hell hM f hf hT x hbH hb1) t

end SHE.FullHorizonEndpointVersion
