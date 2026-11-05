module

public import SHE.NativeObservationEndpoint
public import SHE.NativeStoppedBracket
public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FullHorizonEndpoint
open Set MeasureTheory PredictableL2 StoppedItoInputs FiniteHaar StoppedFourier
open NativeObservationEndpoint NativeObservationProcess
open scoped NNReal ENNReal
local instance fullHorizonEndpoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance fullHorizonEndpoint_finite : Fact ((2:ENNReal)≠∞) := ⟨by simp⟩
local instance fullHorizonEndpoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance fullHorizonEndpoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b : ℝ≥0)

/-- The original full-H measure restricted before b is exactly the
b-horizon measure. This is an input-space statement, not a new integral. -/
theorem energy_before (hbH : b≤H) :
    (energyMeasure μ H).restrict (before (Ω:=Ω) (b:ℝ))=energyMeasure μ b := by
  have hs : before (Ω:=Ω) (b:ℝ)=Iio b×ˢ (univ:Set Ω) := by
    ext p
    simp only [before,mem_setOf_eq,mem_prod,mem_Iio,mem_univ,and_true,NNReal.coe_lt_coe]
  rw [hs]
  change ((timeMeasure H).prod μ).restrict (Iio b×ˢ univ)=_
  rw [←Measure.restrict_prod_eq_prod_univ,NativeStoppedBracket.timeMeasure_before hbH]
  rfl

variable {ell M T : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (hT : (b:ℝ)≤T) (x : HeatCircle)

def raw : ℝ≥0×Ω→RealHaarInput := (before (b:ℝ)).indicator (fullIntegrand hell f T x)

include hf in
theorem raw_predictable : StronglyMeasurable[𝓕.predictable] (raw (T:=T) b hell f x) :=
  (fullIntegrand_predictable 𝓕 hell hf T x).indicator (before_measurable 𝓕 (b:ℝ))

include hf hM hT in
theorem raw_memLp (hbH : b≤H) : @MemLp _ _ 𝓕.predictable _ _ (raw (T:=T) b hell f x) 2
    ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  let g:=fun p:ℝ≥0×Ω=>M*(1+heatConstant*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
  have hi : Integrable ((before (b:ℝ)).indicator g) (energyMeasure μ H) := by
    rw [integrable_indicator_iff ((predictable_le_product 𝓕) _ (before_measurable 𝓕 (b:ℝ))),IntegrableOn,
      energy_before μ H b hbH]
    exact majorant_integrable μ b M b le_rfl
  have hp:=raw_predictable (T:=T) 𝓕 b hell f hf x
  have hpm:=hp.mono (predictable_le_product 𝓕)
  have hs : Integrable (fun p=>‖raw (T:=T) b hell f x p‖^2) (energyMeasure μ H) := by
    apply hi.mono' (hpm.norm.pow 2).aestronglyMeasurable
    filter_upwards with p
    simp only [Pi.pow_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    by_cases hpb : (p.1:ℝ)<(b:ℝ)
    · have hpt : (p.1:ℝ)<T:=hpb.trans_le hT
      simp only [raw,Set.indicator_of_mem (show p∈before (Ω:=Ω) (b:ℝ) from hpb),
        fullIntegrand,if_pos hpt]
      have hbefore : (p.1:ℝ)+T-(b:ℝ)<T:=by linarith
      have hafter : (p.1:ℝ)≤(p.1:ℝ)+T-(b:ℝ):=by linarith
      have hh:=NativeObservationProcess.row_norm_sq_bound hell (f p) hbefore hafter x
      simpa only [g,show T-((p.1:ℝ)+T-(b:ℝ))=(b:ℝ)-(p.1:ℝ) by ring] using hh
    · simp only [raw,Set.indicator_of_notMem (show p∉before (Ω:=Ω) (b:ℝ) from hpb),
        norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),le_refl]
  have hm : MemLp (raw (T:=T) b hell f x) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm hpm.aestronglyMeasurable).mpr hs
  change eLpNorm (raw (T:=T) b hell f x) 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))<∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hp]
  exact hm

def process (hbH : b≤H) : Process (E:=RealHaarInput) 𝓕 μ H :=
  (raw_memLp 𝓕 μ H b hell hM f hf hT x hbH).toLp (raw (T:=T) b hell f x)

theorem process_ae (hbH : b≤H) : process 𝓕 μ H b hell hM f hf hT x hbH=ᵐ[energyMeasure μ H]
    raw (T:=T) b hell f x :=
  ae_eq_of_ae_eq_trim (raw_memLp 𝓕 μ H b hell hM f hf hT x hbH).coeFn_toLp

end SHE.FullHorizonEndpoint
