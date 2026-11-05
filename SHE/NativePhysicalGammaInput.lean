module

public import SHE.NativePhysicalGammaKernel
public import SHE.NativeGammaClock
public import SHE.ScalarHeatGammaSlots
public import SHE.AdditiveHaarForcing
public import SHE.OrthogonalItoChannels
public import SHE.StandardItoParameterFubini

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativePhysicalGammaInput
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v b:ℝ≥0)
variable {κ m U:ℝ} (hκ:0<κ) (hm:0<m)

variable (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1)
variable (B:ℝ) (hB:0≤B) (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
variable (hc0:Measurable[𝓕.predictable] c0) (hc1:Measurable[𝓕.predictable] c1)
variable (hr0:Measurable[𝓕.predictable] r0) (hr1:Measurable[𝓕.predictable] r1)
local notation "Raw"=>NativePhysicalGammaKernel.raw v b hκ hm g c0 c1 r0 r1
local notation "Hraw"=>NativePhysicalGammaKernel.raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1 hc0 hc1 hr0 hr1

def majorant (p:ℝ≥0×Ω):ℝ:=
  let C:=16*B^2*(κ+U)
  C+C*heatConstant*((NativeGammaClock.window v b).indicator
    (fun p=>(NativeGammaClock.age v b p)^(-(1/2:ℝ))) p)
local notation "Maj"=>majorant v b (κ:=κ) (U:=U) B

include hκ in
theorem majorant_nonneg (hU:0≤U) (p:ℝ≥0×Ω):0≤Maj p:=by
  have hC:0≤16*B^2*(κ+U):=mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (add_nonneg hκ.le hU)
  exact add_nonneg hC (mul_nonneg (mul_nonneg hC heatConstant_pos.le)
    (Set.indicator_nonneg (fun p hp=>Real.rpow_nonneg (NativeGammaClock.age_pos v b p).le _) p))

include hg hB in
theorem raw_majorized (p:ℝ≥0×Ω) (x:HeatCircle):‖Raw (p,x)‖^2≤Maj p:=by
  classical
  by_cases hp:p∈NativeGammaClock.window v b
  · have he:=NativePhysicalGammaKernel.raw_norm_sq v b hκ hm hB g hg c0 c1 r0 r1 p hp x
    exact he.trans_eq (by dsimp only [majorant];rw [Set.indicator_of_mem hp];ring)
  · rw [NativePhysicalGammaKernel.raw,if_neg hp,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0)]
    exact majorant_nonneg v b hκ B (elliptic_upper_nonneg (c0 p).1 m U hm (c0 p).2.2) p

include 𝓕 hbH hb1 in
theorem majorant_integrable :Integrable Maj (energyMeasure μ H):=by
  haveI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hi:=NativeGammaClock.power_integrable 𝓕 v b μ H hbH hb1 (ρ:=0) (by norm_num)
  simp only [zero_sub] at hi
  exact (integrable_const (16*B^2*(κ+U))).add (hi.const_mul (16*B^2*(κ+U)*heatConstant))

include hgm hg hB hc0 hc1 hr0 hr1 hbH hb1 in
theorem section_memLp (x:HeatCircle):
    @MemLp (ℝ≥0×Ω) (Both RealHaarInput) 𝓕.predictable _ _ (fun p=>Raw (p,x)) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
  have hs:StronglyMeasurable[𝓕.predictable] (fun p=>Raw (p,x)):=
    (Hraw).comp_measurable (measurable_id.prodMk measurable_const)
  have hsa:=hs.mono (predictable_le_product 𝓕)
  have hi:Integrable (fun p=>‖Raw (p,x)‖^2) (energyMeasure μ H):=by
    apply (majorant_integrable 𝓕 v b μ H hbH hb1 B).mono' (hsa.norm.pow 2).aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 p x
  have hm:MemLp (fun p=>Raw (p,x)) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm hsa.aestronglyMeasurable).mpr hi
  change eLpNorm (fun p=>Raw (p,x)) 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))<∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hs]
  exact hm

def process (x:HeatCircle):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  (section_memLp 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 x).toLp
    (fun p=>Raw (p,x))

include hgm hg hB hc0 hc1 hr0 hr1 hbH hb1 in
theorem process_ae (x:HeatCircle):
    process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 x=ᵐ[energyMeasure μ H]
      (fun p=>Raw (p,x)):=
  ae_eq_of_ae_eq_trim (section_memLp 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 x).coeFn_toLp

end SHE.NativePhysicalGammaInput
