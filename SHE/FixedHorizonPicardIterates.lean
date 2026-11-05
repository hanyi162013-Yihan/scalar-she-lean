module
public import SHE.FixedHorizonPicard
public import SHE.PredictableExponentialIterates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.FixedHorizonPicardIterates
open MeasureTheory Set PredictableL2 LowBands NonlinearHaarIntegrand Filter Topology
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable (h:ℝ≥0)(hh:(h:ℝ)≤1){Λ:ℝ}(hΛ:0≤Λ)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M H β:ℝ}
variable (hell:0<ell)(hb:∀z,ell≤a z ∧ a z≤M)
variable (hβ:0<β)(hH:0≤H)(hholder:∀z w,|a z-a w|≤H*|z-w|^β)
variable (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)
variable (B:ℝ≥0)(hBDG:StandardTerminalBDG16 I B)(hpos:0<h)
local notation "N"=>DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I
local notation "Scale"=>PredictableExponential.scale 𝓕 μ h
include hBDG hpos

/-- The actual full-horizon stochastic Picard map has a weighted
contraction, with weight independent of the Picard starting point. -/
theorem exists_weight {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))
    (forcing:Process (E:=StateL2) 𝓕 μ h):
    ∃γ:ℝ,1≤γ ∧ LipschitzWith (1/2)
      (PredictableExponential.conjugate 𝓕 μ h γ forcing N):=by
  obtain ⟨γ,hγ,hsmall⟩:=BieleckiKernel.exists_contraction_weight (CompanionHeat.picardConstant ell M L)
  have hγpos:0<γ:=zero_lt_one.trans_le hγ
  refine ⟨γ,hγ,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he:=FixedHorizonPicard.weighted_bound 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I B hBDG hpos hLip hγpos
    (Scale γ u) (Scale γ v)
  have hs:Scale (-γ) (Scale γ u-Scale γ v)=u-v:=by
    rw [←PredictableExponential.sub,PredictableExponential.cancel]
  have hC:0≤CompanionHeat.picardConstant ell M L*BieleckiKernel.mass γ:=mul_nonneg
    (CompanionHeat.picardConstant_nonneg (hell.le.trans ((hb 0).1.trans (hb 0).2)) L)
    (BieleckiKernel.mass_nonneg hγpos.le)
  rw [hs,←ENNReal.ofReal_mul hC] at he
  have hreal:‖Scale (-γ) (N (Scale γ u)-N (Scale γ v))‖^2≤(1/4:ℝ)*‖u-v‖^2:=
    ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).mp he).trans
      (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))
  have hd:PredictableExponential.conjugate 𝓕 μ h γ forcing N u-
      PredictableExponential.conjugate 𝓕 μ h γ forcing N v=
      Scale (-γ) (N (Scale γ u)-N (Scale γ v)):=by
    rw [PredictableExponential.conjugate,PredictableExponential.conjugate,
      ←PredictableExponential.sub,add_sub_add_left_eq_sub]
  rw [dist_eq_norm,dist_eq_norm,hd]
  change ‖Scale (-γ) (N (Scale γ u)-N (Scale γ v))‖≤(1/2:ℝ)*‖u-v‖
  nlinarith only [hreal,norm_nonneg (Scale (-γ) (N (Scale γ u)-N (Scale γ v))),norm_nonneg (u-v)]

/-- Original smooth Picard iterates converge to any actual fixed point
in ordinary predictable product-L2, on every prescribed positive h≤1. -/
theorem tendsto {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))
    (forcing v start:Process (E:=StateL2) 𝓕 μ h)(hv:v=forcing+N v):
    Tendsto (fun n:ℕ=>(fun w=>forcing+N w)^[n] start) atTop (𝓝 v):=by
  obtain ⟨γ,hγ,hc⟩:=exists_weight 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I B hBDG hpos hLip forcing
  exact PredictableExponentialIterates.tendsto 𝓕 μ h γ forcing N hc v hv start

/-- The same limit holds in the ambient, unweighted physical
time/sample L2 space used for comparing actual continuous versions. -/
theorem ambient_tendsto {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))
    (forcing v start:Process (E:=StateL2) 𝓕 μ h)(hv:v=forcing+N v):
    Tendsto (fun n:ℕ=>processEmbedding 𝓕 μ h ((fun w=>forcing+N w)^[n] start))
      atTop (𝓝 (processEmbedding 𝓕 μ h v)):=
  (processEmbedding 𝓕 μ h).continuous.continuousAt.tendsto.comp
    (tendsto 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I B hBDG hpos hLip forcing v start hv)

end SHE.FixedHorizonPicardIterates
