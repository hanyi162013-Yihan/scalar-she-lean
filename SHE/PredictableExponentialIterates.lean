module
public import SHE.PredictableExponential
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.PredictableExponentialIterates
open MeasureTheory PredictableL2 Filter Topology
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)
local notation "Scale"=>PredictableExponential.scale 𝓕 μ H

theorem scale_norm(γ:ℝ)(v:Process (E:=E) 𝓕 μ H):
    ‖Scale γ v‖≤Real.exp (|γ| * (H:ℝ))*‖v‖:=by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(PredictableMultiplier.memLp 𝓕 μ H (PredictableExponential.weight H γ)
    (PredictableExponential.predictable 𝓕 H γ) _ (PredictableExponential.bound H γ) v).coeFn_toLp]
    with p hp
  change Scale γ v p=PredictableExponential.weight H γ p • v p at hp
  rw [hp,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (PredictableExponential.bound H γ p) (norm_nonneg _)

theorem scale_lipschitz(γ:ℝ):LipschitzWith
    ⟨Real.exp (|γ| * (H:ℝ)),(Real.exp_pos _).le⟩ (PredictableExponential.scale (E:=E) 𝓕 μ H γ):=by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm,←PredictableExponential.sub]
  exact scale_norm 𝓕 μ H γ (u-v)

/-- Literal ordinary Picard iterates are conjugate to the weighted
contraction iterates, from every supplied starting process. -/
theorem conjugate_iterate(γ:ℝ)(forcing:Process (E:=E) 𝓕 μ H)
    (N:Process (E:=E) 𝓕 μ H→Process (E:=E) 𝓕 μ H)
    (start:Process (E:=E) 𝓕 μ H)(n:ℕ):
    Scale γ ((PredictableExponential.conjugate 𝓕 μ H γ forcing N)^[n] (Scale (-γ) start))=
      (fun v=>forcing+N v)^[n] start:=by
  induction n with
  | zero=>simpa only [Function.iterate_zero_apply] using PredictableExponential.cancel' 𝓕 μ H γ start
  | succ n ih=>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',PredictableExponential.conjugate,
      PredictableExponential.cancel',ih]

variable [CompleteSpace E]

/-- Weighted contraction proves convergence of the original Picard
iteration in its ordinary predictable product-L2 norm on the full
fixed horizon, not only convergence after exponential reweighting. -/
theorem tendsto(γ:ℝ)(forcing:Process (E:=E) 𝓕 μ H)
    (N:Process (E:=E) 𝓕 μ H→Process (E:=E) 𝓕 μ H)
    (hLip:LipschitzWith (1/2) (PredictableExponential.conjugate 𝓕 μ H γ forcing N))
    (v:Process (E:=E) 𝓕 μ H)(hv:v=forcing+N v)(start:Process (E:=E) 𝓕 μ H):
    Tendsto (fun n:ℕ=>(fun w=>forcing+N w)^[n] start) atTop (𝓝 v):=by
  let Φ:=PredictableExponential.conjugate 𝓕 μ H γ forcing N
  have hc:ContractingWith (1/2) Φ:=⟨by norm_num,hLip⟩
  let z:=Scale (-γ) v
  have hz:Φ z=z:=by
    dsimp only [Φ,z,PredictableExponential.conjugate]
    rw [PredictableExponential.cancel',←hv]
  have he:hc.fixedPoint Φ=z:=(hc.fixedPoint_unique hz).symm
  have hl:=hc.tendsto_iterate_fixedPoint (Scale (-γ) start)
  rw [he] at hl
  have ht:=((scale_lipschitz (E:=E) 𝓕 μ H γ).continuous.tendsto z).comp hl
  simpa only [Function.comp_def,conjugate_iterate,Φ,z,PredictableExponential.cancel'] using ht

end SHE.PredictableExponentialIterates
