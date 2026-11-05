module
public import SHE.FiniteItoNoise
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.FiniteItoGradientAction
open MeasureTheory PredictableL2 FiniteItoNoise
open scoped NNReal ENNReal
variable {Ω C:Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)
variable {n:ℕ}(Y:ℝ≥0×Ω→State n)(hY:StronglyMeasurable[𝓕.predictable] Y)
variable (R:Fin n→Process (E:=C) 𝓕 μ H)

def direction (ℓ:C→L[ℝ]ℝ)(p:ℝ≥0×Ω):State n:=WithLp.toLp 2 (fun i=>ℓ (R i p))

theorem coordinates (A:State n→L[ℝ]ℝ)(v:State n):
    A v=∑i:Fin n,A (EuclideanSpace.basisFun (Fin n) ℝ i)*v i:=by
  conv_lhs=>rw [←(EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  rw [map_sum]
  simp only [map_smul,EuclideanSpace.basisFun_repr,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Evaluation of the FULL named finite-Ito gradient row is exactly the
Gaussian mean derivative in its corresponding actual input direction. -/
theorem action (ℓ:C→L[ℝ]ℝ)(G:ℝ→State n→ℝ)(p:ℝ≥0×Ω):
    ℓ (FiniteItoNoise.gradientRow 𝓕 μ H Y R G p)=
      fderiv ℝ (G (p.1:ℝ)) (Y p) (direction 𝓕 μ H R ℓ p):=by
  rw [coordinates]
  simp only [FiniteItoNoise.gradientRow,map_sum,map_smul,FiniteItoNoise.gradientCoefficient,
    direction,WithLp.ofLp_toLp,smul_eq_mul]

/-- The original predictable gradient process has that SAME full
coordinate action on a genuine original time/sample event. -/
theorem process_ae (ℓ:C→L[ℝ]ℝ)(G:ℝ→State n→ℝ)(hG:FiniteItoNoise.AdmissibleGradient G):
    ∀ᵐp∂energyMeasure μ H,ℓ (FiniteItoNoise.gradientProcess 𝓕 μ H Y hY R G hG p)=
      fderiv ℝ (G (p.1:ℝ)) (Y p) (direction 𝓕 μ H R ℓ p):=by
  filter_upwards [FiniteItoNoise.gradientProcess_ae 𝓕 μ H Y hY R G hG] with p hp
  rw [hp]
  exact action 𝓕 μ H Y R ℓ G p

/-- When the actual finite test is differentiable, its full row action
is the literal scalar directional derivative used by KernelFTC. -/
theorem action_deriv (ℓ:C→L[ℝ]ℝ)(G:ℝ→State n→ℝ)(p:ℝ≥0×Ω)
    (hG:DifferentiableAt ℝ (G (p.1:ℝ)) (Y p)):
    ℓ (FiniteItoNoise.gradientRow 𝓕 μ H Y R G p)=
      deriv (fun t:ℝ=>G (p.1:ℝ) (Y p+t•direction 𝓕 μ H R ℓ p)) 0:=by
  have hl:HasDerivAt (fun t:ℝ=>Y p+t•direction 𝓕 μ H R ℓ p) (direction 𝓕 μ H R ℓ p) 0:=by
    convert ((hasDerivAt_id (0:ℝ)).smul_const (direction 𝓕 μ H R ℓ p)).const_add (Y p) using 1 <;> simp only [id_eq,one_smul]
  have hG' :HasFDerivAt (G (p.1:ℝ)) (fderiv ℝ (G (p.1:ℝ)) (Y p)) (Y p+(0:ℝ)•direction 𝓕 μ H R ℓ p):=by
    simpa only [zero_smul,add_zero] using hG.hasFDerivAt
  have hd:=hG'.comp_hasDerivAt 0 hl
  rw [action]
  simpa only [zero_smul,add_zero,Function.comp_def] using hd.deriv.symm
end SHE.FiniteItoGradientAction
