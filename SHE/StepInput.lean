module

public import SHE.SignedTransport
public import SHE.InputProjection

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.StepInput
open MeasureTheory AddCircle CircleHeat
local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local instance : InnerProductSpace ℝ CircleL2 := InnerProductSpace.rclikeToReal ℂ CircleL2

/-- The actual linear synthesis of literal equal-cell real step fields. -/
def stepLinearMap (N : ℕ) [NeZero N] : (ZMod N → ℝ) →ₗ[ℝ] CircleL2 where
  toFun := stepLp N
  map_add' := stepLp_add N
  map_smul' c v := by simpa only [RingHom.id_apply] using stepLp_smul N c v

def stepSpace (N : ℕ) [NeZero N] : Submodule ℝ CircleL2 := (stepLinearMap N).range

instance stepSpace_finiteDimensional (N : ℕ) [NeZero N] : FiniteDimensional ℝ (stepSpace N) :=
  inferInstanceAs (FiniteDimensional ℝ (LinearMap.range (stepLinearMap N)))

instance stepSpace_complete (N : ℕ) [NeZero N] : CompleteSpace (stepSpace N) := inferInstance

instance stepSpace_projection (N : ℕ) [NeZero N] : (stepSpace N).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The massive negative norm is the actual inverse Fourier weight. -/
def negativeEnergy (κ Λ ρ : ℝ) (f : CircleL2) :=
  weightedFourierSq (fun n => (massiveWeight κ Λ ρ n)⁻¹) f

theorem negativeEnergy_summable {κ Λ ρ : ℝ} (hΛ : 0<Λ) (hρ : 0≤ρ) (f : CircleL2) :
    Summable (fun n : ℤ => (massiveWeight κ Λ ρ n)⁻¹*‖fourierCoeff f n‖^2) := by
  have hb (n : ℤ) : (massiveWeight κ Λ ρ n)⁻¹ ≤ Λ^(-ρ) := by
    unfold massiveWeight
    rw [← Real.rpow_neg (by positivity : 0 ≤ Λ+(κ*(n:ℝ))^2)]
    exact Real.rpow_le_rpow_of_nonpos hΛ (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (inv_nonneg.mpr (massiveWeight_nonneg hΛ.le κ ρ n)) (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (hb n) (sq_nonneg _))
    ((summable_fourier_sq f).mul_left (Λ^(-ρ)))

/-- Dyadic averaging is bounded from the actual massive negative
Fourier norm to L². This uses the proved step inverse and actual
orthogonal projection, rather than postulating the input estimate. -/
theorem step_projection_negative (N : ℕ) [NeZero N]
    {κ Λ ρ : ℝ} (hκ : 0≤κ) (hΛ : 0<Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (f : CircleL2)
    (hf : Summable (fun n : ℤ => (massiveWeight κ Λ ρ n)⁻¹*‖fourierCoeff f n‖^2)) :
    ‖(stepSpace N).starProjection f‖^2 ≤
      inverseConstant κ ρ*(Λ+(N:ℝ)^2)^ρ*negativeEnergy κ Λ ρ f := by
  have hw (n : ℤ) : 0<massiveWeight κ Λ ρ n :=
    Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg hΛ (sq_nonneg _)) _
  have hC : 0 ≤ inverseConstant κ ρ*(Λ+(N:ℝ)^2)^ρ :=
    mul_nonneg (inverseConstant_nonneg hκ hρ hρhalf) (Real.rpow_nonneg (by positivity) _)
  have hneg : negativeEnergy κ Λ ρ f =
      InputProjection.weightedEnergy (fourierBasis (T:=1)) (fun i => (massiveWeight κ Λ ρ i)⁻¹) f := by
    simp only [negativeEnergy,weightedFourierSq,InputProjection.weightedEnergy,fourierBasis_repr]
  rw [hneg]
  refine InputProjection.real_projection_bound (fourierBasis (T:=1)) (massiveWeight κ Λ ρ) hw
    (stepSpace N) (inverseConstant κ ρ*(Λ+(N:ℝ)^2)^ρ) hC ?_ ?_ f ?_
  · intro g
    obtain ⟨v,hv⟩ := g.property
    change stepLp N v=(g:CircleL2) at hv
    simpa only [fourierBasis_repr,← hv] using
      summable_stepLp_massive N v hκ hΛ.le hρ hρhalf
  · intro g
    obtain ⟨v,hv⟩ := g.property
    change stepLp N v=(g:CircleL2) at hv
    simpa only [InputProjection.weightedEnergy,weightedFourierSq,fourierBasis_repr,← hv] using
      stepLp_massive_inverse N v hκ hΛ.le hρ hρhalf
  · simpa only [fourierBasis_repr] using hf

/-- Every L² input automatically has the required negative Fourier
energy; the projection estimate needs no additional moment premise. -/
theorem step_projection_negative_L2 (N : ℕ) [NeZero N]
    {κ Λ ρ : ℝ} (hκ : 0≤κ) (hΛ : 0<Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2) (f : CircleL2) :
    ‖(stepSpace N).starProjection f‖^2 ≤
      inverseConstant κ ρ*(Λ+(N:ℝ)^2)^ρ*negativeEnergy κ Λ ρ f :=
  step_projection_negative N hκ hΛ hρ hρhalf f (negativeEnergy_summable hΛ hρ.le f)

end SHE.StepInput
