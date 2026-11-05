module

public import SHEStochastic.MatrixPointRowDomination
public import SHEStochastic.MatrixSquareCoefficient
public import SHEStochastic.MatrixDiffusionRows
public import SHEStochastic.HolderWeightedEnergy
public import SHEStochastic.VectorNativeHeatEndpoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixPointSquareEnergy
open MeasureTheory SHE SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d] {P : Profile d}

/-- Passing from the completed Haar factor to any original square
factor preserves every spatial observation row norm. -/
theorem feature_norm (A : MatrixSquareCoefficient.Data P) (v : Physical (d := d)) :
    ‖(factor P).adjoint v‖=‖BoundedFieldOperator.operator (BoundedFieldOperator.adjoint A.field) v‖ := by
  rw [←A.rotation.symm.norm_map ((factor P).adjoint v),A.reconstruct_adjoint]
  unfold MatrixSquareCoefficient.Data.factor VectorPhysicalFactor.factor
  rw [ContinuousLinearMap.adjoint_comp,(VectorWhiteCoordinates.analysis (d := d)).symm.adjoint_eq_symm,
    ←BoundedFieldOperator.operator_adjoint]
  exact (VectorWhiteCoordinates.analysis (d := d)).norm_map _

theorem norm (A : MatrixSquareCoefficient.Data P) (τ : ℝ) (x : HeatCircle) (i : d) :
    ‖MatrixPointHeatRows.row τ P x i‖=
      ‖BoundedFieldOperator.operator (BoundedFieldOperator.adjoint A.field) (VectorPointHeatTest.test τ x i)‖ := by
  rw [MatrixPointHeatRows.row_eq,feature_norm]

/-- A physical scalar-weighted component feature is controlled by the
original-square coefficient energy without any global coefficient cap. -/
theorem feature_bound (A : MatrixSquareCoefficient.Data P)
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) (u : Physical (d := d))
    (hA : A.value=ᵐ[ν] fun y => G (u y)) (v : Physical (d := d)) (k : AddCircle (1 : ℝ) → ℝ) (i : d)
    (hk : v=ᵐ[ν] fun y => k y • EuclideanSpace.single i (1 : ℝ)) :
    ENNReal.ofReal (‖(factor P).adjoint v‖^2) ≤ ∫⁻ y,ENNReal.ofReal ((k y)^2*‖G (u y)‖^2) ∂ν := by
  rw [feature_norm A v,←HolderWeightedEnergy.state_mass]
  apply lintegral_mono_ae
  filter_upwards [BoundedFieldOperator.operator_ae (BoundedFieldOperator.adjoint A.field) v,hk,hA] with y ho ht ha
  rw [ho,ht]
  change ENNReal.ofReal (‖(Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (A.value y)).adjoint
    (k y • EuclideanSpace.single i (1 : ℝ))‖^2) ≤ _
  rw [map_smul,ha,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (MatrixDiffusionRows.norm_le i (G (u y))) 2) (sq_nonneg _)

theorem bound (A : MatrixSquareCoefficient.Data P)
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) (u : Physical (d := d))
    (hA : A.value=ᵐ[ν] fun y => G (u y)) (τ : ℝ) (x : HeatCircle) (i : d) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row τ P x i‖^2) ≤
      ∫⁻ y,ENNReal.ofReal ((RealCausalHeatKernel.value x τ
        (CircleNormalization.scale 1 (2*Real.pi) y))^2*‖G (u y)‖^2) ∂ν := by
  rw [MatrixPointHeatRows.row_eq]
  exact feature_bound A G u hA _ _ i (MatrixPointRowDomination.test_ae τ x i)

/-- The identical coefficient energy controls time-space row increments.
All matrix orientations and the original coupled noise are retained. -/
theorem difference_bound (A : MatrixSquareCoefficient.Data P)
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) (u : Physical (d := d))
    (hA : A.value=ᵐ[ν] fun y => G (u y)) (τ σ : ℝ) (x z : HeatCircle) (i : d) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row τ P x i-MatrixPointHeatRows.row σ P z i‖^2) ≤
      ∫⁻ y,ENNReal.ofReal ((RealCausalHeatKernel.value x τ (CircleNormalization.scale 1 (2*Real.pi) y)-
        RealCausalHeatKernel.value z σ (CircleNormalization.scale 1 (2*Real.pi) y))^2*‖G (u y)‖^2) ∂ν := by
  rw [MatrixPointHeatRows.row_eq,MatrixPointHeatRows.row_eq,←map_sub]
  apply feature_bound A G u hA _ _ i
  filter_upwards [Lp.coeFn_sub (VectorPointHeatTest.test τ x i) (VectorPointHeatTest.test σ z i),
    MatrixPointRowDomination.test_ae τ x i,MatrixPointRowDomination.test_ae σ z i] with y hs hx hz
  rw [hs]
  change VectorPointHeatTest.test τ x i y-VectorPointHeatTest.test σ z i y=_
  rw [hx,hz,sub_smul]

/-- The two circle normalizations are inverse as literal point maps. -/
theorem scale_inverse (z : HeatCircle) :
    CircleNormalization.scale 1 (2*Real.pi) (CircleNormalization.scale (2*Real.pi) 1 z)=z := by
  induction z using Quotient.inductionOn with
  | _ r =>
    simp only [CircleNormalization.scale,AddCircle.equivAddCircle_apply_mk]
    congr 1
    field_simp

variable {n : ℕ} {P : Profile (Fin n)}

/-- The same bound in the native heat circle retains normalized Haar
measure exactly and uses the true rescaled original L2 state. -/
theorem native_bound (A : MatrixSquareCoefficient.Data P)
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) (u : Physical (d := Fin n))
    (hA : A.value=ᵐ[ν] fun y => G (u y)) (τ : ℝ) (x : HeatCircle) (i : Fin n) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row τ P x i‖^2) ≤
      ∫⁻ y : HeatCircle,ENNReal.ofReal ((RealCausalHeatKernel.value x τ y)^2*
        ‖G (VectorNativeHeatEndpoint.push u y)‖^2) ∂AddCircle.haarAddCircle := by
  apply (bound A G u hA τ x i).trans_eq
  rw [←(CircleNormalization.scale_measurePreserving (2*Real.pi) 1).lintegral_comp_emb
    (CircleNormalization.scaleMeasurableEquiv (2*Real.pi) 1).measurableEmbedding]
  apply lintegral_congr_ae
  filter_upwards [VectorNativeHeatEndpoint.push_ae u] with y hy
  rw [hy,scale_inverse]

/-- Exact normalized-circle version of the genuine matrix row increment
bound, usable with the existing sublinear scalar heat increment theory. -/
theorem native_difference_bound (A : MatrixSquareCoefficient.Data P)
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) (u : Physical (d := Fin n))
    (hA : A.value=ᵐ[ν] fun y => G (u y)) (τ σ : ℝ) (x z : HeatCircle) (i : Fin n) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row τ P x i-MatrixPointHeatRows.row σ P z i‖^2) ≤
      ∫⁻ y : HeatCircle,ENNReal.ofReal ((RealCausalHeatKernel.value x τ y-RealCausalHeatKernel.value z σ y)^2*
        ‖G (VectorNativeHeatEndpoint.push u y)‖^2) ∂AddCircle.haarAddCircle := by
  apply (difference_bound A G u hA τ σ x z i).trans_eq
  rw [←(CircleNormalization.scale_measurePreserving (2*Real.pi) 1).lintegral_comp_emb
    (CircleNormalization.scaleMeasurableEquiv (2*Real.pi) 1).measurableEmbedding]
  apply lintegral_congr_ae
  filter_upwards [VectorNativeHeatEndpoint.push_ae u] with y hy
  rw [hy,scale_inverse]

end SHEStochastic.MatrixPointSquareEnergy
