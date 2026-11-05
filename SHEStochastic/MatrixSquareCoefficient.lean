module

public import SHEStochastic.MatrixHaarNoiseRotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixSquareCoefficient
open MeasureTheory Matrix MatrixInfiniteHaar SHE
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- A concrete bounded square matrix coefficient with prescribed elliptic
covariance. Completeness, inverse bounds, and stochastic transport are
consequences, not fields of these data. -/
structure Data (P : Profile d) where
  value : AddCircle (1 : ℝ) → Matrix d d ℝ
  measurable : Measurable value
  bound : ℝ≥0
  norm_bound : ∀ᵐ x ∂μ, ‖value x‖ ≤ bound
  covariance_ae : ∀ᵐ x ∂μ, value x * (value x)ᴴ = P.value x

namespace Data
variable {P : Profile d} (A : Data P)

/-- A measurable coefficient with the prescribed bounded covariance
automatically has a uniform norm bound; this avoids repeating square-root
energy arguments for each new concrete noise representation. -/
def ofCovariance (P : Profile d) (G : AddCircle (1 : ℝ) → Matrix d d ℝ) (hG : Measurable G)
    (hCov : ∀ᵐ x ∂μ, G x*(G x)ᴴ=P.value x) : Data P where
  value := G
  measurable := hG
  bound := NNReal.sqrt P.bound
  norm_bound := by
    filter_upwards [hCov,P.norm_bound] with x hx hb
    have he : ‖G x‖^2=‖G x*(G x)ᴴ‖ := by
      have hh := Matrix.l2_opNorm_conjTranspose_mul_self ((G x)ᴴ)
      simpa only [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose,pow_two] using hh.symm
    have hs : ((NNReal.sqrt P.bound : ℝ))^2=(P.bound : ℝ) := by
      exact_mod_cast NNReal.sq_sqrt P.bound
    apply (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).mp
    rw [he,hx,hs]
    exact hb
  covariance_ae := hCov

def field : VectorPhysicalFactor.Coefficient (d := d) :=
  MatrixFieldOperator.field A.value A.measurable A.bound A.norm_bound

def factor : Input (d := d) →L[ℝ] Physical (d := d) := VectorPhysicalFactor.factor A.field

theorem covariance : A.factor.comp A.factor.adjoint = multiplier P := by
  rw [factor, VectorPhysicalFactor.covariance]
  apply BoundedFieldOperator.operator_congr
  filter_upwards [A.covariance_ae] with x hx
  change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (A.value x)) *
    star (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (A.value x)) =
      Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (P.value x)
  rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, hx]

theorem pointwise_isUnit : ∀ᵐ x ∂μ, IsUnit (A.value x) := by
  filter_upwards [A.covariance_ae, P.lower_bound] with x hx hlo
  have hDiff : (P.value x - P.lower • (1 : Matrix d d ℝ)).PosSemidef :=
    (sub_nonneg.mpr hlo).posSemidef
  have hp : (P.value x).PosDef := by
    convert (Matrix.PosDef.one.smul P.lower_pos).add_posSemidef hDiff using 1
    abel
  have hd : IsUnit (A.value x).det := by
    have hh : IsUnit ((A.value x).det * ((A.value x)ᴴ).det) := by
      rw [← Matrix.det_mul, hx]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
    exact isUnit_of_mul_isUnit_left hh
  exact (Matrix.isUnit_iff_isUnit_det _).mpr hd

theorem operator_injective : Function.Injective (BoundedFieldOperator.operator A.field) := by
  intro u v huv
  apply Lp.ext
  filter_upwards [MatrixFieldOperator.operator_ae A.value A.measurable A.bound A.norm_bound u,
    MatrixFieldOperator.operator_ae A.value A.measurable A.bound A.norm_bound v,
    A.pointwise_isUnit] with x hu hv hx
  apply WithLp.ofLp_injective
  apply Matrix.mulVec_injective_of_isUnit hx
  exact hu.symm.trans ((congrArg (fun f : Physical (d := d) => (f x).ofLp) huv).trans hv)

theorem bijective : Function.Bijective A.factor := by
  constructor
  · exact A.operator_injective.comp VectorWhiteCoordinates.analysis.symm.injective
  · exact SynthesisEquivalence.surjective_of_covariance A.factor (MatrixHaarCovarianceInverse.equivalence P) A.covariance

def equivalence : Input (d := d) ≃L[ℝ] Physical (d := d) :=
  ContinuousLinearEquiv.ofBijective A.factor
    (LinearMap.ker_eq_bot.mpr A.bijective.1) (LinearMap.range_eq_top.mpr A.bijective.2)

/-- Every concrete bounded square factor of the same elliptic covariance
differs from the completed infinite Haar factor by a genuine unitary. -/
def rotation : Input (d := d) ≃ₗᵢ[ℝ] Input (d := d) :=
  SynthesisEquivalence.comparison (MatrixInfiniteHaar.equivalence P) A.equivalence
    ((MatrixInfiniteHaar.covariance P).trans A.covariance.symm)

theorem reconstruct (z : Input (d := d)) : MatrixInfiniteHaar.factor P (A.rotation z) = A.factor z := by
  change MatrixInfiniteHaar.equivalence P ((MatrixInfiniteHaar.equivalence P).symm (A.equivalence z)) = A.equivalence z
  exact (MatrixInfiniteHaar.equivalence P).apply_symm_apply _

theorem rotation_eq (z : Input (d := d)) :
    A.rotation z = (MatrixInfiniteHaar.synthesis P).adjoint (A.factor z) := rfl

theorem reconstruct_adjoint (u : Physical (d := d)) :
    A.rotation.symm ((MatrixInfiniteHaar.factor P).adjoint u) = A.factor.adjoint u := by
  let J := A.rotation.toContinuousLinearEquiv.toContinuousLinearMap
  have hh : (MatrixInfiniteHaar.factor P).comp J = A.factor := by
    apply ContinuousLinearMap.ext
    intro z
    exact A.reconstruct z
  have ha := congrArg (fun K : Input (d := d) →L[ℝ] Physical (d := d) => K.adjoint) hh
  rw [ContinuousLinearMap.adjoint_comp,
    show J.adjoint = A.rotation.symm.toContinuousLinearEquiv.toContinuousLinearMap from A.rotation.adjoint_eq_symm] at ha
  exact congrArg (fun K : Physical (d := d) →L[ℝ] Input (d := d) => K u) ha

end Data
end SHEStochastic.MatrixSquareCoefficient
