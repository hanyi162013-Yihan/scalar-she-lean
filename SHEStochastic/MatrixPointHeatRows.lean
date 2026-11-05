module

public import SHEStochastic.VectorPointHeatTest
public import SHEStochastic.MatrixHaarOperatorBounds
public import SHEStochastic.MatrixHaarHeatRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPointHeatRows
open MeasureTheory SHE SHE.FiniteHaar SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def row (τ : ℝ) (P : Profile d) (x : HeatCircle) (i : d) : Input (d := d) :=
  if 0 < τ then (factor P).adjoint (VectorPointHeatTest.test τ x i) else 0

theorem test_norm {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) (i : d) :
    ‖VectorPointHeatTest.test τ x i‖=‖circleHeat τ x‖ := by
  have he : ∀ᵐ y ∂μ, ‖VectorPointHeatTest.test τ x i y‖=‖ScalarHaarHeatRows.test τ x y‖ := by
    filter_upwards [(L2EuclideanCoordinates.injection i).coeFn_compLpL (ScalarHaarHeatRows.test τ x)] with y hy
    change ‖(L2EuclideanCoordinates.injection i).compLpL 2 μ (ScalarHaarHeatRows.test τ x) y‖=_
    rw [hy]
    simp [L2EuclideanCoordinates.injection,norm_smul,PiLp.norm_single]
  have hn : ‖VectorPointHeatTest.test τ x i‖=‖ScalarHaarHeatRows.test τ x‖ :=
    le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
      (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))
  have hs := congrArg norm (ScalarHaarHeatRows.embed_test hτ x)
  rw [realEmbed_norm_eq,LinearIsometryEquiv.norm_map] at hs
  exact hn.trans hs

/-- The actual full infinite Haar point rows have their literal matrix
heat covariance, including off-diagonal components and distinct centers. -/
theorem pairing {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (P : Profile d)
    (x z : HeatCircle) (i j : d) :
    inner ℝ (row τ P x i) (row σ P z j)=
      ∫ y, P.value y i j*
        (ProfileVariance.heatPhysical τ x (CircleNormalization.scale 1 (2*Real.pi) y)).re*
        (ProfileVariance.heatPhysical σ z (CircleNormalization.scale 1 (2*Real.pi) y)).re ∂μ := by
  rw [row,row,if_pos hτ,if_pos hσ,ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.comp_apply,covariance,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [VectorPointHeatTest.test_ae hτ x i,VectorPointHeatTest.test_ae hσ z j,
    MatrixFieldOperator.operator_ae P.value P.measurable P.bound P.norm_bound
      (VectorPointHeatTest.test σ z j)] with y ht hs hm
  change (multiplier P (VectorPointHeatTest.test σ z j) y).ofLp = _ at hm
  rw [ht]
  simp only [L2EuclideanCoordinates.injection,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,real_inner_smul_left,EuclideanSpace.inner_single_left,conj_trivial,one_mul]
  have he := congrFun hm i
  rw [hs] at he
  simp only [L2EuclideanCoordinates.injection,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,
    dotProduct,PiLp.single_apply,ite_mul,mul_ite,mul_zero,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_one] at he
  rw [he]
  ring

theorem norm_sq {τ : ℝ} (hτ : 0 < τ) (P : Profile d) (x : HeatCircle) (i : d) :
    ‖row τ P x i‖^2 ≤ P.upper*(1+heatConstant*τ^(-(1/2 : ℝ))) := by
  rw [row,if_pos hτ]
  have he := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (factor P).adjoint
    (VectorPointHeatTest.test τ x i)
  rw [ContinuousLinearMap.adjoint_adjoint,covariance] at he
  rw [he]
  exact (bounded P _).trans (mul_le_mul_of_nonneg_left
    (by rw [test_norm hτ]; exact circleHeat_norm_sq_bound hτ x) P.upper_pos.le)

theorem pairing_native {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (P : Profile d)
    (κ : HeatCircle → Matrix d d ℝ)
    (hκ : ∀ y, P.value y=κ (CircleNormalization.scale 1 (2*Real.pi) y))
    (x z : HeatCircle) (i j : d) :
    inner ℝ (row τ P x i) (row σ P z j)=
      ∫ y, κ y i j*(ProfileVariance.heatPhysical τ x y).re*
        (ProfileVariance.heatPhysical σ z y).re ∂AddCircle.haarAddCircle := by
  rw [pairing hτ hσ]
  simp_rw [hκ]
  exact (CircleNormalization.scale_measurePreserving 1 (2*Real.pi)).integral_comp
    (CircleNormalization.scaleMeasurableEquiv 1 (2*Real.pi)).measurableEmbedding
    (fun y => κ y i j*(ProfileVariance.heatPhysical τ x y).re*
      (ProfileVariance.heatPhysical σ z y).re)

theorem row_eq (τ : ℝ) (P : Profile d) (x : HeatCircle) (i : d) :
    row τ P x i=(factor P).adjoint (VectorPointHeatTest.test τ x i) := by
  by_cases ht : 0 < τ
  · simp only [row,if_pos ht]
  · simp only [row,if_neg ht,VectorPointHeatTest.zero (not_lt.mp ht),map_zero]

theorem measurable {Z : Type*} [MeasurableSpace Z] (τ : Z → ℝ) (hτ : Measurable τ)
    (x : Z → HeatCircle) (hx : Measurable x) (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2)) (i : d) :
    @Measurable Z (Input (d := d)) _ (borel _) (fun z => row (τ z) (Q z) (x z) i) := by
  have hp : Measurable (fun z : Z => (τ z,x z)) := hτ.prodMk hx
  have hu := Measurable.comp
    (g := fun p : ℝ × HeatCircle => VectorPointHeatTest.test p.1 p.2 i)
    (f := fun z : Z => (τ z,x z)) (VectorPointHeatTest.measurable i) hp
  have he : (fun z => row (τ z) (Q z) (x z) i)=
      (fun z => (factor (Q z)).adjoint (VectorPointHeatTest.test (τ z) (x z) i)) :=
    funext (fun z => row_eq (τ z) (Q z) (x z) i)
  rw [he]
  exact MatrixHaarHeatRows.measurable Q hQ (fun z : Z => VectorPointHeatTest.test (τ z) (x z) i) hu

end SHEStochastic.MatrixPointHeatRows
