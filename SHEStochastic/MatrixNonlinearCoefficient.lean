module

public import SHEStochastic.NativeMatrixCoefficient
public import SHEStochastic.MatrixSelfAdjointNormBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixNonlinearCoefficient
open MeasureTheory Matrix MatrixInfiniteHaar MatrixSquareCoefficient
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The original bounded uniformly elliptic square diffusion. Its
matrix covariance and Haar profiles are constructed below. -/
structure Coefficient (d : Type*) [Fintype d] [DecidableEq d] where
  value : EuclideanSpace ℝ d → Matrix d d ℝ
  measurable : Measurable value
  bound : ℝ≥0
  norm_bound : ∀ z, ‖value z‖ ≤ bound
  lower : ℝ
  lower_pos : 0 < lower
  lower_bound : ∀ z, lower • (1 : Matrix d d ℝ) ≤ value z * (value z)ᴴ

namespace Coefficient
variable (G : Coefficient d)

def covariance (z : EuclideanSpace ℝ d) : Matrix d d ℝ := G.value z * (G.value z)ᴴ

theorem covariance_measurable : Measurable G.covariance :=
  G.measurable.mul (continuous_star.measurable.comp G.measurable)

theorem covariance_bound (z : EuclideanSpace ℝ d) : ‖G.covariance z‖ ≤ (G.bound : ℝ) ^ 2 := by
  change ‖G.value z * star (G.value z)‖ ≤ _
  calc
    _ ≤ ‖G.value z‖ * ‖star (G.value z)‖ := norm_mul_le _ _
    _ = ‖G.value z‖ ^ 2 := by rw [norm_star, pow_two]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (G.norm_bound z) 2

theorem covariance_upper (z : EuclideanSpace ℝ d) :
    G.covariance z ≤ ((G.bound : ℝ) ^ 2 + 1) • (1 : Matrix d d ℝ) := by
  have hherm : (G.covariance z).IsHermitian := by
    change IsSelfAdjoint (G.value z * star (G.value z))
    exact IsSelfAdjoint.mul_star_self _
  exact (MatrixSelfAdjointNormBounds.bound _ hherm).2.trans
    (smul_le_smul_of_nonneg_right ((G.covariance_bound z).trans (le_add_of_nonneg_right zero_le_one)) zero_le_one)

theorem covariance_difference (z w : EuclideanSpace ℝ d) :
    ‖G.covariance z - G.covariance w‖ ≤ 2 * (G.bound : ℝ) * ‖G.value z - G.value w‖ := by
  have he : G.covariance z - G.covariance w =
      (G.value z - G.value w) * star (G.value z) +
        G.value w * star (G.value z - G.value w) := by
    change G.value z * star (G.value z) - G.value w * star (G.value w) = _
    rw [star_sub, sub_mul, mul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(G.value z - G.value w) * star (G.value z)‖ +
        ‖G.value w * star (G.value z - G.value w)‖ := norm_add_le _ _
    _ ≤ ‖G.value z - G.value w‖ * ‖G.value z‖ +
        ‖G.value w‖ * ‖G.value z - G.value w‖ := by
      simpa only [norm_star] using add_le_add
        (norm_mul_le (G.value z - G.value w) (star (G.value z)))
        (norm_mul_le (G.value w) (star (G.value z - G.value w)))
    _ ≤ _ := by nlinarith only [G.norm_bound z, G.norm_bound w, norm_nonneg (G.value z - G.value w)]

theorem covariance_holder {β K : ℝ}
    (hG : ∀ z w, ‖G.value z - G.value w‖ ≤ K * ‖z-w‖ ^ β) (z w : EuclideanSpace ℝ d) :
    ‖G.covariance z - G.covariance w‖ ≤ (2 * (G.bound : ℝ) * K) * ‖z-w‖ ^ β := by
  exact (G.covariance_difference z w).trans
    ((mul_le_mul_of_nonneg_left (hG z w) (mul_nonneg (by norm_num) G.bound.coe_nonneg)).trans_eq (by ring))

def profile (u : AddCircle (1 : ℝ) → EuclideanSpace ℝ d) (hu : Measurable u) : Profile d where
  value x := G.covariance (u x)
  measurable := G.covariance_measurable.comp hu
  bound := G.bound ^ 2
  norm_bound := Filter.Eventually.of_forall fun x => by
    simpa only [NNReal.coe_pow] using G.covariance_bound (u x)
  lower := G.lower
  lower_pos := G.lower_pos
  lower_bound := Filter.Eventually.of_forall fun x => G.lower_bound (u x)
  upper := (G.bound : ℝ) ^ 2 + 1
  upper_pos := by positivity
  upper_bound := Filter.Eventually.of_forall fun x => G.covariance_upper (u x)

def data (u : AddCircle (1 : ℝ) → EuclideanSpace ℝ d) (hu : Measurable u) : Data (G.profile u hu) where
  value x := G.value (u x)
  measurable := G.measurable.comp hu
  bound := G.bound
  norm_bound := Filter.Eventually.of_forall fun x => G.norm_bound (u x)
  covariance_ae := Filter.Eventually.of_forall fun _ => rfl

variable {Z : Type*} [MeasurableSpace Z]

def family (u : Z × AddCircle (1 : ℝ) → EuclideanSpace ℝ d) (hu : Measurable u) (z : Z) : Profile d :=
  G.profile (fun x => u (z,x)) (hu.comp (measurable_const.prodMk measurable_id))

def dataFamily (u : Z × AddCircle (1 : ℝ) → EuclideanSpace ℝ d) (hu : Measurable u) (z : Z) :
    Data (G.family u hu z) :=
  G.data (fun x => u (z,x)) (hu.comp (measurable_const.prodMk measurable_id))

theorem family_measurable (u : Z × AddCircle (1 : ℝ) → EuclideanSpace ℝ d) (hu : Measurable u) :
    Measurable (fun z : Z × AddCircle (1 : ℝ) => (G.family u hu z.1).value z.2) :=
  G.covariance_measurable.comp hu

theorem dataFamily_measurable (u : Z × AddCircle (1 : ℝ) → EuclideanSpace ℝ d) (hu : Measurable u) :
    Measurable (fun z : Z × AddCircle (1 : ℝ) => (G.dataFamily u hu z.1).value z.2) :=
  G.measurable.comp hu

end Coefficient
end SHEStochastic.MatrixNonlinearCoefficient
