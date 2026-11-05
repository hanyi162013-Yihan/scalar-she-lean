module

public import SHEStochastic.HeatCovarianceMeasure
public import SHEStochastic.MatrixSelfAdjointNormBounds
public import Mathlib.Analysis.Matrix.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHeatCovariance
open MeasureTheory Set SHE SHE.ProfileVariance HeatCovarianceMeasure
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
abbrev SpatialCircle := HeatCovarianceMeasure.Circle
abbrev Domain := ℝ × SpatialCircle

/-- Full matrix point covariance of the heat convolution. The positive
heat-square measure reuses the scalar time/space integrability estimates. -/
def covariance (κ : Domain → Matrix d d ℝ) (p : Window × SpatialCircle) : Matrix d d ℝ :=
  ∫ z, κ z ∂HeatCovarianceMeasure.measure p.1 p.2

theorem integrable (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M : ℝ)
    (hM : ∀ z, ‖κ z‖ ≤ M) (p : Window × SpatialCircle) :
    Integrable κ (HeatCovarianceMeasure.measure p.1 p.2) :=
  Integrable.of_bound hκ.aestronglyMeasurable M (Filter.Eventually.of_forall hM)

def entry (i j : d) : Matrix d d ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun A := A i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

theorem entry_formula (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M : ℝ)
    (hM : ∀ z, ‖κ z‖ ≤ M) (p : Window × SpatialCircle) (i j : d) :
    covariance κ p i j = positiveVarianceMap (fun z => κ z i j) (p.1.val,p.2) := by
  have he : covariance κ p i j = ∫ z, κ z i j ∂HeatCovarianceMeasure.measure p.1 p.2 :=
    ((entry i j).integral_comp_comm (integrable κ hκ M hM p)).symm
  rw [he, positiveVarianceMap_eq p.1.property.1.le]
  apply HeatCovarianceMeasure.scalar_integral p.1 p.2 _ ((entry i j).continuous.measurable.comp hκ)
    (‖entry i j‖*M)
  intro z
  exact ((entry i j).le_opNorm (κ z)).trans
    (mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _))

theorem measurable (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M : ℝ)
    (hM : ∀ z, ‖κ z‖ ≤ M) : Measurable (covariance κ) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hij : Measurable (fun z => κ z i j) := (entry i j).continuous.measurable.comp hκ
  have hi := positiveVarianceMap_measurable hij
  have hp : Measurable (fun p : Window × SpatialCircle => (p.1.val,p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have he : (fun p : Window × SpatialCircle => covariance κ p i j) =
      (fun p => positiveVarianceMap (fun z => κ z i j) (p.1.val,p.2)) :=
    funext (fun p => entry_formula κ hκ M hM p i j)
  rw [he]
  exact hi.comp hp

theorem norm_bound (κ : Domain → Matrix d d ℝ) (M : ℝ)
    (hM : ∀ z, ‖κ z‖ ≤ M) (p : Window × SpatialCircle) :
    ‖covariance κ p‖ ≤ M*(HeatCovarianceMeasure.measure p.1 p.2).real univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hM)

theorem small_bound (κ : Domain → Matrix d d ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ z, ‖κ z‖ ≤ M) (p : Window × SpatialCircle) :
    ‖covariance κ p‖ ≤ upperConstant*M*p.1.val^(1/2 : ℝ) := by
  exact (norm_bound κ M hM p).trans
    ((mul_le_mul_of_nonneg_left (HeatCovarianceMeasure.mass_bounds p.1 p.2).2 hM0).trans_eq (by ring))

/-- The concrete matrix covariance map is O(sqrt t) Lipschitz in the
uniform matrix norm. No scalar diagonal reduction loses cross entries. -/
theorem difference (κ η : Domain → Matrix d d ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (M D : ℝ) (hD : 0 ≤ D) (hκM : ∀ z, ‖κ z‖ ≤ M) (hηM : ∀ z, ‖η z‖ ≤ M)
    (hDiff : ∀ z, ‖κ z-η z‖ ≤ D) (p : Window × SpatialCircle) :
    ‖covariance κ p-covariance η p‖ ≤ upperConstant*D*p.1.val^(1/2 : ℝ) := by
  change ‖(∫ z, κ z ∂HeatCovarianceMeasure.measure p.1 p.2)-
    (∫ z, η z ∂HeatCovarianceMeasure.measure p.1 p.2)‖ ≤ _
  rw [← integral_sub (integrable κ hκ M hκM p) (integrable η hη M hηM p)]
  exact small_bound (fun z => κ z-η z) D hD hDiff p

theorem elliptic (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M ell U : ℝ)
    (hM : ∀ z, ‖κ z‖ ≤ M)
    (hLo : ∀ z, ell • (1 : Matrix d d ℝ) ≤ κ z)
    (hHi : ∀ z, κ z ≤ U • (1 : Matrix d d ℝ)) (p : Window × SpatialCircle) :
    ((HeatCovarianceMeasure.measure p.1 p.2).real univ*ell) • (1 : Matrix d d ℝ) ≤ covariance κ p ∧
      covariance κ p ≤ ((HeatCovarianceMeasure.measure p.1 p.2).real univ*U) • (1 : Matrix d d ℝ) := by
  constructor
  · have hh := integral_mono_ae (integrable_const (ell • (1 : Matrix d d ℝ)))
      (integrable κ hκ M hM p) (Filter.Eventually.of_forall hLo)
    rw [Matrix.le_iff] at hh
    change (covariance κ p-((HeatCovarianceMeasure.measure p.1 p.2).real univ*ell) • (1 : Matrix d d ℝ)).PosSemidef
    convert! hh using 1 <;> simp only [covariance, integral_const, smul_smul]
  · have hh := integral_mono_ae (integrable κ hκ M hM p)
      (integrable_const (U • (1 : Matrix d d ℝ))) (Filter.Eventually.of_forall hHi)
    rw [Matrix.le_iff] at hh
    change (((HeatCovarianceMeasure.measure p.1 p.2).real univ*U) • (1 : Matrix d d ℝ)-covariance κ p).PosSemidef
    convert! hh using 1 <;> simp only [covariance, integral_const, smul_smul]

theorem lower_bound (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M ell U : ℝ)
    (hell : 0 ≤ ell) (hM : ∀ z, ‖κ z‖ ≤ M)
    (hLo : ∀ z, ell • (1 : Matrix d d ℝ) ≤ κ z)
    (hHi : ∀ z, κ z ≤ U • (1 : Matrix d d ℝ)) (p : Window × SpatialCircle) :
    (lowerConstant*ell*p.1.val^(1/2 : ℝ)) • (1 : Matrix d d ℝ) ≤ covariance κ p := by
  apply le_trans _ (elliptic κ hκ M ell U hM hLo hHi p).1
  apply smul_le_smul_of_nonneg_right _ zero_le_one
  have hh := mul_le_mul_of_nonneg_right (HeatCovarianceMeasure.mass_bounds p.1 p.2).1 hell
  convert! hh using 1 <;> ring

theorem positive (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M ell U : ℝ)
    (hell : 0 < ell) (hM : ∀ z, ‖κ z‖ ≤ M)
    (hLo : ∀ z, ell • (1 : Matrix d d ℝ) ≤ κ z)
    (hHi : ∀ z, κ z ≤ U • (1 : Matrix d d ℝ)) (p : Window × SpatialCircle) :
    (covariance κ p).PosDef := by
  have hp : 0 < lowerConstant*ell*p.1.val^(1/2 : ℝ) :=
    mul_pos (mul_pos lowerConstant_pos hell) (Real.rpow_pos_of_pos p.1.property.1 _)
  have hd : (covariance κ p-(lowerConstant*ell*p.1.val^(1/2 : ℝ)) • (1 : Matrix d d ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (sub_nonneg.mpr (lower_bound κ hκ M ell U hell.le hM hLo hHi p))
  convert (Matrix.PosDef.one.smul hp).add_posSemidef hd using 1
  abel

end SHEStochastic.MatrixHeatCovariance
