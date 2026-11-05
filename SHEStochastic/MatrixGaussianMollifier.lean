module

public import SHEStochastic.MatrixGaussianAverage
public import SHEStochastic.MatrixProfileHilbert
public import SHEStochastic.IsotropicGaussianHolder
public import SHEStochastic.MatrixHeatCovariance
public import SHEStochastic.MatrixOrthogonalField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixGaussianMollifier
open MeasureTheory ProbabilityTheory SHE SHE.GaussianRangeSmooth MatrixNonlinearCoefficient
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff
variable {n : ℕ} (G : Coefficient (Fin n))

/-- Smooth the full covariance by a genuine isotropic vector Gaussian.
This preserves the same lower ellipticity constant at every scale. -/
def covariance (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  MatrixGaussianAverage.average G (IsotropicGaussianHolder.matrix ε) z

theorem measurable (ε : ℝ) : Measurable (covariance G ε) := by
  have hp : Measurable (fun z : EuclideanSpace ℝ (Fin n) => (IsotropicGaussianHolder.matrix (n := n) ε,z)) :=
    measurable_const.prodMk measurable_id
  exact Measurable.comp
    (g := fun p : Matrix (Fin n) (Fin n) ℝ × EuclideanSpace ℝ (Fin n) => MatrixGaussianAverage.average G p.1 p.2)
    (f := fun z : EuclideanSpace ℝ (Fin n) => (IsotropicGaussianHolder.matrix (n := n) ε,z))
    (MatrixGaussianAverage.measurable G) hp

theorem norm_bound (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ‖covariance G ε z‖ ≤ (G.bound : ℝ)^2 :=
  MatrixGaussianAverage.norm_bound G _ z

theorem elliptic (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    G.lower • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ covariance G ε z ∧
      covariance G ε z ≤ ((G.bound : ℝ)^2+1) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
  MatrixGaussianAverage.elliptic G _ z

theorem nonnegative (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ covariance G ε z :=
  (smul_nonneg G.lower_pos.le zero_le_one).trans (elliptic G ε z).1

theorem positive (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) : (covariance G ε z).PosDef := by
  have hs : (covariance G ε z-G.lower • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (elliptic G ε z).1)
  convert (Matrix.PosDef.one.smul G.lower_pos).add_posSemidef hs using 1
  abel

theorem entry {ε : ℝ} (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    covariance G ε z i j=roughAverageExtension (IsotropicGaussianHolder.matrix ε)
      (fun y => G.covariance y i j) z := by
  change MatrixHeatCovariance.entry i j
    (∫ y, G.covariance (z+y) ∂multivariateGaussian 0 (IsotropicGaussianHolder.matrix ε))=_
  rw [← (MatrixHeatCovariance.entry i j).integral_comp_comm
    (MatrixGaussianAverage.integrable G (IsotropicGaussianHolder.matrix ε) z)]
  exact (extension_eq_average_on_range (IsotropicGaussianHolder.matrix (n := n) ε)
    (fun y => G.covariance y i j) (z := z)
    (by rw [IsotropicGaussianHolder.range_top (n := n) hε.ne']; trivial)).symm

/-- Full matrix smoothness follows from the existing scalar range
smoother through fixed finite Hilbert coordinates. -/
theorem smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (covariance G ε) := by
  apply contDiff_infty.mpr
  intro k
  have hs : ContDiff ℝ k (fun z : EuclideanSpace ℝ (Fin n) =>
      fun p : Fin n × Fin n => covariance G ε z p.1 p.2) := by
    apply contDiff_pi.mpr
    intro p
    have he : (fun z => covariance G ε z p.1 p.2)=
        roughAverageExtension (IsotropicGaussianHolder.matrix ε) (fun y => G.covariance y p.1 p.2) :=
      funext (fun z => entry G hε z p.1 p.2)
    rw [he]
    apply contDiff_roughAverageExtension (IsotropicGaussianHolder.nonnegative hε.le)
      _ ((MatrixHeatCovariance.entry p.1 p.2).continuous.measurable.comp G.covariance_measurable)
      (‖MatrixHeatCovariance.entry p.1 p.2‖*(G.bound : ℝ)^2) _ k
    intro z
    exact ((MatrixHeatCovariance.entry p.1 p.2).le_opNorm (G.covariance z)).trans
      (mul_le_mul_of_nonneg_left (G.covariance_bound z) (norm_nonneg _))
  have hh := (MatrixProfileHilbert.toMatrix (Fin n)).contDiff.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin n => ℝ)).symm.contDiff.comp hs)
  convert hh using 1
  funext z
  rfl

theorem holder {K β : ℝ} (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (ε : ℝ) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖covariance G ε z-covariance G ε w‖ ≤ (2*(G.bound : ℝ)*K)*‖z-w‖^β :=
  MatrixGaussianAverage.mean_holder G hG _ z w

theorem lipschitz {ε K β : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖covariance G ε z-covariance G ε w‖ ≤
      ((2*(G.bound : ℝ)*K)*GaussianNormMoment.moment (Fin n) (β+1)*ε^((β-1)/2))*‖z-w‖ :=
  MatrixGaussianAverage.mean_lipschitz G hε hK hβ hG _ le_rfl z w

theorem error {ε K β : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (z : EuclideanSpace ℝ (Fin n)) :
    ‖covariance G ε z-G.covariance z‖ ≤
      (2*(G.bound : ℝ)*K)*ε^(β/2)*GaussianNormMoment.moment (Fin n) β := by
  apply MatrixGaussianAverage.displacement G hK hβ hG _
    (IsotropicGaussianHolder.nonnegative hε).nonneg hε _ z
  change ‖ε • (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ ε
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hε]
  have hI : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 :=
    MatrixOrthogonalField.matrix_norm _ (by simp)
  exact (mul_le_mul_of_nonneg_left hI hε).trans_eq (mul_one ε)

end SHEStochastic.MatrixGaussianMollifier
