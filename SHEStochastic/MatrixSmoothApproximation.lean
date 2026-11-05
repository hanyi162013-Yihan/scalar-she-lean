module

public import SHEStochastic.MatrixSmoothCoefficient
public import SHEStochastic.MatrixFixedHorizonPicard
public import SHEStochastic.MatrixPhysicalProfile
public import SHE.CompactMollifier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixSmoothApproximation
open MeasureTheory Filter SHE SHE.FiniteHaar MatrixNonlinearCoefficient MatrixCanonicalProfile
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator Topology ContDiff
variable {n : ℕ} (G : Coefficient (Fin n)) {K β : ℝ}

/-- Reuse the scalar construction's deterministic scale sequence. -/
def coefficient (m : ℕ) : Coefficient (Fin n) :=
  MatrixSmoothCoefficient.coefficient G (CompactMollifier.radius m)

def holderConstant (K : ℝ) : ℝ := MatrixSmoothCoefficient.sqrtConstant G*(2*(G.bound : ℝ)*K)

theorem holderConstant_nonneg (hK : 0 ≤ K) : 0 ≤ holderConstant G K :=
  mul_nonneg (MatrixSmoothCoefficient.sqrtConstant_nonneg G)
    (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)

theorem smooth (m : ℕ) : ContDiff ℝ ∞ (coefficient G m).value :=
  MatrixSmoothCoefficient.smooth G (CompactMollifier.radius_pos m)

theorem holder (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (m : ℕ) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G m).value z-(coefficient G m).value w‖ ≤ holderConstant G K*‖z-w‖^β :=
  MatrixSmoothCoefficient.holder G hG _ z w

def lipschitzConstant (K β : ℝ) (m : ℕ) : ℝ :=
  MatrixSmoothCoefficient.sqrtConstant G*((2*(G.bound : ℝ)*K)*
    GaussianNormMoment.moment (Fin n) (β+1)*CompactMollifier.radius m^((β-1)/2))

theorem lipschitzConstant_nonneg (hK : 0 ≤ K) (β : ℝ) (m : ℕ) :
    0 ≤ lipschitzConstant G K β m :=
  mul_nonneg (MatrixSmoothCoefficient.sqrtConstant_nonneg G)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)
      (GaussianNormMoment.nonneg _)) (Real.rpow_nonneg (CompactMollifier.radius_pos m).le _))

theorem lipschitz (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (m : ℕ) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G m).value z-(coefficient G m).value w‖ ≤
      lipschitzConstant G K β m*‖z-w‖ :=
  MatrixSmoothCoefficient.lipschitz G (CompactMollifier.radius_pos m) hK hβ hG z w

theorem uniform_limit (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) :
    TendstoUniformly (fun m => (coefficient G m).value) (fun z => CFC.sqrt (G.covariance z)) atTop := by
  have ht : Tendsto (fun m => MatrixSmoothCoefficient.sqrtConstant G*
      ((2*(G.bound : ℝ)*K)*CompactMollifier.radius m^(β/2)*GaussianNormMoment.moment (Fin n) β))
      atTop (𝓝 (0 : ℝ)) := by
    have he := ((CompactMollifier.radius_tendsto.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ β/2))).const_mul
      (2*(G.bound : ℝ)*K)).mul_const (GaussianNormMoment.moment (Fin n) β)
    simpa only [Real.zero_rpow (by positivity : β/2 ≠ 0),mul_zero,zero_mul] using
      he.const_mul (MatrixSmoothCoefficient.sqrtConstant G)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with m hm z
  rw [dist_eq_norm,norm_sub_rev]
  unfold coefficient
  exact (MatrixSmoothCoefficient.error G (CompactMollifier.radius_pos m).le hK hβ.le hG z).trans_lt hm

/-- All smooth approximants have a common coupled Gaussian profile
horizon and common one-input stability constants. Their Lipschitz
constants do not enter this choice. -/
theorem exists_common_parameters (hK : 0 ≤ K) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) :
    ∃ P : ∀ m : ℕ, Parameters (coefficient G m), ∀ m,
      (P m).holder=holderConstant G K ∧ (P m).exponent=β ∧ (P m).horizon=(P 0).horizon ∧
      MatrixProfileStability.memoryConstant (coefficient G m) (P m).holder (P m).exponent*
        ProfileVolterra.powerConstant (((P m).exponent-1)/4)*(P m).horizon^((P m).exponent/4) ≤ 1/2 := by
  obtain ⟨P,hPK,hPβ,hs⟩ := MatrixPhysicalProfile.exists_parameters (coefficient G 0)
    (holderConstant_nonneg G hK) hβ hβ1 (holder G hG 0)
  have hc := P.small
  rw [hPK,hPβ] at hc hs
  let Q (m : ℕ) : Parameters (coefficient G m) :=
    ⟨holderConstant G K,β,P.horizon,holderConstant_nonneg G hK,hβ,hβ1,P.horizon_pos,
      P.horizon_le_one,holder G hG m,hc⟩
  exact ⟨Q,fun m => ⟨rfl,rfl,rfl,hs⟩⟩

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {Ω : Type*} [MeasurableSpace Ω] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- Every smooth approximant has a unique native predictable mild
fixed point on the same prescribed physical time interval. -/
theorem exists_unique_heat_mild (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (hH : (H : ℝ) ≤ 1) (N : FiniteScalarIto.Family F μ H (Fin n × HaarNode))
    (u : MatrixInfiniteHaar.Physical (d := Fin n)) (m : ℕ) :
    ∃! v : PredictableL2.Process (E := MatrixInfiniteHaar.Physical (d := Fin n)) F μ H,
      v=VectorHeatInitialProcess.process F μ H u+
        MatrixPredictableConvolution.map hH N (coefficient G m) v :=
  MatrixFixedHorizonPicard.exists_unique_heat_mild hH N (coefficient G m)
    (lipschitzConstant_nonneg G hK β m) (lipschitz G hK hβ.le hG m) u

end SHEStochastic.MatrixSmoothApproximation
