module

public import SHE.NativeObservationProcess
public import SHE.TwoChannelItoRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.NativeObservationCaps
open MeasureTheory Set FiniteHaar StoppedFourier PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal
local instance nativeObservationCaps_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeObservationCaps_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeObservationCaps_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeObservationCaps_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeObservationCaps_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

def cap (M gap : ℝ) : ℝ := M*(1+StoppedFourier.heatConstant*gap^(-(1/2:ℝ)))

theorem cap_nonneg {M gap : ℝ} (hM : 0≤M) (hgap : 0<gap) : 0≤cap M gap :=
  mul_nonneg hM (add_nonneg zero_le_one (mul_nonneg StoppedFourier.heatConstant_pos.le
    (Real.rpow_nonneg hgap.le _)))

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- Literal positive-prefix observation inputs have a genuine uniform
pathwise row cap. It applies to arbitrary predictable bounded fields,
including random-past frozen profiles. -/
theorem process_bound {ell M T t : ℝ} (hell : 0<ell) (hM : 0≤M)
    (f : ℝ≥0×Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (ht : t<T) (x : HeatCircle) :
    ∀ᵐ p ∂energyMeasure μ H,‖NativeObservationProcess.process 𝓕 μ H hell hM f hf ht x p‖^2≤cap M (T-t) := by
  filter_upwards [NativeObservationProcess.process_ae 𝓕 μ H hell hM f hf ht x] with p hp
  rw [hp]
  have hn := NativeObservationProcess.integrand_norm_bound hell hM f ht x p
  have hC := cap_nonneg hM (sub_pos.mpr ht)
  have hs := Real.sq_sqrt hC
  dsimp only [cap] at hs hC ⊢
  nlinarith [norm_nonneg (NativeObservationProcess.integrand hell f T t x p)]

/-- The actual two-channel block retains both row energies. -/
theorem block_bound (u v : Process (E:=RealHaarInput) 𝓕 μ H) {K L : ℝ}
    (hu : ∀ᵐ p ∂energyMeasure μ H,‖u p‖^2≤K)
    (hv : ∀ᵐ p ∂energyMeasure μ H,‖v p‖^2≤L) :
    ∀ᵐ p ∂energyMeasure μ H,‖TwoChannelItoRows.block 𝓕 μ H u v p‖^2≤K+L := by
  filter_upwards [hu,hv,TwoChannelItoRows.block_ae 𝓕 μ H u v] with p hu hv hp
  rw [hp,WithLp.prod_norm_sq_eq_of_L2]
  exact add_le_add hu hv

/-- A bounded convex-weight residual interpolation has an absolute cap
without a damping loss. The coarse constant is sufficient for the
ordinary finite-dimensional Ito applicability step. -/
theorem residual_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) {r K : ℝ} (hr : |r|≤1) (hK : 0≤K)
    (hu : ‖u‖^2≤K) (hv : ‖v‖^2≤K) :
    ‖v+r • (u-v)‖^2≤10*K := by
  have hs : ‖r • (u-v)‖≤‖u-v‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans_eq (one_mul _)
  have hd : ‖u-v‖^2≤2*(‖u‖^2+‖v‖^2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans (by
      simpa only [Nat.reduceSub,pow_one] using add_pow_le (norm_nonneg u) (norm_nonneg v) 2)
  have ha : ‖v+r • (u-v)‖^2≤2*(‖v‖^2+‖r • (u-v)‖^2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans (by
      simpa only [Nat.reduceSub,pow_one] using add_pow_le (norm_nonneg v) (norm_nonneg (r • (u-v))) 2)
  have hp := pow_le_pow_left₀ (norm_nonneg _) hs 2
  linarith

end SHE.NativeObservationCaps
