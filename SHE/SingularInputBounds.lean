module

public import SHE.FullHorizonEndpointVersion
public import SHE.TwoChannelItoRows
public import SHE.PredictableContraction
public import SHE.PredictableItoRotation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.SingularInputBounds
open Set MeasureTheory PredictableL2 StoppedItoInputs PredictableItoRotation OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H b : ℝ≥0)

def Bound (K : ℝ) (u : Process (E:=C) 𝓕 μ H) : Prop :=
  ∀ᵐ p∂energyMeasure μ H,p.1≤b→‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ))

theorem stop_bound {K : ℝ} (hK : 0≤K) {u : Process (E:=C) 𝓕 μ H}
    (hu : Bound 𝓕 μ H b K u) (t : ℝ) : Bound 𝓕 μ H b K (stop 𝓕 μ H t u) := by
  filter_upwards [hu,stop_ae 𝓕 μ H t u] with p hu hs hp
  rw [hs]
  by_cases ht : p∈before (Ω:=Ω) t
  · rw [indicator_of_mem ht]
    exact hu hp
  · rw [indicator_of_notMem ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact mul_nonneg hK (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hp)) _)

theorem smul_bound {K : ℝ} {u : Process (E:=C) 𝓕 μ H}
    (hu : Bound 𝓕 μ H b K u) (a : ℝ) : Bound 𝓕 μ H b (a^2*K) (a • u) := by
  filter_upwards [hu,ae_eq_of_ae_eq_trim (Lp.coeFn_smul a u)] with p hu hs hp
  rw [hs]
  change ‖a • u p‖^2≤_
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact (mul_le_mul_of_nonneg_left (hu hp) (sq_nonneg a)).trans_eq (by ring)

theorem sub_bound {K L : ℝ} {u v : Process (E:=C) 𝓕 μ H}
    (hu : Bound 𝓕 μ H b K u) (hv : Bound 𝓕 μ H b L v) :
    Bound 𝓕 μ H b (2*(K+L)) (u-v) := by
  filter_upwards [hu,hv,ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v)] with p hu hv hs hp
  rw [hs]
  change ‖u p-v p‖^2≤_
  have hn:=(pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (u p) (v p)) 2).trans
    (add_pow_le (norm_nonneg (u p)) (norm_nonneg (v p)) 2)
  norm_num only [Nat.reduceSub,pow_one] at hn
  nlinarith [hu hp,hv hp]

theorem weighted_bound {K : ℝ} {u : Process (E:=C) 𝓕 μ H}
    (hu : Bound 𝓕 μ H b K u) (a : ℝ≥0×Ω→ℝ)
    (ha : StronglyMeasurable[𝓕.predictable] a) (hb : ∀ p,|a p|≤1) :
    Bound 𝓕 μ H b K (PredictableContraction.weighted 𝓕 μ H a ha hb u) := by
  filter_upwards [hu,PredictableContraction.weighted_ae 𝓕 μ H a ha hb u] with p hu hw hp
  rw [hw]
  have hn : ‖a p • u p‖≤‖u p‖:=by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)).trans_eq (one_mul _)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hu hp)

variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
local instance singularInputBounds_blockSigma : MeasurableSpace (Both C) := borel _
local instance singularInputBounds_blockBorel : BorelSpace (Both C) := ⟨rfl⟩

theorem block_bound {K L : ℝ} {u v : Process (E:=C) 𝓕 μ H}
    (hu : Bound 𝓕 μ H b K u) (hv : Bound 𝓕 μ H b L v) :
    Bound 𝓕 μ H b (K+L) (TwoChannelItoRows.block 𝓕 μ H u v) := by
  filter_upwards [hu,hv,TwoChannelItoRows.block_ae 𝓕 μ H u v] with p hu hv hb hp
  rw [hb,WithLp.prod_norm_sq_eq_of_L2]
  exact (add_le_add (hu hp) (hv hp)).trans_eq (by ring)

theorem right_bound {K : ℝ} {u : Process (E:=C) 𝓕 μ H} (hu : Bound 𝓕 μ H b K u) :
    Bound 𝓕 μ H b K (processIsometry 𝓕 μ H (fun _=>right (C:=C)) (right_measurable 𝓕) u) := by
  filter_upwards [hu,processIsometry_ae 𝓕 μ H (fun _=>right (C:=C)) (right_measurable 𝓕) u] with p hu hi hp
  rw [hi,LinearIsometry.norm_map]
  exact hu hp

end SHE.SingularInputBounds
