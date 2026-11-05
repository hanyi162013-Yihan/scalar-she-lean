module

public import SHE.DyadicChaining
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Uniform

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual Borel–Cantelli step for p=16,q=2 Kolmogorov continuity.
At level n the grid refines by B=2^32 and bad edges have size >2^-n.
Their total probability has a proved summable geometric majorant. -/
noncomputable section
namespace SHE.KolmogorovEdges
open Set MeasureTheory Filter DyadicClock DyadicChaining
open scoped ENNReal Topology

def base : ℕ := 2^32
theorem base_ge_two : 2 ≤ base := by norm_num [base]
def rate : ℝ := (2:ℝ)^16/(base:ℝ)
theorem rate_nonneg : 0 ≤ rate := by unfold rate; positivity
theorem rate_lt_one : rate < 1 := by norm_num [rate,base]

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E]

theorem moment_tail (μ : Measure Ω) {Y : Ω → E} (hY : Measurable Y)
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hM : (∫⁻ ω, ENNReal.ofReal (‖Y ω‖^16) ∂μ) ≤ ENNReal.ofReal A) :
    μ {ω | ε < ‖Y ω‖} ≤ ENNReal.ofReal (A/ε^16) := by
  have hεp : 0 < ε^16 := pow_pos hε _
  have hm := ENNReal.continuous_ofReal.measurable.comp (hY.norm.pow_const 16)
  calc
    _ ≤ μ {ω | ENNReal.ofReal (ε^16) ≤ ENNReal.ofReal (‖Y ω‖^16)} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hω.le 16)
    _ ≤ (∫⁻ ω,ENNReal.ofReal (‖Y ω‖^16) ∂μ)/ENNReal.ofReal (ε^16) :=
      meas_ge_le_lintegral_div hm.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr hεp)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A/ENNReal.ofReal (ε^16) := ENNReal.div_le_div_right hM _
    _ = ENNReal.ofReal (A/ε^16) := (ENNReal.ofReal_div_of_pos hεp).symm

def BadEdge (X : ℝ → Ω → E) (n k : ℕ) : Set Ω :=
  {ω | (1/2:ℝ)^n < ‖X (point base n k) ω-X (point base n (k+1)) ω‖}

def Bad (X : ℝ → Ω → E) (n : ℕ) : Set Ω := ⋃ k ∈ Finset.range (base^n), BadEdge X n k

theorem point_step (n k : ℕ) :
    |point base n k-point base n (k+1)|=1/(base:ℝ)^n := by
  have hp := pow_pos (base_real_pos base_ge_two) n
  unfold point
  rw [← sub_div,Nat.cast_add,Nat.cast_one]
  have he : (k:ℝ)-((k:ℝ)+1)= -1 := by ring
  rw [he,neg_div,abs_neg,abs_of_pos (div_pos zero_lt_one hp)]

theorem probability_algebra (C : ℝ) (n : ℕ) :
    (base:ℝ)^n * (C*(1/(base:ℝ)^n)^2/((1/2:ℝ)^n)^16)=C*rate^n := by
  have hB := (base_real_pos base_ge_two).ne'
  have he : ((1/2:ℝ)^n)^16=1/((2:ℝ)^16)^n := by
    rw [one_div_pow,one_div_pow]
    congr 1
    rw [← pow_mul,← pow_mul,Nat.mul_comm n 16]
  rw [he,rate]
  simp only [div_pow,one_pow]
  field_simp [hB,pow_ne_zero n hB]
  <;> ring

variable (μ : Measure Ω) (X : ℝ → Ω → E)
variable (hX : ∀ t ∈ Icc (0:ℝ) 1,Measurable (X t))
variable {C : ℝ} (hC : 0 ≤ C)
variable (hM : ∀ s ∈ Icc (0:ℝ) 1,∀ t ∈ Icc (0:ℝ) 1,
  (∫⁻ ω,ENNReal.ofReal (‖X s ω-X t ω‖^16) ∂μ) ≤ ENNReal.ofReal (C*|s-t|^2))
include hX hC hM

theorem badEdge_probability (n k : ℕ) (hk : k < base^n) :
    μ (BadEdge X n k) ≤ ENNReal.ofReal (C*(1/(base:ℝ)^n)^2/((1/2:ℝ)^n)^16) := by
  have hs := point_mem base_ge_two hk.le
  have ht := point_mem base_ge_two (Nat.succ_le_of_lt hk)
  have he := hM _ hs _ ht
  rw [point_step] at he
  exact moment_tail μ ((hX _ hs).sub (hX _ ht)) (mul_nonneg hC (sq_nonneg _)) (by positivity) he

theorem bad_probability (n : ℕ) : μ (Bad X n) ≤ ENNReal.ofReal (C*rate^n) := by
  apply (measure_biUnion_finset_le (Finset.range (base^n)) (BadEdge X n)).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range (base^n),ENNReal.ofReal (C*(1/(base:ℝ)^n)^2/((1/2:ℝ)^n)^16) := by
      apply Finset.sum_le_sum
      intro k hk
      exact badEdge_probability μ X hX hC hM n k (Finset.mem_range.mp hk)
    _ = ENNReal.ofReal (C*rate^n) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast]
      simp only [Nat.cast_pow]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (base:ℝ)^n),probability_algebra]

theorem bad_measurable (n : ℕ) : MeasurableSet (Bad X n) := by
  apply MeasurableSet.biUnion (Finset.countable_toSet (Finset.range (base^n)))
  intro k hk
  have hkn : k < base^n := Finset.mem_range.mp hk
  exact measurableSet_lt measurable_const (((hX _ (point_mem base_ge_two hkn.le)).sub
    (hX _ (point_mem base_ge_two (Nat.succ_le_of_lt hkn)))).norm)

theorem eventually_edgeBound : ∀ᵐ ω ∂μ,∀ᶠ n in atTop,EdgeBound base (fun t => X t ω) n := by
  have hsum : (∑' n,μ (Bad X n)) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n,ENNReal.ofReal (C*rate^n) := ENNReal.tsum_le_tsum (bad_probability μ X hX hC hM)
      _ = ENNReal.ofReal C*(∑' n,(ENNReal.ofReal rate)^n) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.ofReal_pow rate_nonneg,ENNReal.tsum_mul_left]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((tsum_geometric_lt_top).mpr (ENNReal.ofReal_lt_one.mpr rate_lt_one))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  by_contra hbad
  apply hn
  apply mem_iUnion.mpr
  refine ⟨k,mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,?_⟩⟩
  simpa only [BadEdge,mem_ofPred_eq,dist_eq_norm] using lt_of_not_ge hbad

end SHE.KolmogorovEdges
