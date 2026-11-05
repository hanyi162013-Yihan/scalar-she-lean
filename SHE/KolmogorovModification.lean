module

public import SHE.KolmogorovEdges
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! A genuine one-dimensional Kolmogorov continuous-modification theorem
for p=16,q=2 on [0,1], proved from finite grids and Borel–Cantelli.
No continuous-version or Kolmogorov theorem is an external input. -/
noncomputable section
namespace SHE.KolmogorovModification
open Set MeasureTheory Filter DyadicClock DyadicChaining KolmogorovEdges
open scoped ENNReal Topology
open Classical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def goodSet (X : ℝ → Ω → E) : Set Ω := ⋃ N : ℕ,⋂ n : ℕ,⋂ (_ : N ≤ n),(Bad X n)ᶜ

theorem not_bad_iff (X : ℝ → Ω → E) (ω : Ω) (n : ℕ) :
    ω ∉ Bad X n ↔ EdgeBound base (fun t => X t ω) n := by
  constructor
  · intro hn k hk
    by_contra hb
    apply hn
    apply mem_iUnion.mpr
    refine ⟨k,mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,?_⟩⟩
    simpa only [BadEdge,mem_ofPred_eq,dist_eq_norm] using lt_of_not_ge hb
  · intro hn hbad
    rcases mem_iUnion.mp hbad with ⟨k,hk⟩
    rcases mem_iUnion.mp hk with ⟨hk,hbad⟩
    have he := hn k (Finset.mem_range.mp hk)
    exact (not_lt_of_ge he) (by simpa only [BadEdge,mem_ofPred_eq,dist_eq_norm] using hbad)

theorem mem_goodSet_iff (X : ℝ → Ω → E) (ω : Ω) :
    ω ∈ goodSet X ↔ ∀ᶠ n in atTop,EdgeBound base (fun t => X t ω) n := by
  simp only [goodSet,mem_iUnion,mem_iInter,mem_compl_iff,not_bad_iff]
  exact eventually_atTop.symm

def modification (X : ℝ → Ω → E) (t : ℝ) (ω : Ω) : E :=
  if ω ∈ goodSet X then pathLimit base (fun r => X r ω) t else 0

theorem continuousOn_modification (X : ℝ → Ω → E) (ω : Ω) :
    ContinuousOn (fun t => modification X t ω) (Icc (0:ℝ) 1) := by
  classical
  by_cases hω : ω ∈ goodSet X
  · have heq : (fun t => modification X t ω)=pathLimit base (fun r => X r ω) := by
      funext t
      exact if_pos hω
    rw [heq]
    exact (pathLimit_uniformContinuousOn base_ge_two _ ((mem_goodSet_iff X ω).mp hω)).continuousOn
  · have heq : (fun t => modification X t ω)=fun _ => (0:E) := by funext t; exact if_neg hω
    rw [heq]
    exact continuousOn_const

variable (μ : Measure Ω) (X : ℝ → Ω → E)
variable (hX : ∀ t ∈ Icc (0:ℝ) 1,Measurable (X t))
variable {C : ℝ} (hC : 0 ≤ C)
variable (hM : ∀ s ∈ Icc (0:ℝ) 1,∀ t ∈ Icc (0:ℝ) 1,
  (∫⁻ ω,ENNReal.ofReal (‖X s ω-X t ω‖^16) ∂μ) ≤ ENNReal.ofReal (C*|s-t|^2))
include hX hC hM

theorem goodSet_measurable : MeasurableSet (goodSet X) := by
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  exact (bad_measurable μ X hX hC hM n).compl

theorem goodSet_ae : ∀ᵐ ω ∂μ,ω ∈ goodSet X := by
  filter_upwards [eventually_edgeBound μ X hX hC hM] with ω hω
  exact (mem_goodSet_iff X ω).mpr hω

theorem modification_measurable {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Measurable (modification X t) := by
  classical
  let F : ℕ → Ω → E := fun n ω => if ω ∈ goodSet X then X (approximate base n t) ω else 0
  have hF : ∀ n,Measurable (F n) := fun n =>
    (hX _ (approximate_mem base_ge_two ht)).ite (goodSet_measurable μ X hX hC hM) measurable_const
  have hl : Tendsto F atTop (𝓝 (modification X t)) := by
    apply tendsto_pi_nhds.mpr
    intro ω
    by_cases hω : ω ∈ goodSet X
    · have he := approximation_tendsto base_ge_two (fun r => X r ω) ((mem_goodSet_iff X ω).mp hω) ht
      simpa only [F,modification,ite_eq_left hω] using he
    · simp only [F,modification,ite_eq_right hω]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hF hl

theorem approximation_original_ae {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∀ᵐ ω ∂μ,Tendsto (fun n => X (approximate base n t) ω) atTop (𝓝 (X t ω)) := by
  let A : ℕ → Set Ω := fun n => {ω | (1/2:ℝ)^n < ‖X (approximate base n t) ω-X t ω‖}
  have hprob (n : ℕ) : μ (A n) ≤ ENNReal.ofReal (C*rate^n) := by
    have hmem := approximate_mem base_ge_two (n := n) ht
    have he := hM _ hmem _ ht
    have hd : |approximate base n t-t| ≤ 1/(base:ℝ)^n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (approximate_bounds base_ge_two ht.1).1),neg_sub]
      exact (approximate_bounds base_ge_two ht.1).2.le
    have hmom : (∫⁻ ω,ENNReal.ofReal (‖X (approximate base n t) ω-X t ω‖^16) ∂μ) ≤
        ENNReal.ofReal (C*(1/(base:ℝ)^n)^2) := he.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hd 2) hC))
    have hp := moment_tail μ ((hX _ hmem).sub (hX _ ht))
      (mul_nonneg hC (sq_nonneg _)) (by positivity : (0:ℝ) < (1/2)^n) hmom
    apply hp.trans
    apply ENNReal.ofReal_le_ofReal
    rw [← probability_algebra C n]
    have hB : (1:ℝ) ≤ (base:ℝ)^n := one_le_pow₀ (by
      exact_mod_cast (show 1 ≤ base by have := base_ge_two; omega))
    have hA : 0 ≤ C*(1/(base:ℝ)^n)^2/((1/2:ℝ)^n)^16 := by positivity
    nlinarith
  have hsum : (∑' n,μ (A n)) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n,ENNReal.ofReal (C*rate^n) := ENNReal.tsum_le_tsum hprob
      _ = ENNReal.ofReal C*(∑' n,(ENNReal.ofReal rate)^n) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.ofReal_pow rate_nonneg,ENNReal.tsum_mul_left]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((tsum_geometric_lt_top).mpr (ENNReal.ofReal_lt_one.mpr rate_lt_one))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  have hb : ∀ᶠ n in atTop,‖X (approximate base n t) ω-X t ω‖ ≤ (1/2:ℝ)^n := by
    filter_upwards [hω] with n hn
    exact le_of_not_gt hn
  have hl := squeeze_zero_norm' hb (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1))
  have he := hl.add_const (X t ω)
  simpa only [sub_add_cancel,zero_add] using he

theorem modification_ae {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : modification X t =ᵐ[μ] X t := by
  filter_upwards [goodSet_ae μ X hX hC hM,approximation_original_ae μ X hX hC hM ht] with ω hω ho
  rw [modification,ite_eq_left hω]
  exact tendsto_nhds_unique (approximation_tendsto base_ge_two _ ((mem_goodSet_iff X ω).mp hω) ht) ho

theorem modification_joint_measurable :
    Measurable (fun p : (Icc (0:ℝ) 1) × Ω => modification X p.1 p.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : Icc (0:ℝ) 1) ω => modification X t ω)
  · intro ω
    exact (continuousOn_modification X ω).domRestrict
  · intro t
    exact modification_measurable μ X hX hC hM t.2

/-- Concrete Kolmogorov continuity: a genuine jointly Borel modification
with continuous paths is constructed from p=16,q=2 moment bounds. -/
theorem exists_continuous_modification : ∃ Y : ℝ → Ω → E,
    (∀ ω,ContinuousOn (fun t => Y t ω) (Icc (0:ℝ) 1)) ∧
    (∀ t ∈ Icc (0:ℝ) 1,Measurable (Y t) ∧ Y t =ᵐ[μ] X t) ∧
    Measurable (fun p : (Icc (0:ℝ) 1) × Ω => Y p.1 p.2) := by
  refine ⟨modification X,continuousOn_modification X,?_,modification_joint_measurable μ X hX hC hM⟩
  intro t ht
  exact ⟨modification_measurable μ X hX hC hM ht,modification_ae μ X hX hC hM ht⟩

end SHE.KolmogorovModification
