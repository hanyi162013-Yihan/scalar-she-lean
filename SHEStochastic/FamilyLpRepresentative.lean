module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Reuse the existing fast-approximation representative argument for
one strongly measurable L² family, without requiring separability of all L². -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.FamilyLpRepresentative
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

variable {X Ω E : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (μ : Measure Ω) (F : X → Lp E 2 μ) (hF : StronglyMeasurable F)
local instance : MeasurableSpace (Lp E 2 μ) := borel _
local instance : BorelSpace (Lp E 2 μ) := ⟨rfl⟩

theorem exists_fast (x : X) (k : ℕ) :
    ∃ n : ℕ, dist (hF.approx n x) (F x) < (1 / 2 : ℝ) ^ k := by
  have he := (hF.tendsto_approx x).eventually
    (Metric.ball_mem_nhds (F x) (by positivity : 0 < (1 / 2 : ℝ) ^ k))
  exact he.exists

def fastIndex (x : X) (k : ℕ) : ℕ := Nat.find (exists_fast μ F hF x k)

theorem fastIndex_measurable (k : ℕ) : Measurable (fun x => fastIndex μ F hF x k) := by
  classical
  apply measurable_find (exists_fast μ F hF · k)
  intro n
  exact measurableSet_lt (((hF.approx n).stronglyMeasurable.dist hF).measurable) measurable_const

def fastApprox (x : X) (k : ℕ) : Lp E 2 μ := hF.approx (fastIndex μ F hF x k) x

theorem fast_bound (x : X) (k : ℕ) : dist (fastApprox μ F hF x k) (F x) < (1 / 2 : ℝ) ^ k :=
  Nat.find_spec (exists_fast μ F hF x k)

theorem fast_tendsto (x : X) : Tendsto (fastApprox μ F hF x) atTop (𝓝 (F x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => (fast_bound μ F hF x k).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))

theorem simple_eval_measurable (s : SimpleFunc X (Lp E 2 μ)) :
    Measurable (fun p : X × Ω => s p.1 p.2) := by
  let S := ↥(s.range : Set (Lp E 2 μ))
  have hev : Measurable (fun p : S × Ω => (p.1.val : Ω → E) p.2) :=
    measurable_from_prod_countable_right (fun f => (Lp.stronglyMeasurable f.val).measurable)
  have hs : Measurable (fun x : X => (⟨s x, s.mem_range_self x⟩ : S)) := s.measurable.subtype_mk
  exact hev.comp ((hs.comp measurable_fst).prodMk measurable_snd)

theorem fast_eval_measurable (k : ℕ) :
    Measurable (fun p : X × Ω => fastApprox μ F hF p.1 k p.2) := by
  have he : Measurable (fun p : ℕ × (X × Ω) => hF.approx p.1 p.2.1 p.2.2) :=
    measurable_from_prod_countable_right (fun n => simple_eval_measurable μ (hF.approx n))
  exact he.comp (((fastIndex_measurable μ F hF k).comp measurable_fst).prodMk measurable_id)

def representative (p : X × Ω) : E :=
  limUnder atTop (fun k => fastApprox μ F hF p.1 k p.2)

theorem representative_measurable : Measurable (representative μ F hF) :=
  (StronglyMeasurable.limUnder (fun k => (fast_eval_measurable μ F hF k).stronglyMeasurable)).measurable

theorem cauchy_bound (x : X) (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) :
    eLpNorm (fun ω => fastApprox μ F hF x n ω - fastApprox μ F hF x m ω) 2 μ <
      ENNReal.ofReal (3 * (1 / 2 : ℝ) ^ N) := by
  have he : eLpNorm (fun ω => fastApprox μ F hF x n ω - fastApprox μ F hF x m ω) 2 μ =
      ENNReal.ofReal (dist (fastApprox μ F hF x n) (fastApprox μ F hF x m)) := by
    calc
      _ = eLpNorm (fastApprox μ F hF x n - fastApprox μ F hF x m : Lp E 2 μ) 2 μ :=
        (eLpNorm_congr_ae (Lp.coeFn_sub _ _)).symm
      _ = ‖fastApprox μ F hF x n - fastApprox μ F hF x m‖ₑ := (Lp.enorm_def _).symm
      _ = _ := by rw [dist_eq_norm, ofReal_norm]
  rw [he]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 3 * (1 / 2 : ℝ) ^ N)).mpr
  have hn' := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hn
  have hm' := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hm
  have hd := dist_triangle (fastApprox μ F hF x n) (F x) (fastApprox μ F hF x m)
  rw [dist_comm (F x)] at hd
  linarith [fast_bound μ F hF x n, fast_bound μ F hF x m,
    pow_pos (by norm_num : (0 : ℝ) < 1 / 2) N]

theorem representative_ae (x : X) :
    (fun ω => representative μ F hF (x, ω)) =ᵐ[μ] F x := by
  have hsum : (∑' k : ℕ, ENNReal.ofReal (3 * (1 / 2 : ℝ) ^ k)) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ = ENNReal.ofReal 3 * (∑' k : ℕ, (ENNReal.ofReal (1 / 2 : ℝ)) ^ k) := by
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.tsum_mul_left]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (tsum_geometric_lt_top.mpr (by norm_num))
  have hc := Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun k => (Lp.stronglyMeasurable (fastApprox μ F hF x k)).aestronglyMeasurable)
    (by norm_num : (1 : ENNReal) ≤ 2) hsum (cauchy_bound μ F hF x)
  obtain ⟨ns, hns, hs⟩ := (tendstoInMeasure_of_tendsto_Lp (fast_tendsto μ F hF x)).exists_seq_tendsto_ae
  filter_upwards [hc, hs] with ω hω hsω
  obtain ⟨l, hl⟩ := hω
  have he : representative μ F hF (x, ω) = l := hl.limUnder_eq
  rw [he]
  exact tendsto_nhds_unique (hl.comp hns.tendsto_atTop) hsω

end SHEStochastic.FamilyLpRepresentative
