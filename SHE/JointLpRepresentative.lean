module

public import SHE.MeasurableL2Field
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! A jointly Borel representative of every element of a separable
real L² space. Fast approximants are chosen measurably, and their actual
spatial almost-everywhere convergence is proved from L² estimates.
This supplies predictable scalar representatives of L²-valued processes. -/
noncomputable section
namespace SHE.JointLpRepresentative
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X] (ν : Measure X)
local instance jointLpRepresentative_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance jointLpRepresentative_oneLeExponent : Fact ((1:ENNReal) ≤ 2) := ⟨by norm_num⟩
local instance jointLpRepresentative_lpSigma : MeasurableSpace (Lp ℝ 2 ν) := borel (Lp ℝ 2 ν)
local instance jointLpRepresentative_lpBorel : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩
variable [SecondCountableTopology (Lp ℝ 2 ν)]

def approximant : ℕ → SimpleFunc (Lp ℝ 2 ν) (Lp ℝ 2 ν) :=
  (stronglyMeasurable_id : StronglyMeasurable (id : Lp ℝ 2 ν → Lp ℝ 2 ν)).approx

theorem approximant_tendsto (f : Lp ℝ 2 ν) :
    Tendsto (fun n => approximant ν n f) atTop (𝓝 f) :=
  (stronglyMeasurable_id : StronglyMeasurable (id : Lp ℝ 2 ν → Lp ℝ 2 ν)).tendsto_approx f

theorem exists_fast (f : Lp ℝ 2 ν) (k : ℕ) :
    ∃ n : ℕ,dist (approximant ν n f) f < (1/2:ℝ)^k := by
  have he := (approximant_tendsto ν f).eventually
    (Metric.ball_mem_nhds f (by positivity : (0:ℝ) < (1/2)^k))
  obtain ⟨n,hn⟩ := he.exists
  exact ⟨n,hn⟩

open Classical in
def fastIndex (f : Lp ℝ 2 ν) (k : ℕ) : ℕ := Nat.find (exists_fast ν f k)

theorem fastIndex_measurable (k : ℕ) : Measurable (fun f => fastIndex ν f k) := by
  classical
  apply measurable_find (exists_fast ν · k)
  intro n
  exact measurableSet_lt ((approximant ν n).measurable.dist measurable_id) measurable_const

def fastApprox (f : Lp ℝ 2 ν) (k : ℕ) : Lp ℝ 2 ν := approximant ν (fastIndex ν f k) f

theorem fastApprox_bound (f : Lp ℝ 2 ν) (k : ℕ) :
    dist (fastApprox ν f k) f < (1/2:ℝ)^k := Nat.find_spec (exists_fast ν f k)

theorem fastApprox_tendsto (f : Lp ℝ 2 ν) : Tendsto (fastApprox ν f) atTop (𝓝 f) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => (fastApprox_bound ν f k).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))

theorem simple_eval_measurable {P : Type*} [MeasurableSpace P]
    (s : SimpleFunc P (Lp ℝ 2 ν)) : Measurable (fun p : P × X => s p.1 p.2) := by
  let S := ↥(s.range : Set (Lp ℝ 2 ν))
  have hev : Measurable (fun p : S × X => (p.1.val : X → ℝ) p.2) :=
    measurable_from_prod_countable_right (fun f => (Lp.stronglyMeasurable f.val).measurable)
  have hs : Measurable (fun p : P => (⟨s p,s.mem_range_self p⟩ : S)) := s.measurable.subtype_mk
  have hp : Measurable (fun p : P × X => ((⟨s p.1,s.mem_range_self p.1⟩ : S),p.2)) :=
    (hs.comp measurable_fst).prodMk measurable_snd
  exact hev.comp hp

theorem fast_eval_measurable (k : ℕ) :
    Measurable (fun p : Lp ℝ 2 ν × X => fastApprox ν p.1 k p.2) := by
  have he : Measurable (fun p : ℕ × (Lp ℝ 2 ν × X) => approximant ν p.1 p.2.1 p.2.2) :=
    measurable_from_prod_countable_right (fun n => simple_eval_measurable ν (approximant ν n))
  have hp : Measurable (fun p : Lp ℝ 2 ν × X => (fastIndex ν p.1 k,p)) :=
    ((fastIndex_measurable ν k).comp measurable_fst).prodMk measurable_id
  exact he.comp hp

def representative (p : Lp ℝ 2 ν × X) : ℝ := limUnder atTop (fun k => fastApprox ν p.1 k p.2)

theorem representative_measurable : Measurable (representative ν) :=
  (StronglyMeasurable.limUnder (fun k => (fast_eval_measurable ν k).stronglyMeasurable)).measurable

theorem fastApprox_cauchy_bound (f : Lp ℝ 2 ν) (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) :
    eLpNorm (fun x => fastApprox ν f n x-fastApprox ν f m x) 2 ν <
      ENNReal.ofReal (3*(1/2:ℝ)^N) := by
  have he : eLpNorm (fun x => fastApprox ν f n x-fastApprox ν f m x) 2 ν=
      ENNReal.ofReal (dist (fastApprox ν f n) (fastApprox ν f m)) := by
    calc
      _ = eLpNorm (fastApprox ν f n-fastApprox ν f m : Lp ℝ 2 ν) 2 ν :=
        (eLpNorm_congr_ae (Lp.coeFn_sub (fastApprox ν f n) (fastApprox ν f m))).symm
      _ = ‖fastApprox ν f n-fastApprox ν f m‖ₑ := (Lp.enorm_def _).symm
      _ = _ := by rw [dist_eq_norm,ofReal_norm]
  rw [he]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0:ℝ) < 3*(1/2:ℝ)^N)).mpr
  have hn' := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) hn
  have hm' := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) hm
  have hd := dist_triangle (fastApprox ν f n) f (fastApprox ν f m)
  rw [dist_comm f] at hd
  linarith [fastApprox_bound ν f n,fastApprox_bound ν f m,pow_pos (by norm_num : (0:ℝ) < 1/2) N]

/-- The jointly Borel realization represents EVERY L² element, with the
correct spatial almost-everywhere equality for each individual element. -/
theorem representative_ae (f : Lp ℝ 2 ν) :
    (fun x => representative ν (f,x))=ᵐ[ν] f := by
  have hsum : (∑' k : ℕ,ENNReal.ofReal (3*(1/2:ℝ)^k)) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ = ENNReal.ofReal 3*(∑' k : ℕ,(ENNReal.ofReal (1/2:ℝ))^k) := by
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
          ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.tsum_mul_left]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (tsum_geometric_lt_top.mpr (by norm_num))
  have hc := Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun k => (Lp.stronglyMeasurable (fastApprox ν f k)).aestronglyMeasurable)
    (by norm_num : (1:ENNReal) ≤ 2) hsum (fastApprox_cauchy_bound ν f)
  obtain ⟨ns,hns,hs⟩ := (tendstoInMeasure_of_tendsto_Lp (fastApprox_tendsto ν f)).exists_seq_tendsto_ae
  filter_upwards [hc,hs] with x hx hsx
  obtain ⟨l,hl⟩ := hx
  have he : representative ν (f,x)=l := hl.limUnder_eq
  rw [he]
  exact tendsto_nhds_unique (hl.comp hns.tendsto_atTop) hsx

end SHE.JointLpRepresentative
