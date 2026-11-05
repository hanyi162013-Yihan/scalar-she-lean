module

public import SHEStochastic.CanonicalBrownianMeasure
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.CanonicalBrownianChannels
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
abbrev Sample := ℝ≥0 → ℝ
local notation "μ" => CanonicalBrownianMeasure.measure

def start (i : ℕ) : ℝ≥0 := 2*(i : ℝ≥0)
def time (i : ℕ) (t : ℝ≥0) : ℝ≥0 := start i+min t 1

/-- Countably many native Brownian channels are obtained from disjoint
unit increments of the single constructed raw Brownian process. -/
def value (i : ℕ) (t : ℝ≥0) (ω : Sample) : ℝ := ω (time i t)-ω (start i)

theorem measurable_value (i : ℕ) (t : ℝ≥0) : Measurable (value i t) :=
  (measurable_pi_apply (time i t)).sub (measurable_pi_apply (start i))

/-- Every family of two-point raw increments is jointly Gaussian;
this is a finite linear-map consequence of the existing Brownian laws. -/
theorem difference_gaussian {I : Type*} (a b : I → ℝ≥0) :
    IsGaussianProcess (fun i ω => ω (a i)-ω (b i)) μ := by
  classical
  apply CanonicalBrownianMeasure.preBrownian.isGaussianProcess.of_isGaussianProcess
  intro i
  refine ⟨{a i,b i},{
    toFun := fun x => x ⟨a i,by simp⟩-x ⟨b i,by simp⟩
    map_add' := fun x y => by simp;ring
    map_smul' := fun c x => by simp;ring },?_⟩
  intro ω
  rfl

theorem gaussian : IsGaussianProcess (fun p : ℕ×ℝ≥0 => value p.1 p.2) μ :=
  difference_gaussian (fun p : ℕ×ℝ≥0 => time p.1 p.2) (fun p : ℕ×ℝ≥0 => start p.1)

theorem memLp_value (i : ℕ) (t : ℝ≥0) : MemLp (value i t) 2 μ :=
  (gaussian.hasGaussianLaw_eval (i,t)).memLp_two

theorem mean_value (i : ℕ) (t : ℝ≥0) : (∫ ω,value i t ω ∂μ)=0 := by
  change (∫ ω : Sample,ω (time i t)-ω (start i) ∂μ)=0
  rw [integral_sub]
  · have hm (q : ℝ≥0) : (∫ ω : Sample,ω q ∂μ)=0 := CanonicalBrownianMeasure.preBrownian.integral_eval q
    rw [hm,hm,sub_self]
  · exact (CanonicalBrownianMeasure.preBrownian.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · exact (CanonicalBrownianMeasure.preBrownian.isGaussianProcess.hasGaussianLaw_eval _).integrable

theorem covariance_raw (a b c d : ℝ≥0) :
    cov[fun ω : Sample => ω a-ω b,fun ω => ω c-ω d;μ]=
      min (a : ℝ) (c : ℝ)-min (a : ℝ) (d : ℝ)-min (b : ℝ) (c : ℝ)+min (b : ℝ) (d : ℝ) := by
  have hm (s : ℝ≥0) : MemLp (fun ω : Sample => ω s) 2 μ :=
    (CanonicalBrownianMeasure.preBrownian.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  rw [covariance_fun_sub_fun_sub (hm a) (hm b) (hm c) (hm d)]
  simp only [CanonicalBrownianMeasure.covariance]

theorem covariance_same (i : ℕ) (s t : ℝ≥0) :
    cov[value i s,value i t;μ]=min (min (s : ℝ) 1) (min (t : ℝ) 1) := by
  change cov[fun ω : Sample => ω (time i s)-ω (start i),
    fun ω => ω (time i t)-ω (start i);μ]=_
  rw [covariance_raw]
  simp only [time,start,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_min,NNReal.coe_one]
  have hs : 0 ≤ min (s : ℝ) 1 := le_min s.coe_nonneg zero_le_one
  have ht : 0 ≤ min (t : ℝ) 1 := le_min t.coe_nonneg zero_le_one
  have hc (A B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
      min (A+B) (A+C)-min (A+B) A-min A (A+C)+min A A=min B C := by
    rw [min_add_add_left,
      min_eq_right (a := A+B) (b := A) (by linarith),
      min_eq_left (a := A) (b := A+C) (by linarith),min_self]
    ring
  exact hc _ _ _ hs ht

theorem covariance_lt {i j : ℕ} (hij : i < j) (s t : ℝ≥0) : cov[value i s,value j t;μ]=0 := by
  change cov[fun ω : Sample => ω (time i s)-ω (start i),
    fun ω => ω (time j t)-ω (start j);μ]=_
  rw [covariance_raw]
  simp only [time,start,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_min,NNReal.coe_one]
  have hi : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
  have hs0 : 0 ≤ min (s : ℝ) 1 := le_min s.coe_nonneg zero_le_one
  have ht0 : 0 ≤ min (t : ℝ) 1 := le_min t.coe_nonneg zero_le_one
  have hs1 : min (s : ℝ) 1 ≤ 1 := min_le_right _ _
  have hc (A B x y : ℝ) (hAB : A+1 ≤ B) (hx : x ≤ 1) (hy : 0 ≤ y) :
      min (A+x) (B+y)-min (A+x) B-min A (B+y)+min A B=0 := by
    rw [min_eq_left (a := A+x) (b := B+y) (by linarith),
      min_eq_left (a := A+x) (b := B) (by linarith),
      min_eq_left (a := A) (b := B+y) (by linarith),
      min_eq_left (a := A) (b := B) (by linarith)]
    ring
  exact hc _ _ _ _ (by linarith) hs1 ht0

/-- Exact Kronecker/minimum covariance for every pair of channels,
including repeated coordinates and times. -/
theorem covariance_value (i j : ℕ) (s t : ℝ≥0) :
    cov[value i s,value j t;μ]=(if i=j then min (min (s : ℝ) 1) (min (t : ℝ) 1) else 0) := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg (Nat.ne_of_lt h)]
    exact covariance_lt h s t
  · rw [if_pos rfl]
    exact covariance_same i s t
  · rw [if_neg (Nat.ne_of_gt h),covariance_comm]
    exact covariance_lt h t s

end SHEStochastic.CanonicalBrownianChannels
