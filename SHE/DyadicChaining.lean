module

public import SHE.DyadicClock
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Deterministic dyadic chaining: eventual adjacent-edge bounds on
nested finite grids construct an actual continuous limit on [0,1]. -/
noncomputable section
namespace SHE.DyadicChaining
open Set Filter DyadicClock
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]

def EdgeBound (B : ℕ) (f : ℝ → E) (n : ℕ) : Prop :=
  ∀ k < B^n,dist (f (point B n k)) (f (point B n (k+1))) ≤ (1/2:ℝ)^n

theorem grid_chain_bound {B n a b : ℕ} {f : ℝ → E} (hab : a ≤ b) (hb : b ≤ B^n)
    (he : EdgeBound B f n) :
    dist (f (point B n a)) (f (point B n b)) ≤ (b-a:ℕ)*(1/2:ℝ)^n := by
  apply (dist_le_Ico_sum_dist (fun k => f (point B n k)) hab).trans
  calc
    _ ≤ ∑ _k ∈ Finset.Ico a b,(1/2:ℝ)^n := by
      apply Finset.sum_le_sum
      intro k hk
      exact he k ((Finset.mem_Ico.mp hk).2.trans_le hb)
    _ = _ := by simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]

theorem approximation_increment {B : ℕ} (hB : 2 ≤ B) (f : ℝ → E) {n : ℕ}
    (he : EdgeBound B f (n+1)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    dist (f (approximate B n t)) (f (approximate B (n+1) t)) ≤ B*(1/2:ℝ)^(n+1) := by
  have hbounds := refinement_bounds hB n t
  have hi := index_le hB (n := n+1) ht
  have hc := grid_chain_bound hbounds.1 hi he
  have hlen : index B (n+1) t-B*index B n t ≤ B := by omega
  have hlenR : ((index B (n+1) t-B*index B n t:ℕ):ℝ) ≤ B := by exact_mod_cast hlen
  change dist (f (point B n (index B n t))) (f (point B (n+1) (index B (n+1) t))) ≤ _
  rw [point_refine hB]
  exact hc.trans (mul_le_mul_of_nonneg_right hlenR (by positivity))

variable [CompleteSpace E]

theorem approximation_cauchy {B : ℕ} (hB : 2 ≤ B) (f : ℝ → E)
    (he : ∀ᶠ n in atTop,EdgeBound B f n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    CauchySeq (fun n => f (approximate B n t)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let g : ℕ → E := fun k => f (approximate B (k+N) t)
  have hg : ∀ k,dist (g k) (g (k+1)) ≤ (B:ℝ)*(1/2:ℝ)^(N+1)*(1/2:ℝ)^k := by
    intro k
    have hi := approximation_increment hB f (hN (k+N+1) (by omega)) ht
    change dist (f (approximate B (k+N) t)) (f (approximate B (k+1+N) t)) ≤ _
    rw [show k+1+N=k+N+1 by omega]
    calc
      _ ≤ B*(1/2:ℝ)^(k+N+1) := hi
      _ = _ := by rw [show k+N+1=N+1+k by omega,pow_add]; ring
  have hc : CauchySeq g := cauchySeq_of_le_geometric (1/2:ℝ) ((B:ℝ)*(1/2:ℝ)^(N+1)) (by norm_num) hg
  have hlim := hc.tendsto_limUnder
  have hfull : Tendsto (fun n => f (approximate B n t)) atTop (𝓝 (limUnder atTop g)) :=
    (tendsto_add_atTop_iff_nat N).mp hlim
  exact hfull.cauchySeq

def pathLimit (B : ℕ) (f : ℝ → E) (t : ℝ) : E := limUnder atTop (fun n => f (approximate B n t))

theorem approximation_tendsto {B : ℕ} (hB : 2 ≤ B) (f : ℝ → E)
    (he : ∀ᶠ n in atTop,EdgeBound B f n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => f (approximate B n t)) atTop (𝓝 (pathLimit B f t)) :=
  (approximation_cauchy hB f he ht).tendsto_limUnder

theorem approximation_limit_bound {B N : ℕ} (hB : 2 ≤ B) (f : ℝ → E)
    (he : ∀ n ≥ N,EdgeBound B f n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {n : ℕ} (hn : N ≤ n) :
    dist (f (approximate B n t)) (pathLimit B f t) ≤ B*(1/2:ℝ)^n := by
  have hall : ∀ᶠ k in atTop,EdgeBound B f k := eventually_atTop.mpr ⟨N,he⟩
  have hlim := (tendsto_add_atTop_iff_nat n).mpr (approximation_tendsto hB f hall ht)
  have hg : ∀ k,dist (f (approximate B (k+n) t)) (f (approximate B (k+1+n) t)) ≤
      (B:ℝ)*(1/2:ℝ)^(n+1)*(1/2:ℝ)^k := by
    intro k
    have hi := approximation_increment hB f (he (k+n+1) (by omega)) ht
    rw [show k+1+n=k+n+1 by omega]
    calc
      _ ≤ B*(1/2:ℝ)^(k+n+1) := hi
      _ = _ := by rw [show k+n+1=n+1+k by omega,pow_add]; ring
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) ((B:ℝ)*(1/2:ℝ)^(n+1))
    (by norm_num : (1/2:ℝ) < 1) hg hlim
  simp only [zero_add] at hb
  convert hb using 1
  rw [pow_succ]
  ring

theorem close_indices {B : ℕ} (hB : 2 ≤ B) {n : ℕ} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≤ t) (hd : t-s < 1/(B:ℝ)^n) :
    index B n s ≤ index B n t ∧ index B n t ≤ index B n s+1 := by
  have hp := pow_pos (base_real_pos hB) n
  have hmono := Nat.floor_mono (mul_le_mul_of_nonneg_right hst hp.le)
  have hfloor := Nat.floor_le (mul_nonneg ht hp.le)
  have hfloorS := Nat.lt_floor_add_one (s*(B:ℝ)^n)
  have hdm := (lt_div_iff₀ hp).mp hd
  have hiR : (index B n t:ℝ) < (index B n s:ℝ)+2 := by
    change (index B n t:ℝ) ≤ t*(B:ℝ)^n at hfloor
    change s*(B:ℝ)^n < (index B n s:ℝ)+1 at hfloorS
    nlinarith
  have hi : index B n t < index B n s+2 := by exact_mod_cast hiR
  exact ⟨hmono,by omega⟩

theorem approximation_near {B : ℕ} (hB : 2 ≤ B) (f : ℝ → E) {n : ℕ}
    (he : EdgeBound B f n) {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (hd : dist s t < 1/(B:ℝ)^n) :
    dist (f (approximate B n s)) (f (approximate B n t)) ≤ (1/2:ℝ)^n := by
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this ht hs (by simpa only [dist_comm] using hd) (le_of_not_ge hst)
  have hd' : t-s < 1/(B:ℝ)^n := by simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] using hd
  have hi := close_indices hB hs.1 ht.1 hst hd'
  have hb := grid_chain_bound hi.1 (index_le hB ht) he
  have hlen : ((index B n t-index B n s:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show index B n t-index B n s ≤ 1 by omega)
  exact hb.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlen (by positivity : 0 ≤ (1/2:ℝ)^n))

theorem pathLimit_uniformContinuousOn {B : ℕ} (hB : 2 ≤ B) (f : ℝ → E)
    (he : ∀ᶠ n in atTop,EdgeBound B f n) : UniformContinuousOn (pathLimit B f) (Icc (0:ℝ) 1) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => (2*(B:ℝ)+1)*(1/2:ℝ)^n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul (2*(B:ℝ)+1)
  obtain ⟨n,hn,hsmall⟩ := ((eventually_ge_atTop N).and (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨1/(B:ℝ)^n,by positivity,?_⟩
  intro s hs t ht hst
  have hsB := approximation_limit_bound hB f hN hs hn
  have htB := approximation_limit_bound hB f hN ht hn
  have hc := approximation_near hB f (hN n hn) hs ht hst
  have htri := dist_triangle4 (pathLimit B f s) (f (approximate B n s))
    (f (approximate B n t)) (pathLimit B f t)
  rw [dist_comm] at hsB
  nlinarith

end SHE.DyadicChaining
