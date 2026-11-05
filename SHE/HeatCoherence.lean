module

public import SHE.FiniteStabilization
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Max

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HeatCoherence
open SimpleGraph

variable {I : Type*}

/-- Physical heat observations are coherent when their ages are
comparable and their centers are close on the larger heat scale. -/
def graph (t x : I → ℝ) (K : ℝ) : SimpleGraph I where
  Adj i j := i ≠ j ∧ t i ≤ K*t j ∧ t j ≤ K*t i ∧
    |x i-x j| ≤ K*Real.sqrt (max (t i) (t j))
  symm := ⟨fun i j h => ⟨h.1.symm,h.2.2.1,h.2.1,by simpa only [abs_sub_comm,max_comm] using h.2.2.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem graph_mono (t x : I → ℝ) (ht : ∀ i, 0 ≤ t i) {K L : ℝ} (hKL : K ≤ L) :
    graph t x K ≤ graph t x L := by
  intro i j h
  exact ⟨h.1,h.2.1.trans (mul_le_mul_of_nonneg_right hKL (ht j)),
    h.2.2.1.trans (mul_le_mul_of_nonneg_right hKL (ht i)),
    h.2.2.2.trans (mul_le_mul_of_nonneg_right hKL (Real.sqrt_nonneg _))⟩

theorem walk_age_bound (t x : I → ℝ) {K : ℝ} (hK : 0 ≤ K)
    {i j : I} (p : (graph t x K).Walk i j) : t i ≤ K^p.length*t j := by
  induction p with
  | nil => simp
  | @cons i k j hadj p ih =>
    calc
      t i ≤ K*t k := hadj.2.1
      _ ≤ K*(K^p.length*t j) := mul_le_mul_of_nonneg_left ih hK
      _ = _ := by simp only [Walk.length_cons,pow_succ]; ring

/-- An edge bound on the literal vertices visited by a walk controls
its endpoint centers by the walk length. -/
theorem walk_center_bound {G : SimpleGraph I} (x : I → ℝ) {i j : I}
    (p : G.Walk i j) (L : ℝ)
    (hedge : ∀ u v, u ∈ p.support → v ∈ p.support → G.Adj u v → |x u-x v| ≤ L) :
    |x i-x j| ≤ (p.length:ℝ)*L := by
  induction p with
  | nil => simp
  | @cons i k j hadj p ih =>
    have hip : i ∈ (Walk.cons hadj p).support := by simp
    have hkp : k ∈ (Walk.cons hadj p).support := by simp [p.start_mem_support]
    have hfirst := hedge i k hip hkp hadj
    have hrest := ih (fun u v hu hv huv => hedge u v
      (p.support_subset_support_cons hadj hu) (p.support_subset_support_cons hadj hv) huv)
    calc
      _ ≤ |x i-x k|+|x k-x j| := abs_sub_le _ _ _
      _ ≤ L+(p.length:ℝ)*L := add_le_add hfirst hrest
      _ = _ := by simp only [Walk.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem reachable_age_bound [Fintype I] (t x : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    {K : ℝ} (hK : 1 ≤ K) {i j : I} (hij : (graph t x K).Reachable i j) :
    t i ≤ K^(Fintype.card I)*t j := by
  obtain ⟨p,hp⟩ := hij.exists_isPath
  exact (walk_age_bound t x (zero_le_one.trans hK) p).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (Nat.le_of_lt hp.length_lt)) (ht j))

theorem reachable_center_bound [Fintype I] (t x : I → ℝ)
    {K T : ℝ} (hK : 0 ≤ K) {i j : I} (hij : (graph t x K).Reachable i j)
    (hT : ∀ v, (graph t x K).Reachable i v → t v ≤ T) :
    |x i-x j| ≤ (Fintype.card I:ℝ)*K*Real.sqrt T := by
  classical
  obtain ⟨p,hp⟩ := hij.exists_isPath
  have hvert (v : I) (hv : v ∈ p.support) : t v ≤ T := hT v (p.takeUntil v hv).reachable
  have hbound := walk_center_bound x p (K*Real.sqrt T) (by
    intro u v hu hv huv
    exact huv.2.2.2.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (max_le (hvert u hu) (hvert v hv))) hK))
  have hlen : (p.length:ℝ) ≤ (Fintype.card I:ℝ) := by exact_mod_cast Nat.le_of_lt hp.length_lt
  exact hbound.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlen
      (mul_nonneg hK (Real.sqrt_nonneg T)))

/-- The actual coherence graphs have stable adjacent reachability
relations among finitely many increasing thresholds. -/
theorem stable_threshold [Fintype I] (t x : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (K : ℕ → ℝ) (hK : Monotone K) :
    ∃ k ≤ (Fintype.card I)^2, ∀ i j,
      (graph t x (K k)).Reachable i j ↔ (graph t x (K (k+1))).Reachable i j := by
  apply FiniteStabilization.monotone_relation_stabilizes
  intro i j k l hkl hij
  exact hij.mono (graph_mono t x ht (hK hkl))

theorem controlled_stable_threshold [Fintype I] (t x : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (F : ℝ → ℝ) :
    ∃ k ≤ (Fintype.card I)^2,
      1 ≤ FiniteStabilization.thresholds F k ∧
      FiniteStabilization.thresholds F k < FiniteStabilization.thresholds F (k+1) ∧
      F (FiniteStabilization.thresholds F k) ≤ FiniteStabilization.thresholds F (k+1) ∧
      ∀ i j, (graph t x (FiniteStabilization.thresholds F k)).Reachable i j ↔
        (graph t x (FiniteStabilization.thresholds F (k+1))).Reachable i j := by
  obtain ⟨k,hk,hstable⟩ := stable_threshold t x ht (FiniteStabilization.thresholds F)
    (FiniteStabilization.thresholds_strictMono F).monotone
  exact ⟨k,hk,FiniteStabilization.thresholds_ge_one F k,
    FiniteStabilization.thresholds_strictMono F (Nat.lt_succ_self k),
    FiniteStabilization.thresholds_dominate F k,hstable⟩

theorem exists_largest_age [Fintype I] (G : SimpleGraph I) (t : I → ℝ) (i : I) :
    ∃ r, G.Reachable i r ∧ ∀ v, G.Reachable i v → t v ≤ t r := by
  classical
  let s := Finset.univ.filter (fun v => G.Reachable i v)
  have hs : s.Nonempty := ⟨i,by simp [s]⟩
  obtain ⟨r,hr,hmax⟩ := Finset.exists_max_image s t hs
  refine ⟨r,by simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hr,?_⟩
  intro v hv
  exact hmax v (by simp [s,hv])

/-- Every actual coherence cluster has a largest-age representative,
with all normalized age and center parameters explicitly bounded. -/
theorem cluster_representative [Fintype I] (t x : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    {K : ℝ} (hK : 1 ≤ K) (i : I) :
    ∃ r, (graph t x K).Reachable i r ∧ ∀ v, (graph t x K).Reachable i v →
      t v ≤ t r ∧ t r ≤ K^(Fintype.card I)*t v ∧
        |x v-x r| ≤ (Fintype.card I:ℝ)*K*Real.sqrt (t r) := by
  obtain ⟨r,hir,hmax⟩ := exists_largest_age (graph t x K) t i
  refine ⟨r,hir,fun v hiv => ⟨hmax v hiv,?_,?_⟩⟩
  · exact reachable_age_bound t x ht hK (hir.symm.trans hiv)
  · have hh := reachable_center_bound t x (zero_le_one.trans hK) (hir.symm.trans hiv)
      (fun w hrw => hmax w (hir.trans hrw))
    simpa only [abs_sub_comm] using hh

/-- At a stable adjacent threshold, representatives of distinct old
clusters cannot be coherent at the larger threshold. -/
theorem representatives_separated (t x : I → ℝ) {K L : ℝ}
    (hstable : ∀ i j, (graph t x K).Reachable i j ↔ (graph t x L).Reachable i j)
    {i j r s : I} (hij : ¬(graph t x K).Reachable i j)
    (hir : (graph t x K).Reachable i r) (hjs : (graph t x K).Reachable j s) :
    ¬(graph t x L).Adj r s := by
  intro hadj
  have hrs := (hstable r s).mpr hadj.reachable
  exact hij (hir.trans (hrs.trans hjs.symm))

end SHE.HeatCoherence
