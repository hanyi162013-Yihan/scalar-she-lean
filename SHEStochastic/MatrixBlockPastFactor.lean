module

public import SHEStochastic.MatrixBlockNaturalFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixBlockPastFactor
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixBlockNaturalFiltration
open scoped NNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0)

theorem terminal_history (s : ℝ≥0) (hs : H ≤ s) (x : MatrixLocalBlockChain.Space (n := n) H) :
    CanonicalStateDriverFiltration.history H s x=x := by
  have hc : min (s : ℝ) (H : ℝ)=(H : ℝ) := min_eq_right hs
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change x.1 (CanonicalFutureStateDriver.stopTime (CanonicalStateDriverFiltration.clock H s) t)=x.1 t
    congr 1
    apply Subtype.ext
    change min t.val (min (s : ℝ) (H : ℝ))=t.val
    rw [hc,min_eq_left t.property.2]
  · funext i
    apply ContinuousMap.ext
    intro t
    change x.2 i (CanonicalFutureStateDriver.stopTime (CanonicalStateDriverFiltration.clock H s) t)=x.2 i t
    congr 1
    apply Subtype.ext
    change min t.val (min (s : ℝ) (H : ℝ))=t.val
    rw [hc,min_eq_left t.property.2]

/-- Reconstruct the physical past from all completed blocks and one
stopped current block. It is constant in every later coordinate. -/
def assemble (j : ℕ) (s : ℝ≥0)
    (z : ((i : Finset.Iic j) → MatrixLocalBlockChain.Space (n := n) H)×MatrixLocalBlockChain.Space (n := n) H) :
    MatrixGlobalBlockPath.Space (n := n) H := fun k =>
  if hk : k≤j then z.1 ⟨k,Finset.mem_Iic.mpr hk⟩ else
    if k=j+1 ∧ 0<s then z.2 else 0

theorem assemble_measurable (j : ℕ) (s : ℝ≥0) : Measurable (assemble (n := n) H j s) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k≤j
  · simpa only [assemble,dif_pos hk,Function.comp_def] using
      (measurable_pi_apply (⟨k,Finset.mem_Iic.mpr hk⟩ : Finset.Iic j)).comp
        (measurable_fst : Measurable (fun z : ((i : Finset.Iic j) → MatrixLocalBlockChain.Space (n := n) H)×
          MatrixLocalBlockChain.Space (n := n) H => z.1))
  · by_cases he : k=j+1 ∧ 0<s
    · simpa only [assemble,dif_neg hk,if_pos he] using
        (measurable_snd : Measurable (fun z : ((i : Finset.Iic j) → MatrixLocalBlockChain.Space (n := n) H)×
          MatrixLocalBlockChain.Space (n := n) H => z.2))
    · simpa only [assemble,dif_neg hk,if_neg he] using
        (measurable_const (a := (0 : MatrixLocalBlockChain.Space (n := n) H)))

/-- Exact factorization of the global physical past. This is pointwise,
including exceptional sequences with nonmatching state endpoints. -/
theorem history_eq (hH : 0<H) (j : ℕ) (s : ℝ≥0) (hs : s≤H)
    (p : MatrixGlobalBlockPath.Space (n := n) H) :
    history H (((j+1 : ℕ) : ℝ≥0)*H+s) p=
      assemble H j s (Preorder.frestrictLe j p,
        CanonicalStateDriverFiltration.history H s (p (j+1))) := by
  funext k
  by_cases hk : k≤j
  · have hk' : (k : ℝ≥0)<((j+1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.lt_succ_of_le hk
    have hkt : (k : ℝ≥0)*H<((j+1 : ℕ) : ℝ≥0)*H+s :=
      (mul_lt_mul_of_pos_right hk' hH).trans_le (le_add_of_nonneg_right bot_le)
    have htime : H≤(((j+1 : ℕ) : ℝ≥0)*H+s)-(k : ℝ≥0)*H := by
      apply le_tsub_of_add_le_right
      have hk₀ : (k : ℝ≥0)≤(j : ℝ≥0) := by exact_mod_cast hk
      have hh := mul_le_mul_of_nonneg_right hk₀ H.coe_nonneg
      push_cast
      nlinarith
    simp only [history,if_pos (Or.inl hkt),assemble,dif_pos hk]
    exact terminal_history H _ htime (p k)
  · by_cases he : k=j+1
    · subst k
      by_cases hp : 0<s
      · have hact : ((j+1 : ℕ) : ℝ≥0)*H<((j+1 : ℕ) : ℝ≥0)*H+s := lt_add_of_pos_right _ hp
        simp only [history,if_pos (Or.inl hact),add_tsub_cancel_left,assemble,dif_neg hk,
          true_and,if_pos hp]
      · have hz : s=0 := le_antisymm (le_of_not_gt hp) bot_le
        subst s
        simp [history,assemble,hk]
    · have hkj : j+2≤k := by omega
      have hk' : ((j+2 : ℕ) : ℝ≥0)≤(k : ℝ≥0) := by exact_mod_cast hkj
      have hh := mul_le_mul_of_nonneg_right hk' H.coe_nonneg
      have htime : ((j+1 : ℕ) : ℝ≥0)*H+s≤(k : ℝ≥0)*H := by push_cast at hh ⊢;nlinarith
      have hn : ¬((k : ℝ≥0)*H<((j+1 : ℕ) : ℝ≥0)*H+s ∨ k=0) := by
        rintro (h | h)
        · exact (not_lt_of_ge htime) h
        · omega
      simp only [history,if_neg hn,assemble,dif_neg hk,he,false_and,if_false]

/-- The physical past sigma algebra is contained in the old-prefix
and current-local-past sigma algebra used by the continuation theorem. -/
theorem past_le (hH : 0<H) (j : ℕ) (s : ℝ≥0) (hs : s≤H) :
    filtration (n := n) H (((j+1 : ℕ) : ℝ≥0)*H+s) ≤
      MeasurableSpace.comap (fun p : MatrixGlobalBlockPath.Space (n := n) H =>
        (Preorder.frestrictLe j p,CanonicalStateDriverFiltration.history H s (p (j+1)))) inferInstance := by
  let g := fun p : MatrixGlobalBlockPath.Space (n := n) H =>
    (Preorder.frestrictLe j p,CanonicalStateDriverFiltration.history H s (p (j+1)))
  have he : history H (((j+1 : ℕ) : ℝ≥0)*H+s)=assemble H j s ∘ g :=
    funext (history_eq H hH j s hs)
  change MeasurableSpace.comap (history H _) inferInstance≤MeasurableSpace.comap g inferInstance
  rw [he,←MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (assemble_measurable H j s).comap_le

/-- Inside the first block no later block is exposed, including at
the right endpoint. -/
theorem initial_history (s : ℝ≥0) (hs : s≤H) (p : MatrixGlobalBlockPath.Space (n := n) H) :
    history H s p=(fun j => if j=0 then CanonicalStateDriverFiltration.history H s (p 0) else 0) := by
  funext j
  by_cases hj : j=0
  · subst j
    simp [history]
  · have hj1 : (1 : ℝ≥0)≤(j : ℝ≥0) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have htime : s≤(j : ℝ≥0)*H := hs.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hj1 (show (0 : ℝ≥0)≤H from bot_le))
    simp only [history,if_neg (not_or.mpr ⟨not_lt_of_ge htime,hj⟩),if_neg hj]

def initialAssemble (x : MatrixLocalBlockChain.Space (n := n) H) : MatrixGlobalBlockPath.Space (n := n) H :=
  fun j => if j=0 then x else 0

theorem initialAssemble_measurable : Measurable (initialAssemble (n := n) H) := by
    apply Measurable.of_eval
    intro j
    by_cases hj : j=0
    · simp only [initialAssemble,if_pos hj]
      exact measurable_id
    · simpa only [initialAssemble,if_neg hj] using (measurable_const (a := (0 : MatrixLocalBlockChain.Space (n := n) H)))

theorem initial_past_le (s : ℝ≥0) (hs : s≤H) :
    filtration (n := n) H s≤MeasurableSpace.comap
      (fun p : MatrixGlobalBlockPath.Space (n := n) H => CanonicalStateDriverFiltration.history H s (p 0)) inferInstance := by
  have hEq : history H s=initialAssemble H ∘ (fun p : MatrixGlobalBlockPath.Space (n := n) H =>
      CanonicalStateDriverFiltration.history H s (p 0)) := funext (initial_history H s hs)
  change MeasurableSpace.comap (history H s) inferInstance≤_
  rw [hEq,←MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (initialAssemble_measurable H).comap_le

end SHEStochastic.MatrixBlockPastFactor
