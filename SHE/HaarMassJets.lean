module

public import SHE.HaarColumnBounds
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE
open Set Finset MeasureTheory

def massCoefficient (b : Bool) (z : ℝ × ℝ) : ℝ :=
  if b then haarRight z.1 z.2 else haarLeft z.1 z.2

def massRectangle (m U : ℝ) : Set (ℝ × ℝ) := Icc (m,m) (U,U)

theorem contDiffAt_massCoefficient (b : Bool) (z : ℝ × ℝ) (hz : 0 < z.1 ∧ 0 < z.2)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k (massCoefficient b) z := by
  cases b
  · exact contDiffAt_haarLeft hz.1 hz.2 k
  · exact contDiffAt_haarRight hz.1 hz.2 k

/-- Every order of the actual two-mass coefficient derivatives is
uniform on the elliptic rectangle; the constant has no spatial depth. -/
theorem massJetBound_exists (m U : ℝ) (hm : 0 < m) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : Bool) (z : ℝ × ℝ), z ∈ massRectangle m U →
      ‖iteratedFDeriv ℝ j (massCoefficient b) z‖ ≤ C := by
  have hc (b : Bool) : ContinuousOn (iteratedFDeriv ℝ j (massCoefficient b)) (massRectangle m U) := by
    intro z hz
    exact ((contDiffAt_massCoefficient b z ⟨hm.trans_le hz.1.1, hm.trans_le hz.1.2⟩ (j : WithTop ℕ∞)).continuousAt_iteratedFDeriv
      le_rfl).continuousWithinAt
  obtain ⟨L,hL⟩ := (isCompact_Icc : IsCompact (massRectangle m U)).exists_bound_of_continuousOn (hc false)
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (massRectangle m U)).exists_bound_of_continuousOn (hc true)
  refine ⟨max 1 (max L R), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro b z hz
  cases b
  · exact (hL z hz).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hR z hz).trans ((le_max_right _ _).trans (le_max_right _ _))

def massJetBound (m U : ℝ) (hm : 0 < m) (j : ℕ) : ℝ :=
  (massJetBound_exists m U hm j).choose

theorem massJetBound_pos (m U : ℝ) (hm : 0 < m) (j : ℕ) : 0 < massJetBound m U hm j :=
  (massJetBound_exists m U hm j).choose_spec.1

theorem massJetBound_le (m U : ℝ) (hm : 0 < m) (j : ℕ) (b : Bool) (z : ℝ × ℝ)
    (hz : z ∈ massRectangle m U) : ‖iteratedFDeriv ℝ j (massCoefficient b) z‖ ≤ massJetBound m U hm j :=
  (massJetBound_exists m U hm j).choose_spec.2 b z hz

theorem massRectangle_segment (m U : ℝ) (z w : ℝ × ℝ)
    (hz : z ∈ massRectangle m U) (hw : z + w ∈ massRectangle m U)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z + t • w ∈ massRectangle m U := by
  have hL : z.1 + t * w.1 ∈ Icc m U := by
    simpa only [Prod.fst_add, add_sub_cancel_left, smul_eq_mul] using
      (convex_Icc m U).add_smul_sub_mem ⟨hz.1.1, hz.2.1⟩ ⟨hw.1.1, hw.2.1⟩ ht
  have hR : z.2 + t * w.2 ∈ Icc m U := by
    simpa only [Prod.snd_add, add_sub_cancel_left, smul_eq_mul] using
      (convex_Icc m U).add_smul_sub_mem ⟨hz.1.2, hz.2.2⟩ ⟨hw.1.2, hw.2.2⟩ ht
  exact ⟨⟨hL.1, hR.1⟩, ⟨hL.2, hR.2⟩⟩

/-- Integral Taylor's formula for the genuine local mass coefficient,
at every finite order and along the actual elliptic segment. -/
theorem massCoefficient_taylor (m U : ℝ) (hm : 0 < m) (b : Bool) (j : ℕ) (z w : ℝ × ℝ)
    (hz : z ∈ massRectangle m U) (hw : z + w ∈ massRectangle m U) :
    massCoefficient b (z + w) =
      (∑ k ∈ range (j + 1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k (massCoefficient b) z (fun _ => w)) +
      (j.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, (1 - t) ^ j •
        iteratedFDeriv ℝ (j + 1) (massCoefficient b) (z + t • w) (fun _ => w) := by
  apply map_add_eq_sum_add_integral_iteratedFDeriv
  intro t ht
  have hs := massRectangle_segment m U z w hz hw t ht
  exact contDiffAt_massCoefficient b _ ⟨hm.trans_le hs.1.1, hm.trans_le hs.1.2⟩ _

theorem massCoefficient_taylor_remainder_bound (m U : ℝ) (hm : 0 < m) (b : Bool) (j : ℕ) (z w : ℝ × ℝ)
    (hz : z ∈ massRectangle m U) (hw : z + w ∈ massRectangle m U) :
    ‖massCoefficient b (z + w) -
      ∑ k ∈ range (j + 1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k (massCoefficient b) z (fun _ => w)‖ ≤
      (j.factorial : ℝ)⁻¹ * massJetBound m U hm (j + 1) * ‖w‖ ^ (j + 1) := by
  rw [massCoefficient_taylor m U hm b j z w hz hw, add_sub_cancel_left, norm_smul]
  have hi : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ j •
        iteratedFDeriv ℝ (j + 1) (massCoefficient b) (z + t • w) (fun _ => w)‖ ≤
      massJetBound m U hm (j + 1) * ‖w‖ ^ (j + 1) := by
    have hb : ∀ t ∈ uIoc (0 : ℝ) 1, ‖(1 - t) ^ j •
        iteratedFDeriv ℝ (j + 1) (massCoefficient b) (z + t • w) (fun _ => w)‖ ≤
        massJetBound m U hm (j + 1) * ‖w‖ ^ (j + 1) := by
      intro t ht
      have hti : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨hti.1.le, hti.2⟩
      have hp : ‖(1 - t) ^ j‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [ht'.2])]
        exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
      rw [norm_smul]
      have hj := (iteratedFDeriv ℝ (j + 1) (massCoefficient b) (z + t • w)).le_opNorm (fun _ => w)
      simp only [prod_const, card_univ, Fintype.card_fin] at hj
      have hh := hj.trans (mul_le_mul_of_nonneg_right
        (massJetBound_le m U hm (j + 1) b _ (massRectangle_segment m U z w hz hw t ht')) (by positivity))
      exact (mul_le_mul hp hh (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc
    _ ≤ ‖(j.factorial : ℝ)⁻¹‖ * (massJetBound m U hm (j + 1) * ‖w‖ ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring

namespace FiniteHaar
open AddCircle CircleHeat
local instance haarMassJets_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Actual integral Taylor expansion of every countable physical Haar
column, with no finite-dimensional surrogate or Taylor hypothesis. -/
theorem globalHaarColumn_taylor (q : HaarNode) (f h : CircleL2) (j : ℕ)
    (hf : ∀ x, 0 < localAverage (nodeDepth q) f x)
    (hfh : ∀ x, 0 < localAverage (nodeDepth q) (f + h) x) :
    globalHaarColumn q (f + h) =
      (∑ k ∈ range (j + 1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k (globalHaarColumn q) f (fun _ => h)) +
      (j.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, (1 - t) ^ j •
        iteratedFDeriv ℝ (j + 1) (globalHaarColumn q) (f + t • h) (fun _ => h) := by
  apply map_add_eq_sum_add_integral_iteratedFDeriv
  intro t ht
  apply contDiffAt_globalHaarColumn
  intro x
  have he := congrFun (localAverage_affine (nodeDepth q) f h 1) x
  simp only [one_smul, one_mul] at he
  have hh := hfh x
  rw [he] at hh
  rw [localAverage_affine]
  change 0 < localAverage (nodeDepth q) f x + t * localAverage (nodeDepth q) h x
  by_cases ht1 : t = 1
  · simpa only [ht1, one_mul] using hh
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hp : 0 < (1-t) * localAverage (nodeDepth q) f x := mul_pos (by linarith) (hf x)
    nlinarith [mul_nonneg ht.1 hh.le]

end FiniteHaar
end SHE
