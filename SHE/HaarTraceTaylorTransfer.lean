module

public import SHE.HaarUnifiedNegative

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
local instance haarTraceTaylorTransfer_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem globalColumnTaylorRemainder_map_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (W : CircleL2 →L[ℝ] E)
    (q : HaarNode) (f h : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle,m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle,m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U) (j : ℕ) :
    W (globalColumnTaylorRemainder q f h j) = (j.factorial:ℝ)⁻¹ •
      ∫ r in (0:ℝ)..1,(1-r)^j • W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h)) := by
  have hp (x : Grid (nodeDepth q)) : 0 < localAverage (nodeDepth q) f x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hp' (x : Grid (nodeDepth q)) : 0 < localAverage (nodeDepth q) (f+h) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hfh x).1
  unfold globalColumnTaylorRemainder
  rw [globalHaarColumn_taylor q f h j hp hp',add_sub_cancel_left,map_smul]
  congr 1
  have hc : ContinuousOn (fun r : ℝ => (1-r)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h)) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow j).smul
      (continuousOn_column_jet_segment q f h m U hm hf hfh (j+1) (fun _ => h))
  rw [← W.intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one)]
  apply intervalIntegral.integral_congr
  intro r _
  exact W.map_smul _ _

/-- A general deterministic transfer from an actual higher-column trace
on a genuine elliptic segment to its actual integral Taylor remainder.
It uses finite Hilbert products before taking the countable limit. -/
theorem global_taylor_trace_transfer {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (W : CircleL2 →L[ℝ] E)
    (f h : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle,m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle,m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U)
    (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (htrace : ∀ r ∈ Icc (0:ℝ) 1,
      Summable (fun q : HaarNode => ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h))‖^2) ∧
      (∑' q : HaarNode,‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h))‖^2) ≤ C) :
    Summable (fun q : HaarNode => ‖W (globalColumnTaylorRemainder q f h j)‖^2) ∧
      (∑' q : HaarNode,‖W (globalColumnTaylorRemainder q f h j)‖^2) ≤ (j.factorial:ℝ)⁻¹^2*C := by
  let F : ℝ → HaarNode → E := fun r q => (1-r)^j •
    W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h))
  have hc (q : HaarNode) : ContinuousOn (fun r => F r q) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow j).smul
      (W.continuous.comp_continuousOn (continuousOn_column_jet_segment q f h m U hm hf hfh (j+1) (fun _ => h)))
  have hb (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      Summable (fun q => ‖F r q‖^2) ∧ (∑' q,‖F r q‖^2) ≤ C := by
    have hj := htrace r hr
    have hp : ‖(1-r)^j‖^2 ≤ 1 := by
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg (by linarith [hr.2])]
      have hh := pow_le_one₀ (by linarith [hr.2] : 0 ≤ 1-r) (by linarith [hr.1]) (n := j)
      nlinarith [pow_nonneg (by linarith [hr.2] : 0 ≤ 1-r) j]
    have heF (q : HaarNode) : ‖F r q‖^2 = ‖(1-r)^j‖^2*
        ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h))‖^2 := by
      dsimp only [F]
      rw [norm_smul,mul_pow]
    refine ⟨(hj.1.mul_left (‖(1-r)^j‖^2)).congr (fun q => (heF q).symm),?_⟩
    simp only [heF,tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left hj.2 (sq_nonneg _)).trans (by nlinarith only [mul_le_mul_of_nonneg_right hp hC])
  have hi := TraceIntegral.square_trace F C hC hc hb
  have he (q : HaarNode) : ‖W (globalColumnTaylorRemainder q f h j)‖^2 =
      (j.factorial:ℝ)⁻¹^2*‖∫ r in (0:ℝ)..1,F r q‖^2 := by
    rw [globalColumnTaylorRemainder_map_integral W q f h m U hm hf hfh j,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  refine ⟨(hi.1.mul_left ((j.factorial:ℝ)⁻¹^2)).congr (fun q => (he q).symm),?_⟩
  simp only [he,tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hi.2 (sq_nonneg _)

end SHE.FiniteHaar
