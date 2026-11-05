module

public import SHE.HaarRealSpace
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE

theorem contDiffAt_haarLeft {l r : ℝ} (hl : 0 < l) (hr : 0 < r)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k (fun p : ℝ × ℝ => haarLeft p.1 p.2) (l,r) := by
  have h : ContDiffAt ℝ k (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 + p.2)) (l,r) :=
    (contDiffAt_fst.mul contDiffAt_snd).div (contDiffAt_fst.add contDiffAt_snd) (by positivity)
  exact (h.sqrt (by positivity)).div contDiffAt_fst hl.ne'

theorem contDiffAt_haarRight {l r : ℝ} (hl : 0 < l) (hr : 0 < r)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k (fun p : ℝ × ℝ => haarRight p.1 p.2) (l,r) := by
  have h : ContDiffAt ℝ k (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 + p.2)) (l,r) :=
    (contDiffAt_fst.mul contDiffAt_snd).div (contDiffAt_fst.add contDiffAt_snd) (by positivity)
  exact (h.sqrt (by positivity)).neg.div contDiffAt_snd hr.ne'

namespace FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
local instance haarDifferentiability_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem contDiff_totalMass (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (totalMass n) := by
  apply ContDiff.sum
  intro x hx
  exact contDiff_apply ℝ (fun _ : Grid n => ℝ) x

theorem contDiffAt_detailColumn (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : DetailIndex n) (x : Grid n) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (fun a => detailColumn n a i x) c := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    have hL : ContDiff ℝ k (fun a : Grid (n+1) → ℝ => fun y : Grid n => a (Sum.inl y)) :=
      contDiff_pi.mpr (fun y => contDiff_apply ℝ (fun _ : Grid (n+1) => ℝ) (Sum.inl y))
    have hR : ContDiff ℝ k (fun a : Grid (n+1) → ℝ => fun y : Grid n => a (Sum.inr y)) :=
      contDiff_pi.mpr (fun y => contDiff_apply ℝ (fun _ : Grid (n+1) => ℝ) (Sum.inr y))
    have hmL := (contDiff_totalMass n k).comp hL
    have hmR := (contDiff_totalMass n k).comp hR
    rcases i with i | (i | i)
    · cases x with
      | inl x =>
        exact (contDiffAt_haarLeft (totalMass_pos n _ (fun y => hc (Sum.inl y)))
          (totalMass_pos n _ (fun y => hc (Sum.inr y))) k).comp c (hmL.prodMk hmR).contDiffAt
      | inr x =>
        exact (contDiffAt_haarRight (totalMass_pos n _ (fun y => hc (Sum.inl y)))
          (totalMass_pos n _ (fun y => hc (Sum.inr y))) k).comp c (hmL.prodMk hmR).contDiffAt
    · cases x with
      | inl x =>
        change ContDiffAt ℝ k (fun a => detailColumn n (fun y => a (Sum.inl y)) i x) c
        exact (ih _ (fun y => hc (Sum.inl y)) i x).comp c hL.contDiffAt
      | inr x => exact contDiffAt_const
    · cases x with
      | inl x => exact contDiffAt_const
      | inr x =>
        change ContDiffAt ℝ k (fun a => detailColumn n (fun y => a (Sum.inr y)) i x) c
        exact (ih _ (fun y => hc (Sum.inr y)) i x).comp c hR.contDiffAt

theorem contDiffAt_haarColumn (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : Option (DetailIndex n)) (x : Grid n) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (fun a => haarColumn n a i x) c := by
  cases i with
  | none =>
    exact ((contDiff_totalMass n k).contDiffAt.sqrt (totalMass_pos n c hc).ne').inv
      (Real.sqrt_pos.mpr (totalMass_pos n c hc)).ne'
  | some i => exact contDiffAt_detailColumn n c hc i x k

theorem contDiff_localAverage (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (localAverage n : CircleL2 → Grid n → ℝ) := by
  apply contDiff_pi.mpr
  intro x
  unfold localAverage
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp
    (contDiff_const.inner ℂ contDiff_id))

/-- Every actual finite dyadic column is infinitely Fréchet smooth on
the open domain where its finitely many local averages are positive. -/
theorem contDiffAt_fixedHaarColumn (n : ℕ) (i : Option (DetailIndex n)) (f : CircleL2)
    (hf : ∀ x, 0 < localAverage n f x) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (fixedHaarColumn n i) f := by
  unfold fixedHaarColumn
  apply ContDiffAt.sum
  intro x hx
  have hc := (contDiffAt_haarColumn n (localAverage n f) hf i x k).comp f
    (contDiff_localAverage n k).contDiffAt
  exact (contDiffAt_const.mul hc).smul ((cellRestriction n x).restrictScalars ℝ).contDiff.contDiffAt

theorem contDiffAt_globalHaarColumn (q : HaarNode) (f : CircleL2)
    (hf : ∀ x, 0 < localAverage (nodeDepth q) f x) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (globalHaarColumn q) f :=
  contDiffAt_fixedHaarColumn (nodeDepth q) _ f hf k

def columnDifferential (q : HaarNode) (f : CircleL2) : CircleL2 →L[ℝ] CircleL2 :=
  fderiv ℝ (globalHaarColumn q) f

theorem hasFDerivAt_globalHaarColumn (q : HaarNode) (f : CircleL2)
    (hf : ∀ x, 0 < localAverage (nodeDepth q) f x) :
    HasFDerivAt (globalHaarColumn q) (columnDifferential q f) f :=
  ((contDiffAt_globalHaarColumn q f hf 1).differentiableAt (by norm_num)).hasFDerivAt

theorem hasDerivAt_globalHaarColumn_line (q : HaarNode) (f h : CircleL2)
    (hf : ∀ x, 0 < localAverage (nodeDepth q) f x) :
    HasDerivAt (fun s : ℝ => globalHaarColumn q (f + s • h)) (columnDifferential q f h) 0 := by
  have hl : HasDerivAt (fun s : ℝ => f + s • h) h 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add f
  have hd : HasFDerivAt (globalHaarColumn q) (columnDifferential q f) (f + (0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using hasFDerivAt_globalHaarColumn q f hf
  exact hd.comp_hasDerivAt 0 hl

end FiniteHaar
end SHE
