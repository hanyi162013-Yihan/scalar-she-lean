module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CircleCut
open MeasureTheory Set Metric Finset

def margin (q : ℕ) : ℝ := 1/(4*((q:ℝ)+1))

theorem margin_pos (q : ℕ) : 0 < margin q := by unfold margin; positivity

/-- A unit circle has a cut uniformly separated from any prescribed
finite family of centers. This uses its actual Haar volume. -/
theorem exists_separated_cut (q : ℕ) (a : Fin q → UnitAddCircle) :
    ∃ c : UnitAddCircle,∀ i,margin q ≤ dist c (a i) := by
  classical
  let B : Set UnitAddCircle := ⋃ i,closedBall (a i) (margin q)
  have hm : volume B ≤ ENNReal.ofReal ((q:ℝ)*(2*margin q)) := by
    calc
      volume B ≤ ∑' i,volume (closedBall (a i) (margin q)) := measure_iUnion_le _
      _ ≤ ∑' _i : Fin q,ENNReal.ofReal (2*margin q) := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [AddCircle.volume_closedBall]
        exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = _ := by simp only [tsum_fintype,sum_const,card_univ,Fintype.card_fin,
        nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg q)]
  have hsmall : (q:ℝ)*(2*margin q) < 1 := by
    unfold margin
    have hd : 0 < 4*((q:ℝ)+1) := by positivity
    have he : (q:ℝ)*(2*(1/(4*((q:ℝ)+1)))) = (2*(q:ℝ))/(4*((q:ℝ)+1)) := by ring
    rw [he,div_lt_iff₀ hd]
    linarith [show 0 ≤ (q:ℝ) by positivity]
  have hne : B ≠ Set.univ := by
    intro he
    rw [he,UnitAddCircle.measure_univ] at hm
    exact (ENNReal.ofReal_lt_one.mpr hsmall).not_ge hm
  obtain ⟨c,hc⟩ := (Set.ne_univ_iff_exists_notMem B).mp hne
  refine ⟨c,fun i => le_of_lt ?_⟩
  have hi : c ∉ closedBall (a i) (margin q) := fun h => hc (mem_iUnion.mpr ⟨i,h⟩)
  simpa only [mem_closedBall,not_le] using hi

theorem antipodal_norm {x : ℝ} (hx : |x| ≤ 1/2) :
    ‖((x+1/2:ℝ):UnitAddCircle)‖ = 1/2-|x| := by
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  by_cases h : x ≤ 0
  · have hb : |x+1/2| ≤ |(1:ℝ)|/2 := by rw [abs_one,abs_of_nonneg (by linarith)]; linarith
    rw [(AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr hb,
      abs_of_nonneg (by linarith),abs_of_nonpos h]
    ring
  · have hx0 : 0 ≤ x := (not_le.mp h).le
    have he : ((x+1/2:ℝ):UnitAddCircle) = ((x-1/2:ℝ):UnitAddCircle) := by
      have hr : x+1/2 = x-1/2+1 := by ring
      rw [hr,AddCircle.coe_add]
      simp
    have hb : |x-1/2| ≤ |(1:ℝ)|/2 := by rw [abs_one,abs_of_nonpos (by linarith)]; linarith
    rw [he,(AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr hb,
      abs_of_nonpos (by linarith),abs_of_nonneg hx0]
    ring

/-- Rotate all centers by one common circle point and choose actual real
lifts uniformly inside the fundamental interval. -/
theorem exists_interior_lifts (q : ℕ) (a : Fin q → UnitAddCircle) :
    ∃ c : UnitAddCircle,∃ b : Fin q → ℝ,
      (∀ i,(b i:UnitAddCircle)+c = a i) ∧
      ∀ i,|b i| ≤ 1/2-margin q := by
  obtain ⟨s,hs⟩ := exists_separated_cut q a
  let c : UnitAddCircle := s+((1/2:ℝ):UnitAddCircle)
  let b (i : Fin q) : ℝ := AddCircle.equivIco 1 (-(1/2:ℝ)) (a i-c)
  have hb (i : Fin q) : (b i:UnitAddCircle) = a i-c := AddCircle.coe_equivIco
  have hba (i : Fin q) : |b i| ≤ 1/2 := by
    have hh := (AddCircle.equivIco 1 (-(1/2:ℝ)) (a i-c)).property
    exact abs_le.mpr ⟨hh.1,by linarith [hh.2]⟩
  refine ⟨c,b,fun i => by rw [hb]; abel,fun i => ?_⟩
  have he : ((b i+1/2:ℝ):UnitAddCircle) = a i-s := by
    rw [AddCircle.coe_add,hb]
    dsimp only [c]
    abel
  have hh := antipodal_norm (hba i)
  rw [he] at hh
  have hd : margin q ≤ ‖a i-s‖ := by simpa only [dist_eq_norm,norm_sub_rev] using hs i
  linarith

end SHE.CircleCut
