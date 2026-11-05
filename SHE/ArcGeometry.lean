module

public import SHE.HaarGeometry

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ArcGeometry
open Set MeasureTheory AddCircle
local instance arcGeometry_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def realArcValue (a b r : ℝ) : ℤ := ⌈r-a⌉-⌈r-b⌉

theorem realArcValue_periodic (a b : ℝ) : Function.Periodic (realArcValue a b) 1 := by
  intro r
  unfold realArcValue
  rw [show r+1-a = (r-a)+1 by ring,show r+1-b = (r-b)+1 by ring,
    Int.ceil_add_one,Int.ceil_add_one]
  norm_num

def arcValue (a b : ℝ) (x : AddCircle (1:ℝ)) : ℤ := (realArcValue_periodic a b).lift x

theorem arcValue_coe (a b r : ℝ) : arcValue a b (r : AddCircle (1:ℝ)) = realArcValue a b r := rfl

def arcSet (a b : ℝ) : Set (AddCircle (1:ℝ)) := {x | arcValue a b x = 1}

theorem measurable_arcValue (a b : ℝ) : Measurable (arcValue a b) := by
  have hm : Measurable (fun x : AddCircle (1:ℝ) => (AddCircle.equivIoc (1:ℝ) 0 x : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (T := (1:ℝ)) 0).measurable_toFun
  have he : arcValue a b = fun x => realArcValue a b (AddCircle.equivIoc (1:ℝ) 0 x) := by
    funext x
    calc
      arcValue a b x = arcValue a b (((AddCircle.equivIoc (1:ℝ) 0 x : ℝ)) : AddCircle (1:ℝ)) :=
        congrArg (arcValue a b) (AddCircle.coe_equivIoc (p := (1:ℝ)) (a := (0:ℝ)) (y := x)).symm
      _ = _ := rfl
  rw [he]
  exact ((hm.sub_const a).ceil).sub ((hm.sub_const b).ceil)

theorem measurableSet_arcSet (a b : ℝ) : MeasurableSet (arcSet a b) :=
  (measurable_arcValue a b) (measurableSet_singleton 1)

theorem ceil_crossing_norm {x z : ℝ} (hz : 0 ≤ z) (hne : ⌈x⌉ ≠ ⌈x+z⌉) :
    ‖(x : AddCircle (1:ℝ))‖ ≤ z := by
  have hle : ⌈x⌉ ≤ ⌈x+z⌉ := Int.ceil_mono (by linarith)
  have hlt : ⌈x⌉ < ⌈x+z⌉ := lt_of_le_of_ne hle hne
  have hcross : (⌈x⌉ : ℝ) < x+z := Int.lt_ceil.mp hlt
  have hx : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have hi : (((⌈x⌉ : ℤ) : ℝ) : AddCircle (1:ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
    exact ⟨⌈x⌉,by simp only [zsmul_eq_mul,mul_one]⟩
  have he : ((x-(⌈x⌉ : ℝ) : ℝ) : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) := by
    rw [QuotientAddGroup.mk_sub,hi,sub_zero]
  calc
    _ = ‖((x-(⌈x⌉ : ℝ) : ℝ) : AddCircle (1:ℝ))‖ := congrArg norm he.symm
    _ ≤ ‖x-(⌈x⌉ : ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ z := by rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hx)]; linarith

/-- A positive translation can change membership in the literal periodic
arc only after reaching one of its two actual endpoints. -/
theorem arc_crossing (a b : ℝ) (x : AddCircle (1:ℝ)) {z : ℝ} (hz : 0 ≤ z)
    (hc : (x ∈ arcSet a b ∧ x+(z : AddCircle (1:ℝ)) ∉ arcSet a b) ∨
      (x ∉ arcSet a b ∧ x+(z : AddCircle (1:ℝ)) ∈ arcSet a b)) :
    dist x (a : AddCircle (1:ℝ)) ≤ z ∨ dist x (b : AddCircle (1:ℝ)) ≤ z := by
  induction x using Quotient.inductionOn with
  | _ r =>
    have hne : realArcValue a b r ≠ realArcValue a b (r+z) := by
      intro he
      have hm : ((r : AddCircle (1:ℝ)) ∈ arcSet a b) ↔
          ((r : AddCircle (1:ℝ))+(z : AddCircle (1:ℝ)) ∈ arcSet a b) := by
        change realArcValue a b r = 1 ↔ arcValue a b ((r : AddCircle (1:ℝ))+(z : AddCircle (1:ℝ))) = 1
        rw [← QuotientAddGroup.mk_add,arcValue_coe,he]
      rcases hc with hc | hc
      · exact hc.2 (hm.mp hc.1)
      · exact hc.1 (hm.mpr hc.2)
    by_cases ha : ⌈r-a⌉ = ⌈r+z-a⌉
    · right
      have hb : ⌈r-b⌉ ≠ ⌈r+z-b⌉ := by
        intro hb
        apply hne
        unfold realArcValue
        rw [ha,hb]
      have hh := ceil_crossing_norm hz (by simpa only [show r+z-b = (r-b)+z by ring] using hb)
      simpa only [dist_eq_norm,← QuotientAddGroup.mk_sub] using hh
    · left
      have hh := ceil_crossing_norm hz (by simpa only [show r+z-a = (r-a)+z by ring] using ha)
      simpa only [dist_eq_norm,← QuotientAddGroup.mk_sub] using hh

end SHE.ArcGeometry
