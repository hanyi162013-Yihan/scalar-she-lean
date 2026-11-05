module

public import SHE.Algebra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.JointDefectDomination
variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]

theorem convex_row_norm {u v : C} {B e : ℝ} (he0 : 0≤e) (he1 : e≤1)
    (hu : ‖u‖≤B) (hv : ‖v‖≤B) : ‖v+(1-e) • (u-v)‖≤B := by
  have he : v+(1-e) • (u-v)=e • v+(1-e) • u := by module
  rw [he]
  calc
    _≤‖e • v‖+‖(1-e) • u‖ := norm_add_le _ _
    _=e*‖v‖+(1-e)*‖u‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg he0,abs_of_nonneg (sub_nonneg.mpr he1)]
    _≤e*B+(1-e)*B := add_le_add (mul_le_mul_of_nonneg_left hv he0)
      (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr he1))
    _=B := by ring

/-- A uniform fixed-gap majorant for the actual direct bracket defect.
It follows from convexity of the physical common-Haar rows, retaining
all cross terms rather than bounding them as independent inputs. -/
theorem direct_abs_le {ui uj vi vj : C} {B ei ej : ℝ} (hB : 0≤B)
    (hei : 0≤ei ∧ ei≤1) (hej : 0≤ej ∧ ej≤1)
    (hui : ‖ui‖≤B) (huj : ‖uj‖≤B) (hvi : ‖vi‖≤B) (hvj : ‖vj‖≤B) :
    |(1-ei)*inner ℝ (ui-vi) vj+(1-ej)*inner ℝ vi (uj-vj)+
      (1-ei)*(1-ej)*inner ℝ (ui-vi) (uj-vj)|≤2*B^2 := by
  rw [← SHE.direct_bracket_defect]
  have hwi := convex_row_norm hei.1 hei.2 hui hvi
  have hwj := convex_row_norm hej.1 hej.2 huj hvj
  have hnew : |inner ℝ (vi+(1-ei) • (ui-vi)) (vj+(1-ej) • (uj-vj))|≤B^2 := by
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [mul_le_mul hwi hwj (norm_nonneg _) hB])
  have hold : |inner ℝ vi vj|≤B^2 :=
    (abs_real_inner_le_norm _ _).trans (by nlinarith [mul_le_mul hvi hvj (norm_nonneg _) hB])
  calc
    _ ≤ |inner ℝ (vi+(1-ei) • (ui-vi)) (vj+(1-ej) • (uj-vj))|+
        |inner ℝ vi vj| := by
          simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le
            (inner ℝ (vi+(1-ei) • (ui-vi)) (vj+(1-ej) • (uj-vj))) 0 (inner ℝ vi vj))
    _ ≤ 2*B^2 := by linarith

end SHE.JointDefectDomination
