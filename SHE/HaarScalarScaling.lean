module

public import SHE.HaarConstantJets
public import SHE.RealHaarIntegrand

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE
open MeasureTheory Finset AddCircle CircleHeat
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

theorem haarMass_scale {c l r : ℝ} (hc : 0<c) (hl : 0<l) (hr : 0<r) :
    haarMass (c*l) (c*r)=Real.sqrt c*haarMass l r := by
  unfold haarMass
  have he : (c*l)*(c*r)/(c*l+c*r)=c*(l*r/(l+r)) := by
    field_simp [hc.ne',(add_pos hl hr).ne',mul_ne_zero hc.ne' (add_pos hl hr).ne']
    <;> ring
  rw [he,Real.sqrt_mul hc.le]

theorem haarLeft_scale {c l r : ℝ} (hc : 0<c) (hl : 0<l) (hr : 0<r) :
    haarLeft (c*l) (c*r)=(Real.sqrt c)⁻¹*haarLeft l r := by
  unfold haarLeft
  rw [haarMass_scale hc hl hr]
  calc
    _=(Real.sqrt c/c)*(haarMass l r/l) := by field_simp
    _=_ := by rw [Real.sqrt_div_self]

theorem haarRight_scale {c l r : ℝ} (hc : 0<c) (hl : 0<l) (hr : 0<r) :
    haarRight (c*l) (c*r)=(Real.sqrt c)⁻¹*haarRight l r := by
  unfold haarRight
  rw [haarMass_scale hc hl hr]
  calc
    _=(Real.sqrt c/c)*(-haarMass l r/r) := by field_simp
    _=_ := by rw [Real.sqrt_div_self]

namespace FiniteHaar

theorem totalMass_scale (n : ℕ) (a : Grid n→ℝ) (c : ℝ) :
    totalMass n (fun x => c*a x)=c*totalMass n a := by simp only [totalMass,mul_sum]

theorem detailColumn_scale (n : ℕ) (a : Grid n→ℝ) (ha : ∀ x,0<a x)
    {c : ℝ} (hc : 0<c) (i : DetailIndex n) (x : Grid n) :
    detailColumn n (fun y => c*a y) i x=(Real.sqrt c)⁻¹*detailColumn n a i x := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i) <;> cases x with
    | inl x =>
      first
      | simpa only [detailColumn,Sum.elim_inl,totalMass_scale] using
          haarLeft_scale hc (totalMass_pos n _ (fun x => ha (Sum.inl x)))
            (totalMass_pos n _ (fun x => ha (Sum.inr x)))
      | exact ih _ (fun x => ha (Sum.inl x)) i x
      | simp only [detailColumn,Sum.elim_inl,mul_zero]
    | inr x =>
      first
      | simpa only [detailColumn,Sum.elim_inr,totalMass_scale] using
          haarRight_scale hc (totalMass_pos n _ (fun x => ha (Sum.inl x)))
            (totalMass_pos n _ (fun x => ha (Sum.inr x)))
      | exact ih _ (fun x => ha (Sum.inr x)) i x
      | simp only [detailColumn,Sum.elim_inr,mul_zero]

theorem haarColumn_scale (n : ℕ) (a : Grid n→ℝ) (ha : ∀ x,0<a x)
    {c : ℝ} (hc : 0<c) (i : Option (DetailIndex n)) (x : Grid n) :
    haarColumn n (fun y => c*a y) i x=(Real.sqrt c)⁻¹*haarColumn n a i x := by
  cases i with
  | none => simp only [haarColumn,totalMass_scale,Real.sqrt_mul hc.le,mul_inv_rev]; ring
  | some i => exact detailColumn_scale n a ha hc i x

theorem localAverage_scale (n : ℕ) (f : CircleL2) (c : ℝ) (x : Grid n) :
    localAverage n (c•f) x=c*localAverage n f x := by
  change localAverageFunctional n x (c•f)=c*localAverageFunctional n x f
  exact (localAverageFunctional n x).map_smul c f

theorem cellRestriction_scale (n : ℕ) (f : CircleL2) (c : ℝ) (x : Grid n) :
    cellRestriction n x (c•f)=c•cellRestriction n x f := by
  exact ((cellRestriction n x).restrictScalars ℝ).map_smul c f

/-- Literal positive scalar homogeneity of every actual Haar column.
The basis is unchanged, so both equations keep the same noise coupling. -/
theorem fixedHaarColumn_scale (n : ℕ) (i : Option (DetailIndex n)) (f : CircleL2)
    (hf : ∀ x,0<localAverage n f x) {c : ℝ} (hc : 0<c) :
    fixedHaarColumn n i (c•f)=Real.sqrt c•fixedHaarColumn n i f := by
  have he : localAverage n (c•f)=fun x => c*localAverage n f x := funext (localAverage_scale n f c)
  unfold fixedHaarColumn
  rw [he,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [haarColumn_scale n _ hf hc,cellRestriction_scale,smul_smul,smul_smul]
  congr 1
  have hs : (Real.sqrt c)⁻¹*c=Real.sqrt c := by
    field_simp [(Real.sqrt_pos.mpr hc).ne']
    nlinarith [Real.sq_sqrt hc.le]
  calc
    _=(Real.sqrt c)⁻¹*c*(Real.sqrt ((2^n:ℕ):ℝ)*haarColumn n (localAverage n f) i x) := by ring
    _=_ := by rw [hs]

theorem globalHaarColumn_scale (q : HaarNode) (f : CircleL2)
    (hf : ∀ x,0<localAverage (nodeDepth q) f x) {c : ℝ} (hc : 0<c) :
    globalHaarColumn q (c•f)=Real.sqrt c•globalHaarColumn q f :=
  fixedHaarColumn_scale _ _ f hf hc

theorem globalHaarColumn_scale_elliptic (q : HaarNode) (f : CircleL2)
    {ell M c : ℝ} (hell : 0<ell) (hf : ∀ᵐ x ∂haarAddCircle,ell≤(f x).re ∧ (f x).re≤M)
    (hc : 0<c) : globalHaarColumn q (c•f)=Real.sqrt c•globalHaarColumn q f :=
  globalHaarColumn_scale q f (fun x => hell.trans_le (localAverage_bounds_ae _ f ell M hf x).1) hc

end FiniteHaar
end SHE
