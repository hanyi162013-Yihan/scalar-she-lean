module

public import SHE.HaarDifferentiability

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE

theorem hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun s : ℝ => a + s * b) b 0 := by
  simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- Logarithmic differentiation of the actual positive square root,
expressed without introducing logarithms into the column formula. -/
theorem hasDerivAt_sqrt_normalized {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f (f a * d) a) (hpos : 0 < f a) :
    HasDerivAt (fun s => Real.sqrt (f s)) (Real.sqrt (f a) / 2 * d) a := by
  convert hf.sqrt hpos.ne' using 1
  have hs : Real.sqrt (f a) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring

def haarLeftDifferential (l r L R : ℝ) : ℝ :=
  haarLeft l r / 2 * (R / r - L / l - (L + R) / (l + r))

def haarRightDifferential (l r L R : ℝ) : ℝ :=
  haarRight l r / 2 * (L / l - R / r - (L + R) / (l + r))

theorem hasDerivAt_haarMass_affine {l r : ℝ} (hl : 0 < l) (hr : 0 < r) (L R : ℝ) :
    HasDerivAt (fun s : ℝ => haarMass (l + s * L) (r + s * R))
      (haarMass l r / 2 * (L / l + R / r - (L + R) / (l + r))) 0 := by
  have hq : HasDerivAt (fun s : ℝ =>
      (l + s * L) * (r + s * R) / ((l + s * L) + (r + s * R)))
      ((l * r / (l + r)) * (L / l + R / r - (L + R) / (l + r))) 0 := by
    convert ((hasDerivAt_affine l L).mul (hasDerivAt_affine r R)).div
      ((hasDerivAt_affine l L).add (hasDerivAt_affine r R)) (by simpa using (add_pos hl hr).ne') using 1
    simp only [Pi.mul_apply, Pi.add_apply, zero_mul, add_zero]
    field_simp [hl.ne', hr.ne', (add_pos hl hr).ne']
  have hs := hasDerivAt_sqrt_normalized
    (f := fun s : ℝ => (l + s * L) * (r + s * R) / ((l + s * L) + (r + s * R)))
    (a := 0) (d := L / l + R / r - (L + R) / (l + r))
    (by simpa only [zero_mul, add_zero] using hq)
    (by simpa only [zero_mul, add_zero] using (div_pos (mul_pos hl hr) (add_pos hl hr)))
  simpa only [zero_mul, add_zero, haarMass] using hs

/-- The exact left-child derivative printed in the local Haar formula. -/
theorem hasDerivAt_haarLeft_affine {l r : ℝ} (hl : 0 < l) (hr : 0 < r) (L R : ℝ) :
    HasDerivAt (fun s : ℝ => haarLeft (l + s * L) (r + s * R))
      (haarLeftDifferential l r L R) 0 := by
  have hd := (hasDerivAt_haarMass_affine hl hr L R).div (hasDerivAt_affine l L)
    (by simpa using hl.ne')
  convert hd using 1
  · rfl
  · simp only [zero_mul, add_zero, haarLeftDifferential, haarLeft]
    field_simp [hl.ne', hr.ne', (add_pos hl hr).ne']
    ring

/-- The exact right-child derivative printed in the local Haar formula. -/
theorem hasDerivAt_haarRight_affine {l r : ℝ} (hl : 0 < l) (hr : 0 < r) (L R : ℝ) :
    HasDerivAt (fun s : ℝ => haarRight (l + s * L) (r + s * R))
      (haarRightDifferential l r L R) 0 := by
  have hd := (hasDerivAt_haarMass_affine hl hr L R).neg.div (hasDerivAt_affine r R)
    (by simpa using hr.ne')
  convert hd using 1
  · rfl
  · simp only [Pi.neg_apply, zero_mul, add_zero, haarRightDifferential, haarRight]
    field_simp [hl.ne', hr.ne', (add_pos hl hr).ne']
    ring

theorem haar_differential_cancellation {l r : ℝ} (hl : 0 < l) (hr : 0 < r) (L R : ℝ) :
    L * haarLeft l r + l * haarLeftDifferential l r L R +
      (R * haarRight l r + r * haarRightDifferential l r L R) = 0 := by
  unfold haarLeftDifferential haarRightDifferential haarLeft haarRight
  field_simp [hl.ne', hr.ne', (add_pos hl hr).ne']
  ring

namespace FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
local instance haarColumnFormula_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem totalMass_affine (n : ℕ) (c h : Grid n → ℝ) (s : ℝ) :
    totalMass n (fun x => c x + s * h x) = totalMass n c + s * totalMass n h := by
  simp only [totalMass, sum_add_distrib, mul_sum]

def detailColumnDifferential : (n : ℕ) → (Grid n → ℝ) → (Grid n → ℝ) → DetailIndex n → Grid n → ℝ
  | 0, _, _, i => nomatch i
  | n + 1, c, h, Sum.inl _ =>
      Sum.elim
        (fun _ => haarLeftDifferential (totalMass n (fun x => c (Sum.inl x)))
          (totalMass n (fun x => c (Sum.inr x))) (totalMass n (fun x => h (Sum.inl x)))
          (totalMass n (fun x => h (Sum.inr x))))
        (fun _ => haarRightDifferential (totalMass n (fun x => c (Sum.inl x)))
          (totalMass n (fun x => c (Sum.inr x))) (totalMass n (fun x => h (Sum.inl x)))
          (totalMass n (fun x => h (Sum.inr x))))
  | n + 1, c, h, Sum.inr (Sum.inl i) =>
      Sum.elim (detailColumnDifferential n (fun x => c (Sum.inl x)) (fun x => h (Sum.inl x)) i) (fun _ => 0)
  | n + 1, c, h, Sum.inr (Sum.inr i) =>
      Sum.elim (fun _ => 0) (detailColumnDifferential n (fun x => c (Sum.inr x)) (fun x => h (Sum.inr x)) i)

def haarColumnDifferential (n : ℕ) (c h : Grid n → ℝ) : Option (DetailIndex n) → Grid n → ℝ
  | none => fun _ => -(totalMass n h) / (2 * (Real.sqrt (totalMass n c)) ^ 3)
  | some i => detailColumnDifferential n c h i

theorem hasDerivAt_detailColumn_affine (n : ℕ) (c h : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : DetailIndex n) (x : Grid n) :
    HasDerivAt (fun s : ℝ => detailColumn n (fun y => c y + s * h y) i x)
      (detailColumnDifferential n c h i x) 0 := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with i | (i | i)
    · cases x with
      | inl x =>
        simpa only [detailColumn, detailColumnDifferential, Sum.elim_inl, totalMass_affine] using
          hasDerivAt_haarLeft_affine (totalMass_pos n _ (fun y => hc (Sum.inl y)))
            (totalMass_pos n _ (fun y => hc (Sum.inr y)))
            (totalMass n (fun y => h (Sum.inl y))) (totalMass n (fun y => h (Sum.inr y)))
      | inr x =>
        simpa only [detailColumn, detailColumnDifferential, Sum.elim_inr, totalMass_affine] using
          hasDerivAt_haarRight_affine (totalMass_pos n _ (fun y => hc (Sum.inl y)))
            (totalMass_pos n _ (fun y => hc (Sum.inr y)))
            (totalMass n (fun y => h (Sum.inl y))) (totalMass n (fun y => h (Sum.inr y)))
    · cases x with
      | inl x => exact ih _ _ (fun y => hc (Sum.inl y)) i x
      | inr x => exact hasDerivAt_const 0 0
    · cases x with
      | inl x => exact hasDerivAt_const 0 0
      | inr x => exact ih _ _ (fun y => hc (Sum.inr y)) i x

theorem hasDerivAt_haarColumn_affine (n : ℕ) (c h : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : Option (DetailIndex n)) (x : Grid n) :
    HasDerivAt (fun s : ℝ => haarColumn n (fun y => c y + s * h y) i x)
      (haarColumnDifferential n c h i x) 0 := by
  cases i with
  | some i => exact hasDerivAt_detailColumn_affine n c h hc i x
  | none =>
    have hm := totalMass_pos n c hc
    have hd := ((hasDerivAt_affine (totalMass n c) (totalMass n h)).sqrt
      (by simpa using hm.ne')).inv (by simpa using (Real.sqrt_pos.mpr hm).ne')
    convert hd using 1
    · funext s
      simp only [haarColumn, totalMass_affine]
      rfl
    · simp only [haarColumnDifferential, zero_mul, add_zero]
      field_simp

theorem localAverage_affine (n : ℕ) (f h : CircleL2) (s : ℝ) :
    localAverage n (f + s • h) = fun x => localAverage n f x + s * localAverage n h x := by
  funext x
  unfold localAverage
  change _ * (inner ℂ _ (f + (s : ℂ) • h)).re = _
  rw [inner_add_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

def fixedColumnDifferential (n : ℕ) (i : Option (DetailIndex n)) (f h : CircleL2) : CircleL2 :=
  ∑ x : Grid n, (
    (Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumnDifferential n (localAverage n f) (localAverage n h) i x) •
      cellRestriction n x f +
    (Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (localAverage n f) i x) • cellRestriction n x h)

/-- The genuine derivative is the local product rule: one unaveraged
direction term and one differentiated child-mass term. -/
theorem hasDerivAt_fixedColumnDifferential (n : ℕ) (i : Option (DetailIndex n)) (f h : CircleL2)
    (hf : ∀ x, 0 < localAverage n f x) :
    HasDerivAt (fun s : ℝ => fixedHaarColumn n i (f + s • h))
      (fixedColumnDifferential n i f h) 0 := by
  unfold fixedHaarColumn fixedColumnDifferential
  apply HasDerivAt.fun_sum
  intro x hx
  have hc := (hasDerivAt_haarColumn_affine n (localAverage n f) (localAverage n h) hf i x).const_mul
    (Real.sqrt (((2 ^ n : ℕ) : ℝ)))
  have hl : HasDerivAt (fun s : ℝ => f + s • h) h 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add f
  have hr := ((cellRestriction n x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hl
  change HasDerivAt (fun s : ℝ => cellRestriction n x (f + s • h)) (cellRestriction n x h) 0 at hr
  have hc' : HasDerivAt (fun s : ℝ => Real.sqrt (((2 ^ n : ℕ) : ℝ)) *
      haarColumn n (localAverage n (f + s • h)) i x)
      (Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumnDifferential n (localAverage n f) (localAverage n h) i x) 0 := by
    simpa only [localAverage_affine] using hc
  convert hc'.smul hr using 1
  simp only [zero_smul, add_zero]
  exact add_comm _ _

theorem columnDifferential_local_formula (q : HaarNode) (f h : CircleL2)
    (hf : ∀ x, 0 < localAverage (nodeDepth q) f x) :
    columnDifferential q f h = fixedColumnDifferential (nodeDepth q)
      (nodeMode (nodeDepth q) q le_rfl) f h :=
  (hasDerivAt_globalHaarColumn_line q f h hf).unique
    (hasDerivAt_fixedColumnDifferential (nodeDepth q) _ f h hf)

end FiniteHaar

end SHE
