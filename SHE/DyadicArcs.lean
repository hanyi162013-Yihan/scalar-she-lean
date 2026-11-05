module

public import SHE.ArcNegative

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DyadicArcs
open Set MeasureTheory AddCircle CircleHeat FiniteHaar ArcGeometry
local instance dyadicArcs_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem arcValue_interval {a b r : ℝ} (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) (hab : a ≤ b) (hr : r ∈ Ioc (0:ℝ) 1) :
    realArcValue a b r = 1 ↔ a < r ∧ r ≤ b := by
  have hc (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
      ⌈r-c⌉ = (if c < r then (1:ℤ) else 0) := by
    split_ifs with hcr
    · apply Int.ceil_eq_iff.mpr
      norm_num
      constructor <;> linarith [hr.1,hr.2,hc.1,hc.2]
    · apply Int.ceil_eq_iff.mpr
      norm_num
      constructor <;> linarith [hr.1,hr.2,hc.1,hc.2]
  rw [realArcValue,hc a ha,hc b hb]
  by_cases har : a < r <;> by_cases hbr : b < r <;>
    norm_num [har,hbr] <;> linarith

theorem ceil_mod_interval (N : ℕ) [NeZero N] (j : ZMod N) {r : ℝ}
    (hr : r ∈ Ioc (0:ℝ) 1) :
    (((⌈(N:ℝ)*r⌉-1:ℤ):ZMod N)=j) ↔
      (j.val:ℝ)/(N:ℝ) < r ∧ r ≤ ((j.val:ℝ)+1)/(N:ℝ) := by
  have hN : 0 < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlo : (0:ℤ) ≤ ⌈(N:ℝ)*r⌉-1 := by
    have hp : (0:ℤ) < ⌈(N:ℝ)*r⌉ := Int.ceil_pos.mpr (mul_pos hN hr.1)
    omega
  have hhi : ⌈(N:ℝ)*r⌉-1 < (N:ℤ) := by
    have hp : ⌈(N:ℝ)*r⌉ ≤ (N:ℤ) := Int.ceil_le.mpr (by
      push_cast
      nlinarith [hr.2])
    omega
  have hv : ((((⌈(N:ℝ)*r⌉-1:ℤ):ZMod N).val):ℤ)=⌈(N:ℝ)*r⌉-1 := by
    rw [ZMod.val_intCast,Int.emod_eq_of_lt hlo hhi]
  have he : (((⌈(N:ℝ)*r⌉-1:ℤ):ZMod N)=j) ↔ ⌈(N:ℝ)*r⌉=(j.val:ℤ)+1 := by
    constructor
    · intro h
      have hh := congrArg (fun z : ZMod N => (z.val:ℤ)) h
      rw [hv] at hh
      omega
    · intro h
      apply ZMod.val_injective
      have hh : ((((⌈(N:ℝ)*r⌉-1:ℤ):ZMod N).val):ℤ)=(j.val:ℤ) := by rw [hv,h]; omega
      exact_mod_cast hh
  rw [he,Int.ceil_eq_iff]
  push_cast
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · apply (div_lt_iff₀ hN).mpr
      nlinarith
    · apply (le_div_iff₀ hN).mpr
      nlinarith
  · rintro ⟨hl,hu⟩
    have hl' := (div_lt_iff₀ hN).mp hl
    have hu' := (le_div_iff₀ hN).mp hu
    constructor <;> nlinarith

/-- The physical dyadic cell is exactly the right-closed periodic arc,
including the cell boundary convention used by the actual Haar factors. -/
theorem cellSet_eq_arcSet (n : ℕ) (x : Grid n) :
    cellSet n x = arcSet ((gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ))
      (((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ)) := by
  ext y
  let r : ℝ := AddCircle.equivIoc (1:ℝ) 0 y
  have hr : r ∈ Ioc (0:ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIoc (1:ℝ) 0 y).property
  have hN : 0 < (((2^n:ℕ):ℝ)) := by positivity
  have ho : gridOrdinal n x < 2^n := (gridFinEquiv n x).isLt
  have ha : (gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hN).mpr
      exact_mod_cast ho.le
  have hb : ((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hN).mpr
      exact_mod_cast (Nat.succ_le_of_lt ho)
  have hab : (gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ) ≤
      ((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_right _ hN.le
    linarith
  change (((⌈((2^n:ℕ):ℝ)*r⌉-1:ℤ):ZMod (2^n))=gridCellEquiv n x) ↔ _
  rw [ceil_mod_interval (2^n) (gridCellEquiv n x) hr,gridCellEquiv_val]
  change _ ↔ arcValue _ _ y = 1
  have hy : (r:AddCircle (1:ℝ))=y := AddCircle.coe_equivIoc
  rw [← hy,arcValue_coe,arcValue_interval ha hb hab hr]

theorem cellRestriction_eq_arcRestriction (n : ℕ) (x : Grid n) (f : CircleL2) :
    cellRestriction n x f = ArcNegative.restriction
      ((gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ))
      (((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ)) f := by
  apply Lp.ext
  filter_upwards [cellRestriction_ae n x f,ArcNegative.restriction_ae
    ((gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ))
    (((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ)) f] with y hc ha
  rw [hc,ha,cellSet_eq_arcSet]

end SHE.DyadicArcs
