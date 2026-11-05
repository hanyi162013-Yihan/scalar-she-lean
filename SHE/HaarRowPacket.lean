module

public import SHE.CellRow

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat CellNegative HaarWeightedHeat CellRow
open scoped ContDiff
local instance haarRowPacket_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def rowScale (n : ℕ) (L : ℝ) : ℝ := (Real.sqrt (((2^n:ℕ):ℝ)))^3/L
def scaledRow (n : ℕ) (L : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : CircleL2 →L[ℝ] ℂ :=
  rowScale n L • (row u).restrictScalars ℝ
def rowState (p : List Bool) (L : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : CircleL2 →L[ℝ] ColumnState ℂ :=
  transformedState p (scaledRow (p.length+1) L u)
def rowSlotConstant (ρ : ℝ) : ℝ := max (Real.sqrt (inverseConstant 1 ρ))
  (Real.sqrt (SmoothCellSobolev.packetConstant ρ))

theorem rowScale_positive (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < rowScale n L := by
  unfold rowScale
  positivity

theorem rowScale_mul (n : ℕ) {L : ℝ} (hL : 0 < L) :
    rowScale n L*(L/(((2^n:ℕ):ℝ))) = Real.sqrt (((2^n:ℕ):ℝ)) := by
  have hN : 0 < (((2^n:ℕ):ℝ)) := by positivity
  have hs := Real.sq_sqrt hN.le
  unfold rowScale
  field_simp
  nlinarith [hs]

theorem rowState_bounded (p : List Bool) (u : C(AddCircle (1:ℝ),ℂ)) {L : ℝ} (hL : 0 < L)
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (v : CircleL2) (M : ℝ) (hM : 0 ≤ M) (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ M) :
    ‖rowState p L u v‖ ≤ 2*M := by
  have hp (b : Bool) : ‖Real.sqrt (((2^(p.length+1):ℕ):ℝ)) •
      scaledRow (p.length+1) L u (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ 2*M := by
    change ‖Real.sqrt (((2^(p.length+1):ℕ):ℝ)) • (rowScale (p.length+1) L •
      row u (cellRestriction (p.length+1) (bottomLeaf p b) v))‖ ≤ _
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos (rowScale_positive _ hL)]
    have hh := mul_le_mul_of_nonneg_left (CellRow.row_bounded (bottomLeaf p b) u L hL.le (hu b) v M hM hv)
      (mul_nonneg (Real.sqrt_nonneg (((2^(p.length+1):ℕ):ℝ))) (rowScale_positive (p.length+1) hL).le)
    rw [← mul_assoc]
    apply hh.trans_eq
    have hs := Real.sq_sqrt (by positivity : 0 ≤ (((2^(p.length+1):ℕ):ℝ)))
    have hfour : (Real.sqrt (((2^(p.length+1):ℕ):ℝ)))^4 = (((2^(p.length+1):ℕ):ℝ))^2 := by
      nlinarith [congrArg (fun r : ℝ => r^2) hs]
    unfold rowScale
    field_simp
    rw [hfour]
    ring
  rw [rowState,transformedState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
  have hm : M ≤ 2*M := by linarith
  exact max_le (max_le ((localAverage_bounded_abs _ _ v M hM hv).trans hm)
    ((localAverage_bounded_abs _ _ v M hM hv).trans hm)) (max_le (hp false) (hp true))

theorem rowState_one_slot {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (u : C(AddCircle (1:ℝ),ℂ)) {L : ℝ} (hL : 0 < L)
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (hlip : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ∀ w ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y-u w‖ ≤ L*dist y w)
    (v : CircleL2) :
    ‖rowState p L u v‖ ≤ rowSlotConstant ρ*Real.sqrt (((2^(p.length+1):ℕ):ℝ))*
      scale Λ ρ (p.length+1)*localNegativeNorm p Λ ρ hΛ hρ.le v := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  let D := scale Λ ρ (p.length+1)
  let R := localNegativeNorm p Λ ρ hΛ hρ.le v
  have hD : 0 ≤ D := by dsimp [D,scale]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hslot : 0 ≤ rowSlotConstant ρ := le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hc (b : Bool) : ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ R := by
    cases b
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hm (b : Bool) : |localAverage (p.length+1) v (bottomLeaf p b)| ≤ rowSlotConstant ρ*Real.sqrt N*D*R := by
    have hh := localAverage_negative_bound hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) v
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg N)) hD) (hc b) (norm_nonneg _) (by positivity))
  have hp (b : Bool) : ‖Real.sqrt N • scaledRow (p.length+1) L u
      (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ rowSlotConstant ρ*Real.sqrt N*D*R := by
    change ‖Real.sqrt N • (rowScale (p.length+1) L • row u (cellRestriction (p.length+1) (bottomLeaf p b) v))‖ ≤ _
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg N),abs_of_pos (rowScale_positive _ hL)]
    have hh := mul_le_mul_of_nonneg_left (CellRow.row_negative hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) u L hL.le (hu b) (hlip b) v)
      (mul_nonneg (Real.sqrt_nonneg N) (rowScale_positive (p.length+1) hL).le)
    have he : Real.sqrt N*rowScale (p.length+1) L*(Real.sqrt (SmoothCellSobolev.packetConstant ρ)*L*
        (Real.sqrt N)⁻¹^3*D*‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (p.length+1) (bottomLeaf p b) v)‖) =
        Real.sqrt (SmoothCellSobolev.packetConstant ρ)*Real.sqrt N*D*
          ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ := by
      dsimp only [rowScale,N]
      field_simp
    rw [← mul_assoc]
    apply hh.trans
    rw [he]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg N)) hD)
      (hc b) (norm_nonneg _) (by positivity)
  rw [rowState,transformedState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
  exact max_le (max_le (hm false) (hm true)) (max_le (hp false) (hp true))

def rowPacketConstant (m U : ℝ) (hm : 0 < m) (j : ℕ) (ρ : ℝ) : ℝ :=
  stateJetBound m (2*U) hm (j+1)*rowSlotConstant ρ*(2:ℝ)^j

/-- An all-order negative-input packet for every actual centered
spatial row satisfying the proved local amplitude/Lipschitz criterion.
This is directly applicable to the actual Gaussian heat row. -/
theorem globalHaarColumn_jet_row_packet {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (u : C(AddCircle (1:ℝ),ℂ)) {L : ℝ} (hL : 0 < L)
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (hlip : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ∀ w ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y-u w‖ ≤ L*dist y w)
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i) :
    ‖row u (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) f v)‖ ≤
      rowPacketConstant m U hm j ρ*(L/(((2^(p.length+1):ℕ):ℝ)))*scale Λ ρ (p.length+1)*
        localNegativeNorm p Λ ρ hΛ hρ.le (v 0)*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i) := by
  have hU := elliptic_upper_nonneg f m U hm hf
  have hp (x : Grid (p.length+1)) : 0 < localAverage (p.length+1) f x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  let z := rowState p L u f
  have hz : z.1 ∈ massRectangle m (2*U) :=
    ⟨⟨(localAverage_bounds_ae _ _ m U hf _).1,(localAverage_bounds_ae _ _ m U hf _).1⟩,
      ⟨(localAverage_bounds_ae _ _ m U hf _).2.trans (by linarith),(localAverage_bounds_ae _ _ m U hf _).2.trans (by linarith)⟩⟩
  have hphys : ‖z.2‖ ≤ 2*U := (norm_snd_le z).trans
    (rowState_bounded p u hL hu f U hU (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hf))
  have hn := (iteratedFDeriv ℝ (j+1) stateColumn z).le_opNorm (fun i => rowState p L u (v i))
  have hb := hn.trans (mul_le_mul_of_nonneg_right (stateColumn_jet_bound m (2*U) hm (j+1) z hz hphys)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← Finset.mul_prod_erase univ _ (mem_univ (0 : Fin (j+1)))] at hb
  have hprod : (∏ i ∈ univ.erase (0 : Fin (j+1)), ‖rowState p L u (v i)‖) ≤
      (2:ℝ)^j*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i) := by
    have hh := Finset.prod_le_prod₀ (s := univ.erase (0 : Fin (j+1))) (fun _ _ => norm_nonneg _) (fun i hi =>
      rowState_bounded p u hL hu (v i) (M i) (hM i) (hv i (mem_erase.mp hi).1))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_erase_of_mem (mem_univ (0 : Fin (j+1))),
      Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel] using hh
  have hdir := mul_le_mul (rowState_one_slot hΛ hρ hρhalf p u hL hu hlip (v 0)) hprod
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by unfold rowSlotConstant scale localNegativeNorm; positivity)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hdir (stateJetBound_nonneg m (2*U) hm (j+1)))
  have he := globalHaarColumn_jet_transformed_state p (scaledRow (p.length+1) L u) f hp (j+1) v
  have hleft : ‖iteratedFDeriv ℝ (j+1) stateColumn z (fun i => rowState p L u (v i))‖ =
      rowScale (p.length+1) L*‖row u (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) f v)‖ := by
    dsimp only [z,rowState]
    rw [← he]
    change ‖rowScale (p.length+1) L • row u (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) f v)‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (rowScale_positive _ hL)]
  rw [hleft] at hb'
  apply (mul_le_mul_iff_right₀ (rowScale_positive (p.length+1) hL)).mp
  apply hb'.trans_eq
  have hs := rowScale_mul (p.length+1) hL
  unfold rowPacketConstant
  rw [show rowScale (p.length+1) L *
      (stateJetBound m (2*U) hm (j+1)*rowSlotConstant ρ*2^j*(L/(((2^(p.length+1):ℕ):ℝ)))*scale Λ ρ (p.length+1)*
        localNegativeNorm p Λ ρ hΛ hρ.le (v 0)*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)) =
      stateJetBound m (2*U) hm (j+1)*rowSlotConstant ρ*2^j*(rowScale (p.length+1) L*(L/(((2^(p.length+1):ℕ):ℝ))))*scale Λ ρ (p.length+1)*
        localNegativeNorm p Λ ρ hΛ hρ.le (v 0)*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i) by ring,hs]
  ring

end SHE.FiniteHaar
