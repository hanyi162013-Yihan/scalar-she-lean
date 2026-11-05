module

public import SHE.HaarTransformedState

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat CellNegative HaarWeightedHeat
open scoped ContDiff
local instance haarNegativeColumns_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def negativeOutput (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (n : ℕ) : CircleL2 →L[ℝ] CircleL2 :=
  ((scale Λ ρ n) • besselHalf Λ ρ hΛ hρ).restrictScalars ℝ

def negativeState (p : List Bool) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) :
    CircleL2 →L[ℝ] ColumnState CircleL2 := transformedState p (negativeOutput Λ ρ hΛ hρ (p.length+1))

def localNegativeNorm (p : List Bool) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : CircleL2) : ℝ :=
  ‖besselHalf Λ ρ hΛ hρ (cellRestriction (p.length+1) (bottomLeaf p false) v)‖+
    ‖besselHalf Λ ρ hΛ hρ (cellRestriction (p.length+1) (bottomLeaf p true) v)‖

def negativeSlotConstant (ρ : ℝ) : ℝ := max (Real.sqrt (inverseConstant 1 ρ)) 1

theorem negativeState_bounded {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (v : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ M) :
    ‖negativeState p Λ ρ hΛ hρ.le v‖ ≤ cellConstant ρ*M := by
  have hC : 1 ≤ cellConstant ρ := cellConstant_one_le hρhalf
  have hm : M ≤ cellConstant ρ*M := by nlinarith
  have hc (b : Bool) :
      ‖Real.sqrt (((2^(p.length+1):ℕ):ℝ)) • negativeOutput Λ ρ hΛ hρ.le (p.length+1)
        (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ cellConstant ρ*M := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (((2^(p.length+1):ℕ):ℝ)) *
      ‖scale Λ ρ (p.length+1) • besselHalf Λ ρ hΛ hρ.le (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by unfold scale; positivity)]
    have hs := scaled_bessel_cell_le hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) v
    have hb := cellRestriction_bounded_norm (p.length+1) (bottomLeaf p b) v M hM hv
    calc
      _ ≤ Real.sqrt (((2^(p.length+1):ℕ):ℝ))*(cellConstant ρ*‖cellRestriction (p.length+1) (bottomLeaf p b) v‖) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (((2^(p.length+1):ℕ):ℝ))*(cellConstant ρ*(M*(Real.sqrt (((2^(p.length+1):ℕ):ℝ)))⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (zero_le_one.trans hC)) (Real.sqrt_nonneg _)
      _ = _ := by
        have hn : Real.sqrt (((2^(p.length+1):ℕ):ℝ)) ≠ 0 := by positivity
        field_simp
  rw [negativeState,transformedState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
  exact max_le (max_le ((localAverage_bounded_abs _ _ v M hM hv).trans hm)
    ((localAverage_bounded_abs _ _ v M hM hv).trans hm)) (max_le (hc false) (hc true))

theorem negativeState_one_slot {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (v : CircleL2) :
    ‖negativeState p Λ ρ hΛ hρ.le v‖ ≤ negativeSlotConstant ρ*Real.sqrt (((2^(p.length+1):ℕ):ℝ))*
      scale Λ ρ (p.length+1)*localNegativeNorm p Λ ρ hΛ hρ.le v := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  let D := scale Λ ρ (p.length+1)
  let A := negativeSlotConstant ρ
  let R := localNegativeNorm p Λ ρ hΛ hρ.le v
  have hA : 1 ≤ A := le_max_right _ _
  have hD : 0 ≤ D := by dsimp [D,scale]; positivity
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc (b : Bool) : ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ R := by
    cases b
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hm (b : Bool) : |localAverage (p.length+1) v (bottomLeaf p b)| ≤ A*Real.sqrt N*D*R := by
    have hh := localAverage_negative_bound hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) v
    have hcoef : Real.sqrt (inverseConstant 1 ρ) ≤ A := le_max_left _ _
    exact hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg N)) hD)
      (hc b) (norm_nonneg _) (by positivity))
  have hp (b : Bool) :
      ‖Real.sqrt N • negativeOutput Λ ρ hΛ hρ.le (p.length+1)
        (cellRestriction (p.length+1) (bottomLeaf p b) v)‖ ≤ A*Real.sqrt N*D*R := by
    change ‖Real.sqrt N • (D • besselHalf Λ ρ hΛ hρ.le
      (cellRestriction (p.length+1) (bottomLeaf p b) v))‖ ≤ _
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg N),abs_of_nonneg hD]
    have hh := mul_le_mul_of_nonneg_left (hc b) (mul_nonneg (Real.sqrt_nonneg N) hD)
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (mul_nonneg (mul_nonneg (Real.sqrt_nonneg N) hD) hR)]
  rw [negativeState,transformedState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
  exact max_le (max_le (hm false) (hm true)) (max_le (hp false) (hp true))

def negativeColumnConstant (m U : ℝ) (hm : 0 < m) (j : ℕ) (ρ : ℝ) : ℝ :=
  stateJetBound m (cellConstant ρ*U) hm (j+1)*negativeSlotConstant ρ*(cellConstant ρ)^j

/-- Every genuine higher Haar derivative column has the manuscript's
negative one-slot bound. The physical state is rescaled before applying
the finite mass-jet estimate, so no rough coefficient multiplies a
distribution and the mass/mesh scales cancel exactly. -/
theorem globalHaarColumn_jet_negative_one_slot {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i) :
    ‖besselHalf Λ ρ hΛ hρ.le (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) f v)‖ ≤
      negativeColumnConstant m U hm j ρ*Real.sqrt (((2^(p.length+1):ℕ):ℝ))*
        localNegativeNorm p Λ ρ hΛ hρ.le (v 0)*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i) := by
  have hU := elliptic_upper_nonneg f m U hm hf
  have hC := cellConstant_one_le hρhalf
  have hU' : U ≤ cellConstant ρ*U := by nlinarith
  have hp (x : Grid (p.length+1)) : 0 < localAverage (p.length+1) f x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  let z := negativeState p Λ ρ hΛ hρ.le f
  have hz : z.1 ∈ massRectangle m (cellConstant ρ*U) :=
    ⟨⟨(localAverage_bounds_ae _ _ m U hf _).1,(localAverage_bounds_ae _ _ m U hf _).1⟩,
      ⟨(localAverage_bounds_ae _ _ m U hf _).2.trans hU',(localAverage_bounds_ae _ _ m U hf _).2.trans hU'⟩⟩
  have hphys : ‖z.2‖ ≤ cellConstant ρ*U :=
    (norm_snd_le z).trans (negativeState_bounded hΛ hρ hρhalf p f U hU
      (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hf))
  have hnorm := (iteratedFDeriv ℝ (j+1) stateColumn z).le_opNorm
    (fun i => negativeState p Λ ρ hΛ hρ.le (v i))
  have hb := hnorm.trans (mul_le_mul_of_nonneg_right
    (stateColumn_jet_bound m (cellConstant ρ*U) hm (j+1) z hz hphys)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← Finset.mul_prod_erase univ _ (mem_univ (0 : Fin (j+1)))] at hb
  have hprod : (∏ i ∈ univ.erase (0 : Fin (j+1)), ‖negativeState p Λ ρ hΛ hρ.le (v i)‖) ≤
      (cellConstant ρ)^j*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i) := by
    have hh := Finset.prod_le_prod₀ (s := univ.erase (0 : Fin (j+1))) (fun _ _ => norm_nonneg _) (fun i hi =>
      negativeState_bounded hΛ hρ hρhalf p (v i) (M i) (hM i) (hv i (mem_erase.mp hi).1))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_erase_of_mem (mem_univ (0 : Fin (j+1))),
      Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel] using hh
  have hdir := mul_le_mul (negativeState_one_slot hΛ hρ hρhalf p (v 0)) hprod
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by unfold negativeSlotConstant localNegativeNorm scale; positivity)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hdir (stateJetBound_nonneg m (cellConstant ρ*U) hm (j+1)))
  have he := globalHaarColumn_jet_transformed_state p (negativeOutput Λ ρ hΛ hρ.le (p.length+1)) f hp (j+1) v
  have hscale : 0 < scale Λ ρ (p.length+1) := by unfold scale; positivity
  have hleft : ‖iteratedFDeriv ℝ (j+1) stateColumn z (fun i => negativeState p Λ ρ hΛ hρ.le (v i))‖ =
      scale Λ ρ (p.length+1)*‖besselHalf Λ ρ hΛ hρ.le (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) f v)‖ := by
    dsimp only [z,negativeState]
    rw [← he]
    change ‖scale Λ ρ (p.length+1) • besselHalf Λ ρ hΛ hρ.le
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) f v)‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hscale]
  rw [hleft] at hb'
  apply (mul_le_mul_iff_right₀ hscale).mp
  exact hb'.trans_eq (by unfold negativeColumnConstant; ring)

theorem localNegativeNorm_leafPath (n : ℕ) (x : Grid n) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (v : CircleL2) :
    localNegativeNorm (leafPath n x) Λ ρ hΛ hρ v =
      ‖besselHalf Λ ρ hΛ hρ (cellRestriction (n+1) (leafChild n x false) v)‖+
        ‖besselHalf Λ ρ hΛ hρ (cellRestriction (n+1) (leafChild n x true) v)‖ := by
  unfold localNegativeNorm
  rw [leafPath_child_eval (fun k y => ‖besselHalf Λ ρ hΛ hρ (cellRestriction k y v)‖) n x false,
    leafPath_child_eval (fun k y => ‖besselHalf Λ ρ hΛ hρ (cellRestriction k y v)‖) n x true]

theorem exists_sum_localNegativeNorm_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ) (n : ℕ) (v : CircleL2),
      (∑ x : Grid n, localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le v^2) ≤
        C*StepInput.negativeEnergy 1 Λ ρ v := by
  obtain ⟨C,hC,hbound⟩ := DyadicLocalization.exists_cell_localization_bound hρ hρhalf
  refine ⟨2*C,by positivity,?_⟩
  intro Λ hΛ n v
  calc
    _ ≤ ∑ x : Grid n, 2*(‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (n+1) (leafChild n x false) v)‖^2+
        ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (n+1) (leafChild n x true) v)‖^2) := by
      apply sum_le_sum
      intro x _
      rw [localNegativeNorm_leafPath]
      nlinarith [sq_nonneg (‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (n+1) (leafChild n x false) v)‖-
        ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction (n+1) (leafChild n x true) v)‖)]
    _ = 2*∑ y : Grid (n+1), StepInput.negativeEnergy 1 Λ ρ (cellRestriction (n+1) y v) := by
      rw [sum_leafChildren n,mul_sum]
      apply sum_congr rfl
      intro x _
      rw [besselHalf_norm_sq,besselHalf_norm_sq,
        NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ),
        NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    _ ≤ 2*(C*StepInput.negativeEnergy 1 Λ ρ v) := mul_le_mul_of_nonneg_left (hbound Λ hΛ (n+1) v) (by norm_num)
    _ = _ := by ring

/-- The actual negative-input generation bound, uniform in the dyadic
generation, mass parameter and elliptic base field, for every derivative
order. Both local negative norms are summed using the proved fractional
Hardy localization theorem. -/
theorem exists_globalHaarColumn_jet_negative_generation_bound (m U : ℝ) (hm : 0 < m)
    (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ) (n : ℕ) (f : CircleL2),
      (∀ᵐ y ∂haarAddCircle, (f y).im = 0) →
      (∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) →
      ∀ (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i) →
      (∑ x : Grid n, ‖besselHalf Λ ρ hΛ hρ.le
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) f v)‖^2) ≤
        C*(((2^(n+1):ℕ):ℝ))*StepInput.negativeEnergy 1 Λ ρ (v 0)*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_sum_localNegativeNorm_bound hρ hρhalf
  refine ⟨1+(negativeColumnConstant m U hm j ρ)^2*C,by positivity,?_⟩
  intro Λ hΛ n f hfreal hf v M hM hv
  let A := (negativeColumnConstant m U hm j ρ)^2*(((2^(n+1):ℕ):ℝ))*
    (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ StepInput.negativeEnergy 1 Λ ρ (v 0) := by
    rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold NegativeNash.energy
    positivity
  calc
    _ ≤ ∑ x : Grid n, A*localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (v 0)^2 := by
      apply sum_le_sum
      intro x _
      have hh := pow_le_pow_left₀ (norm_nonneg _)
        (globalHaarColumn_jet_negative_one_slot hΛ hρ hρhalf (leafPath n x) f m U hm hfreal hf j v M hM hv) 2
      rw [leafPath_length] at hh
      apply hh.trans_eq
      rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
      dsimp only [A]
      ring
    _ = A*∑ x : Grid n, localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (v 0)^2 := (mul_sum _ _ _).symm
    _ ≤ A*(C*StepInput.negativeEnergy 1 Λ ρ (v 0)) :=
      mul_le_mul_of_nonneg_left (hbound Λ hΛ n (v 0)) hA
    _ ≤ _ := by dsimp only [A]; nlinarith [mul_nonneg (by positivity : 0 ≤ (((2^(n+1):ℕ):ℝ))*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2) hE]

end SHE.FiniteHaar
