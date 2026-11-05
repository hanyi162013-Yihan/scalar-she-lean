module

public import SHE.HaarNegativeConstant
public import SHE.HeatDominatedOperator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HaarWeightedHeat NegativeNash
open scoped ContDiff
local instance haarSeparatedConstant_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem constant_jet_transformed_bound (T : CircleL2 →L[ℝ] CircleL2)
    (hT : ∀ z,‖T z‖ ≤ ‖z‖) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle,(f y).im=0)
    (hf : ∀ᵐ y ∂haarAddCircle,m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (hv : ∀ i,i ≠ 0 → ∀ᵐ y ∂haarAddCircle,‖v i y‖ ≤ M i)
    (S : ℝ) (hS : 0 ≤ S) (havg : |localAverage 0 (v 0) ()| ≤ S) (hslot : ‖T (v 0)‖ ≤ S) :
    ‖T (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖ ≤
      stateJetBound (m/2) U (by positivity) (j+1)*S*(∏ i ∈ univ.erase (0 : Fin (j+1)),M i) := by
  let z := transformedConstantState T f
  have hU := elliptic_upper_nonneg f m U hm hf
  have ha := localAverage_bounds_ae 0 f m U hf ()
  have hp : 0 < localAverage 0 f () := hm.trans_le ha.1
  have hs : z.1 ∈ massRectangle (m/2) U := by
    rw [show z=transformedConstantState T f by rfl,transformedConstantState_apply]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have hphys : ‖z.2‖ ≤ U := by
    rw [show z=transformedConstantState T f by rfl,transformedConstantState_apply,Prod.norm_def]
    exact max_le ((hT f).trans (circle_norm_le_ae_bound f U
      (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hf))) (by simpa using hU)
  have hnorm := (iteratedFDeriv ℝ (j+1) stateColumn z).le_opNorm (fun i => transformedConstantState T (v i))
  have hbound := hnorm.trans (mul_le_mul_of_nonneg_right
    (stateColumn_jet_bound (m/2) U (by positivity) (j+1) z hs hphys)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← Finset.mul_prod_erase univ _ (mem_univ (0 : Fin (j+1)))] at hbound
  have hprod : (∏ i ∈ univ.erase (0 : Fin (j+1)),‖transformedConstantState T (v i)‖) ≤
      ∏ i ∈ univ.erase (0 : Fin (j+1)),M i :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i hi =>
      (transformedConstantState_contraction T hT (v i)).trans
        (circle_norm_le_ae_bound (v i) (M i) (hv i (mem_erase.mp hi).1)))
  have hstate : ‖transformedConstantState T (v 0)‖ ≤ S := by
    rw [transformedConstantState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
    have ha' : ‖localAverage 0 (v 0) ()/2‖ ≤ S := by
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    exact max_le (max_le ha' ha') (max_le hslot (by simpa using hS))
  rw [globalHaarColumn_constant_jet_transformed_state T f hp]
  exact hbound.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul hstate hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hS)
    (stateJetBound_nonneg (m/2) U (by positivity) (j+1))).trans_eq (by ring))

/-- Universal mass-normalization transfer for the actual constant jet.
Both hypotheses are ordinary operator estimates, proved below for the
separated literal heat/operator composition. -/
theorem constant_jet_negative_of_mass_bounds {Λ ρ τ K : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (hτ : 1 ≤ τ) (hK : 0 ≤ K) (W : CircleL2 →L[ℝ] CircleL2)
    (hmass : ∀ z,Λ^ρ*‖W z‖^2 ≤ K^2*‖z‖^2)
    (hnegative : ∀ z,‖W z‖^2 ≤ 2*K^2*τ*energy Λ ρ z)
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle,(f y).im=0)
    (hf : ∀ᵐ y ∂haarAddCircle,m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (hv : ∀ i,i ≠ 0 → ∀ᵐ y ∂haarAddCircle,‖v i y‖ ≤ M i) :
    ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖^2 ≤
      2*(stateJetBound (m/2) U (by positivity) (j+1))^2*K^2*τ*energy Λ ρ (v 0)*
        (∏ i ∈ univ.erase (0 : Fin (j+1)),M i)^2 := by
  have hp : 0 < Λ^ρ := Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _
  by_cases hK0 : K=0
  · have hz := hnegative (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)
    simpa only [hK0,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_mul] using hz
  have hKp : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
  let T : CircleL2 →L[ℝ] CircleL2 := (Real.sqrt (Λ^ρ)/K) • W
  have hTsq (z : CircleL2) : ‖T z‖^2=(Λ^ρ/K^2)*‖W z‖^2 := by
    change ‖(Real.sqrt (Λ^ρ)/K) • W z‖^2=_
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,Real.sq_sqrt hp.le]
  have hT (z : CircleL2) : ‖T z‖ ≤ ‖z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hTsq,div_mul_eq_mul_div]
    exact (div_le_iff₀ (sq_pos_of_pos hKp)).mpr ((hmass z).trans_eq (by ring))
  let R := 2*Λ^ρ*τ*energy Λ ρ (v 0)
  have hE : 0 ≤ energy Λ ρ (v 0) := by unfold energy; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have havg : |localAverage 0 (v 0) ()| ≤ Real.sqrt R := by
    have hh := localAverage_zero_negative_sq hΛ hρ (v 0)
    have ht := mul_le_mul_of_nonneg_left hτ (mul_nonneg hp.le hE)
    have hs := Real.sq_sqrt hR
    dsimp only [R] at hs
    nlinarith [Real.sqrt_nonneg R,abs_nonneg (localAverage 0 (v 0) ())]
  have hslot : ‖T (v 0)‖ ≤ Real.sqrt R := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg R)).mp
    rw [hTsq,Real.sq_sqrt hR]
    have hh := mul_le_mul_of_nonneg_left (hnegative (v 0)) (div_nonneg hp.le (sq_nonneg K))
    exact hh.trans_eq (by dsimp only [R]; field_simp)
  have hb := constant_jet_transformed_bound T hT f m U hm hfreal hf j v M hv
    (Real.sqrt R) (Real.sqrt_nonneg R) havg hslot
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [hTsq] at hs
  simp only [mul_pow,Real.sq_sqrt hR] at hs
  rw [div_mul_eq_mul_div] at hs
  have hh := (div_le_iff₀ (sq_pos_of_pos hKp)).mp hs
  apply (mul_le_mul_iff_right₀ hp).mp
  exact hh.trans_eq (by dsimp only [R]; ring)

def separatedHeat (Λ ρ δ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (A : CircleL2 →L[ℂ] CircleL2) : CircleL2 →L[ℝ] CircleL2 :=
  ((besselHalf Λ ρ hΛ hρ).comp (A.comp (heat δ))).restrictScalars ℝ

theorem separatedHeat_mass_negative {Λ ρ δ K : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) (A : CircleL2 →L[ℂ] CircleL2)
    (hA : ∀ z,‖A z‖ ≤ K*‖z‖) (v : CircleL2) :
    Λ^ρ*‖separatedHeat Λ ρ δ hΛ hρ A v‖^2 ≤ K^2*‖v‖^2 ∧
      ‖separatedHeat Λ ρ δ hΛ hρ A v‖^2 ≤ 2*K^2*δ^(-ρ)*energy Λ ρ v := by
  have hp : 0 < Λ^ρ := Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _
  have hm := CellNegative.energy_mass_le (zero_lt_one.trans_le hΛ) hρ (A (heat δ v))
  rw [← besselHalf_norm_sq Λ ρ hΛ hρ] at hm
  change Λ^ρ*‖separatedHeat Λ ρ δ hΛ hρ A v‖^2 ≤ ‖A (heat δ v)‖^2 at hm
  have ha := pow_le_pow_left₀ (norm_nonneg _) (hA (heat δ v)) 2
  rw [mul_pow] at ha
  constructor
  · exact hm.trans (ha.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (heat_contraction δ v) 2) (sq_nonneg K)))
  · have hn := NegativeL2Heat.heat_norm_sq_negative hΛ hρ hρ1 hδ v
    have hE : 0 ≤ energy Λ ρ v := by unfold energy; positivity
    have hb := hm.trans (ha.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg K)))
    have hτ : 1 ≤ δ^(-ρ) := by
      simpa using Real.rpow_le_rpow_of_nonpos hδ hδ1 (neg_nonpos.mpr hρ)
    have hΛρ : 1 ≤ Λ^ρ := Real.one_le_rpow hΛ hρ
    have hs : Λ^ρ+δ^(-ρ) ≤ 2*Λ^ρ*δ^(-ρ) := by
      have h1 := mul_le_mul_of_nonneg_left hτ hp.le
      have h2 := mul_le_mul_of_nonneg_right hΛρ (Real.rpow_nonneg hδ.le (-ρ))
      nlinarith only [h1,h2]
    have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (sq_nonneg K) hE)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hb,hh]

/-- Constant mode of the genuine separated two-scale operator. The
operator A may be any bounded real-output heat-dominated integral
operator; its actual Schur bound is proved independently. -/
theorem globalHaarColumn_constant_jet_separated_negative {Λ ρ δ K : ℝ}
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 0 ≤ K) (A : CircleL2 →L[ℂ] CircleL2) (hA : ∀ z,‖A z‖ ≤ K*‖z‖)
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle,(f y).im=0)
    (hf : ∀ᵐ y ∂haarAddCircle,m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (hv : ∀ i,i ≠ 0 → ∀ᵐ y ∂haarAddCircle,‖v i y‖ ≤ M i) :
    ‖separatedHeat Λ ρ δ hΛ hρ A (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖^2 ≤
      2*(stateJetBound (m/2) U (by positivity) (j+1))^2*K^2*δ^(-ρ)*energy Λ ρ (v 0)*
        (∏ i ∈ univ.erase (0 : Fin (j+1)),M i)^2 := by
  have hτ : 1 ≤ δ^(-ρ) := by
    simpa using Real.rpow_le_rpow_of_nonpos hδ hδ1 (neg_nonpos.mpr hρ)
  exact constant_jet_negative_of_mass_bounds hΛ hρ hτ hK (separatedHeat Λ ρ δ hΛ hρ A)
    (fun z => (separatedHeat_mass_negative hΛ hρ hρ1 hδ hδ1 hK A hA z).1)
    (fun z => (separatedHeat_mass_negative hΛ hρ hρ1 hδ hδ1 hK A hA z).2)
    f m U hm hfreal hf j v M hv

end SHE.FiniteHaar
