module

public import SHE.HaarConstantJets
public import SHE.HaarNegativeCoarse
public import SHE.HaarTransformedState

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HaarWeightedHeat NegativeNash Filter Topology
open scoped ContDiff
local instance haarNegativeConstant_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transformedConstantState (T : CircleL2 →L[ℝ] E) : CircleL2 →L[ℝ] ColumnState E :=
  (((1/2:ℝ) • localAverageFunctional 0 ()).prod
    ((1/2:ℝ) • localAverageFunctional 0 ())).prod (T.prod 0)

theorem transformedConstantState_apply (T : CircleL2 →L[ℝ] E) (f : CircleL2) :
    transformedConstantState T f = ((localAverage 0 f ()/2,localAverage 0 f ()/2),(T f,0)) := by
  simp only [transformedConstantState,ContinuousLinearMap.prod_apply,smul_apply,
    localAverageFunctional_apply,smul_eq_mul,zero_apply]
  congr 2 <;> ring

theorem globalHaarColumn_constant_jet_transformed_state (T : CircleL2 →L[ℝ] E)
    (f : CircleL2) (hf : 0 < localAverage 0 f ()) (j : ℕ) (v : Fin j → CircleL2) :
    T (iteratedFDeriv ℝ j (globalHaarColumn none) f v) =
      iteratedFDeriv ℝ j stateColumn (transformedConstantState T f)
        (fun i => transformedConstantState T (v i)) := by
  have hp : transformedConstantState T f ∈ statePositive := by
    rw [transformedConstantState_apply]
    exact ⟨by change 0 < localAverage 0 f ()/2; positivity,
      by change 0 < localAverage 0 f ()/2; positivity⟩
  have hfun : stateColumn ∘ transformedConstantState T =ᶠ[𝓝 f] T ∘ globalHaarColumn none := by
    have hc : Continuous (fun z : CircleL2 => localAverage 0 z ()) := (localAverageFunctional 0 ()).continuous
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hf] with z hz
    simp only [Function.comp_apply,transformedConstantState_apply,stateColumn,massCoefficient,
      Bool.false_eq_true,↓reduceIte,smul_zero,add_zero,globalHaarColumn_constant_formula]
    rw [haarLeft_half_equal hz,map_smul]
  have he := (transformedConstantState T).iteratedFDerivWithin_comp_right
    (fun z hz => (contDiffAt_stateColumn z hz ∞).contDiffWithinAt)
    isOpen_statePositive.uniqueDiffOn
    (isOpen_statePositive.preimage (transformedConstantState T).continuous).uniqueDiffOn
    hp (i := j) (by simp : (j : WithTop ℕ∞) ≤ ∞)
  have hbase : ContDiffAt ℝ j (globalHaarColumn none) f := by
    apply contDiffAt_globalHaarColumn none f
    intro x
    change Grid 0 at x
    exact Subsingleton.elim x () ▸ hf
  have hleft := T.iteratedFDeriv_comp_left hbase (i := j) le_rfl
  have hcomp : ContDiffAt ℝ j (stateColumn ∘ transformedConstantState T) f :=
    (contDiffAt_stateColumn _ hp j).comp f (transformedConstantState T).contDiff.contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
      (isOpen_statePositive.preimage (transformedConstantState T).continuous).uniqueDiffOn hcomp hp,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      (contDiffAt_stateColumn _ hp j) hp] at he
  rw [(hfun.iteratedFDeriv ℝ j).eq_of_nhds,hleft] at he
  exact congrArg (fun A => A v) he

theorem localAverage_zero_eq_fourier (v : CircleL2) :
    localAverage 0 v () = (fourierCoeff v 0).re := by
  unfold localAverage
  simp only [pow_zero,Nat.cast_one,one_mul]
  have he : cellIndicator 0 ()=fourierBasis 0 := by
    apply Lp.ext
    filter_upwards [cellIndicator_ae 0 (),coeFn_fourierLp 2 (0:ℤ)] with y hy hf
    rw [coe_fourierBasis]
    rw [hy,hf]
    have hy0 : y ∈ cellSet 0 () := by
      change cellIndex 0 y=gridCellEquiv 0 ()
      letI : Subsingleton (ZMod (2^0)) := ZMod.subsingleton_iff.mpr (by norm_num)
      exact Subsingleton.elim _ _
    simp [hy0,fourier_zero]
  change (inner ℂ (cellIndicator 0 ()) v).re = _
  rw [he,← fourierBasis_repr,HilbertBasis.repr_apply_apply]

theorem localAverage_zero_negative_sq {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : CircleL2) :
    |localAverage 0 v ()|^2 ≤ Λ^ρ*energy Λ ρ v := by
  have he := (energy_summable (zero_lt_one.trans_le hΛ) hρ v).le_tsum
    (0:ℤ) (fun k _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hp : 0 < Λ^ρ := Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _
  have hm := mul_le_mul_of_nonneg_left he hp.le
  simp only [Int.cast_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hm
  rw [← mul_assoc,← Real.rpow_add (zero_lt_one.trans_le hΛ),add_neg_cancel,
    Real.rpow_zero,one_mul] at hm
  rw [localAverage_zero_eq_fourier]
  exact (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2).trans hm

theorem weightedHeat_mass_sq {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) (v : CircleL2) :
    Λ^ρ*‖weightedHeat Λ ρ t hΛ hρ b B hb v‖^2 ≤ B^2*‖v‖^2 := by
  have hm := CellNegative.energy_mass_le (zero_lt_one.trans_le hΛ) hρ
    (CircleMultiplier.operator b B hb (heat t v))
  change Λ^ρ*‖besselHalf Λ ρ hΛ hρ (CircleMultiplier.operator b B hb (heat t v))‖^2 ≤ _
  rw [besselHalf_norm_sq]
  apply hm.trans
  have hh := (CircleMultiplier.multiply_norm_le b B hb (heat t v)).trans
    (mul_le_mul_of_nonneg_left (heat_contraction t v) hB)
  simpa only [mul_pow,CircleMultiplier.operator,LinearMap.mkContinuous_apply,
    CircleMultiplier.multiplyLinear,LinearMap.coe_mk,AddHom.coe_mk] using
    pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem weightedHeat_negative_sq {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) (v : CircleL2) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb v‖^2 ≤ 2*B^2*t^(-(1/2:ℝ))*energy Λ ρ v := by
  have hΛ0 := zero_lt_one.trans_le hΛ
  have hK : 1 ≤ Λ^ρ := Real.one_le_rpow hΛ hρ.le
  have hP : 1 ≤ t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have htρ : t^(-ρ) ≤ t^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hE : 0 ≤ energy Λ ρ v := by unfold energy; positivity
  have hm := CellNegative.energy_mass_le hΛ0 hρ.le (CircleMultiplier.operator b B hb (heat t v))
  have hz := pow_le_pow_left₀ (norm_nonneg _)
    (CircleMultiplier.multiply_norm_le b B hb (heat t v)) 2
  rw [mul_pow] at hz
  have hh := (NegativeL2Heat.heat_norm_sq_negative hΛ hρ.le (by linarith : ρ ≤ 1) ht v)
  have hbound := hm.trans (hz.trans (mul_le_mul_of_nonneg_left hh (sq_nonneg B)))
  have hscale : Λ^ρ+t^(-ρ) ≤ 2*Λ^ρ*t^(-(1/2:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hΛ0.le ρ)
    have h2 := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg ht.le (-(1/2:ℝ)))
    nlinarith only [htρ,h1,h2]
  have hfinal : Λ^ρ*energy Λ ρ (CircleMultiplier.operator b B hb (heat t v)) ≤
      Λ^ρ*(2*B^2*t^(-(1/2:ℝ))*energy Λ ρ v) := by
    have hh' := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ B^2*energy Λ ρ v)
    nlinarith only [hbound,hh']
  rw [← besselHalf_norm_sq Λ ρ hΛ hρ.le] at hfinal
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hΛ0 ρ)).mp
  exact hfinal.trans_eq (by ring)

def normalizedConstantOutput (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) : CircleL2 →L[ℝ] CircleL2 :=
  (Real.sqrt (Λ^ρ)/B) • (weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ

theorem normalizedConstantOutput_sq {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) (v : CircleL2) :
    ‖normalizedConstantOutput Λ ρ t hΛ hρ b B hb v‖^2 =
      (Λ^ρ/B^2)*‖weightedHeat Λ ρ t hΛ hρ b B hb v‖^2 := by
  change ‖(Real.sqrt (Λ^ρ)/B) • weightedHeat Λ ρ t hΛ hρ b B hb v‖^2 = _
  simp only [
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans_le hΛ).le ρ)]

theorem normalizedConstantOutput_contraction {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hB : 0 < B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) (v : CircleL2) :
    ‖normalizedConstantOutput Λ ρ t hΛ hρ b B hb v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalizedConstantOutput_sq]
  have hm := weightedHeat_mass_sq (t := t) hΛ hρ b B hB.le hb v
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
  exact hm.trans_eq (by ring)

theorem transformedConstantState_contraction (T : CircleL2 →L[ℝ] E)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (v : CircleL2) :
    ‖transformedConstantState T v‖ ≤ ‖v‖ := by
  rw [transformedConstantState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
  have hm : ‖localAverage 0 v ()/2‖ ≤ ‖v‖ := by
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [localAverage_zero_bound v,norm_nonneg v]
  exact max_le (max_le hm hm) (max_le (hT v) (by simp))

theorem normalizedConstantState_one_slot {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) (v : CircleL2) :
    ‖transformedConstantState (normalizedConstantOutput Λ ρ t hΛ hρ.le b B hb) v‖ ≤
      Real.sqrt (2*Λ^ρ*t^(-(1/2:ℝ))*energy Λ ρ v) := by
  let R := 2*Λ^ρ*t^(-(1/2:ℝ))*energy Λ ρ v
  have hE : 0 ≤ energy Λ ρ v := by unfold energy; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hP : 1 ≤ t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hK : 0 ≤ Λ^ρ := Real.rpow_nonneg (zero_lt_one.trans_le hΛ).le _
  have hm : ‖localAverage 0 v ()/2‖ ≤ Real.sqrt R := by
    have hh := localAverage_zero_negative_sq hΛ hρ.le v
    have hh' := mul_le_mul_of_nonneg_left hP (mul_nonneg hK hE)
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs := Real.sq_sqrt hR
    have hsn := Real.sqrt_nonneg R
    dsimp only [R] at hs
    nlinarith [abs_nonneg (localAverage 0 v ())]
  have hv : ‖normalizedConstantOutput Λ ρ t hΛ hρ.le b B hb v‖ ≤ Real.sqrt R := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg R)).mp
    rw [Real.sq_sqrt hR,normalizedConstantOutput_sq]
    have hh := mul_le_mul_of_nonneg_left
      (weightedHeat_negative_sq hΛ hρ hρhalf ht ht1 b B hB.le hb v)
      (div_nonneg hK (sq_nonneg B))
    apply hh.trans_eq
    dsimp only [R]
    field_simp
  rw [transformedConstantState_apply,Prod.norm_def,Prod.norm_def,Prod.norm_def]
  exact max_le (max_le hm hm) (max_le hv (by simpa using Real.sqrt_nonneg R))

/-- The literal constant Haar column has the full negative distinguished
input bound after heat and an arbitrary bounded output multiplier. The
constant is independent of the massive scale and of the time. -/
theorem globalHaarColumn_constant_jet_negative_weighted {Λ ρ t : ℝ}
    (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (ht1 : t ≤ 1)
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im=0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i,0 ≤ M i) (hv : ∀ i,i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖^2 ≤
      (2*(stateJetBound (m/2) U (by positivity) (j+1))^2)*B^2*t^(-(1/2:ℝ))*energy Λ ρ (v 0)*
        (∏ i ∈ univ.erase (0 : Fin (j+1)),M i)^2 := by
  by_cases hB0 : B=0
  · have hz := weightedHeat_norm_le Λ ρ t hΛ hρ.le b B hB hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)
    simp only [hB0,zero_mul] at hz
    have he := le_antisymm hz (norm_nonneg _)
    simp only [he,hB0,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_mul,le_refl]
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  let T := normalizedConstantOutput Λ ρ t hΛ hρ.le b B hb
  let S := Real.sqrt (2*Λ^ρ*t^(-(1/2:ℝ))*energy Λ ρ (v 0))
  let C := stateJetBound (m/2) U (by positivity : 0 < m/2) (j+1)
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)),M i
  let z := transformedConstantState T f
  have hC : 0 ≤ C := stateJetBound_nonneg _ _ _ _
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => hM i)
  have hE : 0 ≤ energy Λ ρ (v 0) := by unfold energy; positivity
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hT : ∀ w,‖T w‖ ≤ ‖w‖ := normalizedConstantOutput_contraction hΛ hρ.le b B hBp hb
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
  have hnorm := (iteratedFDeriv ℝ (j+1) stateColumn z).le_opNorm
    (fun i => transformedConstantState T (v i))
  have hbound := hnorm.trans (mul_le_mul_of_nonneg_right
    (stateColumn_jet_bound (m/2) U (by positivity) (j+1) z hs hphys)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← Finset.mul_prod_erase univ _ (mem_univ (0 : Fin (j+1)))] at hbound
  have hprod : (∏ i ∈ univ.erase (0 : Fin (j+1)),‖transformedConstantState T (v i)‖) ≤ P := by
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    exact (transformedConstantState_contraction T hT (v i)).trans
      (circle_norm_le_ae_bound (v i) (M i) (hv i (mem_erase.mp hi).1))
  have hslot : ‖transformedConstantState T (v 0)‖ ≤ S :=
    normalizedConstantState_one_slot hΛ hρ hρhalf ht ht1 b B hBp hb (v 0)
  have hbound' : ‖iteratedFDeriv ℝ (j+1) stateColumn z (fun i => transformedConstantState T (v i))‖ ≤ C*S*P :=
    hbound.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul hslot hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hS) hC).trans_eq (by ring))
  have he := globalHaarColumn_constant_jet_transformed_state T f hp (j+1) v
  have hleft : ‖iteratedFDeriv ℝ (j+1) stateColumn z (fun i => transformedConstantState T (v i))‖ =
      (Real.sqrt (Λ^ρ)/B)*‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖ := by
    rw [← he]
    change ‖(Real.sqrt (Λ^ρ)/B) • weightedHeat Λ ρ t hΛ hρ.le b B hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (Λ^ρ)/B)]
  rw [hleft] at hbound'
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (Real.sqrt (Λ^ρ)/B)*
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v)‖) hbound' 2
  have hR : 0 ≤ 2*Λ^ρ*t^(-(1/2:ℝ))*energy Λ ρ (v 0) := by positivity
  simp only [mul_pow,div_pow,Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans_le hΛ).le ρ),
    show S^2=2*Λ^ρ*t^(-(1/2:ℝ))*energy Λ ρ (v 0) from Real.sq_sqrt hR] at hsq
  rw [div_mul_eq_mul_div] at hsq
  have hh := (div_le_iff₀ (sq_pos_of_pos hBp)).mp hsq
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) ρ)).mp
  exact hh.trans_eq (by dsimp only [C,P]; ring)

end SHE.FiniteHaar
