module

public import SHE.HaarNegativeTaylor
public import SHE.HaarNegativeConstant

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HaarWeightedHeat
open scoped ContDiff
local instance haarUnifiedNegative_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- The exact negative-input unified trace for the entire actual Haar
factor, including its constant column, at every positive derivative
order. The mass parameter and the dyadic approximation do not enter the
constant. -/
theorem exists_global_negative_jet_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t), t ≤ 1 →
      ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      Summable (fun q : HaarNode => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ∧
      (∑' q : HaarNode, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ≤
        C*B^2*t^(-(1/2:ℝ))*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  obtain ⟨C,hC,htrace⟩ := exists_globalHaarColumn_jet_negative_trace m U hm j hρ hρhalf
  let K := 2*(stateJetBound (m/2) U (by positivity) (j+1))^2
  refine ⟨C+K,by dsimp [K]; positivity,?_⟩
  intro Λ t hΛ ht ht1 f hf v M hM hv b B hB hb
  let F : HaarNode → ℝ := fun q => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
    (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
      (fun i => DyadicApproximation.realEmbed (v i)))‖^2
  have hn := htrace Λ t hΛ ht ht1 f hf v M hM hv b B hB hb
  have hs := option_energy_sum F hn.1
  have hc := globalHaarColumn_constant_jet_negative_weighted hΛ hρ hρhalf ht ht1
    (DyadicApproximation.realEmbed f) m U hm (realEmbed_real f) hf j
    (fun i => DyadicApproximation.realEmbed (v i)) M hM hv b B hB hb
  rw [NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)] at hc
  refine ⟨hs.1,?_⟩
  change (∑' q,F q) ≤ _
  rw [hs.2]
  exact (add_le_add hn.2 hc).trans_eq (by dsimp only [K]; ring)

theorem weighted_globalColumnTaylorRemainder_integral {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B)
    (q : HaarNode) (f h : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U) (j : ℕ) :
    weightedHeat Λ ρ t hΛ hρ b B hb (globalColumnTaylorRemainder q f h j) =
      (j.factorial:ℝ)⁻¹ • ∫ r in (0:ℝ)..1, (1-r)^j •
        weightedHeat Λ ρ t hΛ hρ b B hb
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h)) := by
  have hp (x : Grid (nodeDepth q)) : 0 < localAverage (nodeDepth q) f x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hp' (x : Grid (nodeDepth q)) : 0 < localAverage (nodeDepth q) (f+h) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hfh x).1
  unfold globalColumnTaylorRemainder
  rw [globalHaarColumn_taylor q f h j hp hp',add_sub_cancel_left]
  change ((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ) ((j.factorial:ℝ)⁻¹ • _) = _
  rw [map_smul]
  congr 1
  have hc : ContinuousOn (fun r : ℝ => (1-r)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f+r•h) (fun _ => h)) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow j).smul
      (continuousOn_column_jet_segment q f h m U hm hf hfh (j+1) (fun _ => h))
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [← ((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ).intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact ((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ).map_smul _ _

/-- The actual full-factor Taylor remainder obeys the same massive
negative-input trace at every order, with only endpoint ellipticity. -/
theorem exists_global_taylor_negative_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t), t ≤ 1 →
      ∀ (f h : DyadicApproximation.RealL2) (M : ℝ), 0 ≤ M →
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle, m ≤ ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ∧
        ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed h y‖ ≤ M) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      Summable (fun q : HaarNode => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ∧
      (∑' q : HaarNode, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ≤
        (j.factorial:ℝ)⁻¹^2*C*B^2*t^(-(1/2:ℝ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed h)*M^(2*j) := by
  obtain ⟨C,hC,htrace⟩ := exists_global_negative_jet_trace m U hm j hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ t hΛ ht ht1 f h M hM hf hfh hh b B hB hb
  let f' := DyadicApproximation.realEmbed f
  let h' := DyadicApproximation.realEmbed h
  let W := (weightedHeat Λ ρ t hΛ hρ.le b B hb).restrictScalars ℝ
  let F : ℝ → HaarNode → CircleL2 := fun r q => (1-r)^j •
    W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f'+r•h') (fun _ => h'))
  let K := C*B^2*t^(-(1/2:ℝ))*StepInput.negativeEnergy 1 Λ ρ h'*M^(2*j)
  have hE : 0 ≤ StepInput.negativeEnergy 1 Λ ρ h' := by
    rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold NegativeNash.energy
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcont (q : HaarNode) : ContinuousOn (fun r => F r q) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow j).smul
      (W.continuous.comp_continuousOn (continuousOn_column_jet_segment q f' h' m U hm hf hfh (j+1) (fun _ => h')))
  have hbound (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      Summable (fun q => ‖F r q‖^2) ∧ (∑' q,‖F r q‖^2) ≤ K := by
    have he : DyadicApproximation.realEmbed (f+r•h) = f'+r•h' := by rw [map_add,map_smul]
    have hj := htrace Λ t hΛ ht ht1 (f+r•h) (by
      rw [he]
      exact affine_field_segment_bounds f' h' m U r hr hf hfh)
      (fun _ => h) (fun _ => M) (fun _ => hM) (fun _ _ => hh) b B hB hb
    simp only [he,prod_const,card_erase_of_mem (mem_univ (0 : Fin (j+1))),
      card_univ,Fintype.card_fin,Nat.add_sub_cancel] at hj
    have hp : ‖(1-r)^j‖^2 ≤ 1 := by
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg (by linarith [hr.2])]
      have hh := pow_le_one₀ (by linarith [hr.2] : 0 ≤ 1-r) (by linarith [hr.1]) (n := j)
      nlinarith [pow_nonneg (by linarith [hr.2] : 0 ≤ 1-r) j]
    have heF (q : HaarNode) : ‖F r q‖^2 = ‖(1-r)^j‖^2*
        ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f'+r•h') (fun _ => h'))‖^2 := by
      dsimp only [F]
      rw [norm_smul,mul_pow]
    refine ⟨?_,?_⟩
    · exact (hj.1.mul_left (‖(1-r)^j‖^2)).congr (fun q => (heF q).symm)
    simp only [heF,tsum_mul_left]
    have hsum : (∑' q, ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (f'+r•h') (fun _ => h'))‖^2) ≤ K := by
      simpa only [K,f',h',show 2*j=j*2 by omega,← pow_mul] using! hj.2
    exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans (by nlinarith only [mul_le_mul_of_nonneg_right hp hK])
  have hi := TraceIntegral.square_trace F K hK hcont hbound
  have he (q : HaarNode) : weightedHeat Λ ρ t hΛ hρ.le b B hb
      (globalColumnTaylorRemainder q f' h' j) = (j.factorial:ℝ)⁻¹ • ∫ r in (0:ℝ)..1,F r q :=
    weighted_globalColumnTaylorRemainder_integral hΛ hρ.le b B hb q f' h' m U hm hf hfh j
  have hen (q : HaarNode) : ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (globalColumnTaylorRemainder q f' h' j)‖^2 = (j.factorial:ℝ)⁻¹^2*‖∫ r in (0:ℝ)..1,F r q‖^2 := by
    rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  change Summable (fun q => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (globalColumnTaylorRemainder q f' h' j)‖^2) ∧ _
  refine ⟨?_,?_⟩
  · exact (hi.1.mul_left ((j.factorial:ℝ)⁻¹^2)).congr (fun q => (hen q).symm)
  change (∑' q, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (globalColumnTaylorRemainder q f' h' j)‖^2) ≤ _
  simp only [hen,tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hi.2 (sq_nonneg _)).trans_eq (by dsimp only [K,h']; ring)

/-- The genuine same-Haar signed factor difference, with an arbitrary
bounded rough output multiplier, satisfies the negative-to-negative
trace without any derivative or approximation premise. -/
theorem exists_global_signed_negative_trace (m U : ℝ) (hm : 0 < m)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t), t ≤ 1 →
      ∀ (f g : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed g y).re ∧
        (DyadicApproximation.realEmbed g y).re ≤ U) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      Summable (fun q : HaarNode => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))‖^2) ∧
      (∑' q : HaarNode, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))‖^2) ≤
        C*B^2*t^(-(1/2:ℝ))*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (g-f)) := by
  obtain ⟨C,hC,hTaylor⟩ := exists_global_taylor_negative_trace m U hm 0 hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ t hΛ ht ht1 f g hf hg b B hB hb
  have hU := elliptic_upper_nonneg (DyadicApproximation.realEmbed f) m U hm hf
  have he : DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed (g-f) = DyadicApproximation.realEmbed g := by
    rw [map_sub]
    abel
  have hbound : ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (g-f) y‖ ≤ 2*U := by
    have he' : DyadicApproximation.realEmbed (g-f) = DyadicApproximation.realEmbed g-DyadicApproximation.realEmbed f := map_sub _ _ _
    rw [he']
    filter_upwards [Lp.coeFn_sub (DyadicApproximation.realEmbed g) (DyadicApproximation.realEmbed f),
      CircleMultiplier.elliptic_norm_bound _ m U hm (realEmbed_real f) hf,
      CircleMultiplier.elliptic_norm_bound _ m U hm (realEmbed_real g) hg] with y hy hfy hgy
    rw [hy]
    exact (norm_sub_le _ _).trans (by linarith)
  have hR (q : HaarNode) : globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f)
      (DyadicApproximation.realEmbed (g-f)) 0 =
      globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f) := by
    simp only [globalColumnTaylorRemainder,he,zero_add,range_one,sum_singleton,Nat.factorial_zero,
      Nat.cast_one,inv_one,iteratedFDeriv_zero_apply,one_smul]
  have hh := hTaylor Λ t hΛ ht ht1 f (g-f) (2*U) (by positivity) hf (by rw [he]; exact hg) hbound b B hB hb
  simpa only [hR,Nat.factorial_zero,Nat.cast_one,inv_one,one_pow,one_mul,mul_zero,pow_zero,mul_one] using! hh

end SHE.FiniteHaar
