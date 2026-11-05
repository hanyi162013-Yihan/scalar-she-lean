module

public import SHE.HaarHigherHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat Filter Topology
open scoped ContDiff
local instance haarConstantJets_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem cellRestriction_zero (f : CircleL2) : cellRestriction 0 () f = f := by
  simpa only [Fintype.sum_unique] using sum_cellRestriction 0 f

theorem circleOne_norm : ‖circleOne‖ = 1 := by
  have he : ‖circleOne‖ ^ 2 = 1 := by rw [circleOne, gridStep_norm_sq]; norm_num
  nlinarith [norm_nonneg circleOne]

theorem circle_norm_le_ae_bound (h : CircleL2) (M : ℝ)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) : ‖h‖ ≤ M := by
  calc
    _ ≤ M * ‖circleOne‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [circleOne_ae, hh] with y ho hh
      simpa only [ho, norm_one, mul_one] using hh
    _ = M := by rw [circleOne_norm, mul_one]

theorem localAverage_zero_bound (h : CircleL2) : |localAverage 0 h ()| ≤ ‖h‖ := by
  simpa only [pow_zero, Nat.cast_one, Real.sqrt_one, one_mul, cellRestriction_zero] using
    localAverage_cell_bound 0 () h

theorem nodeMode_none (n : ℕ) (hq : nodeDepth none ≤ n) : nodeMode n none hq = none := by
  apply modePath_injective n
  rw [modePath_nodeMode]
  rfl

theorem globalHaarColumn_constant_formula (f : CircleL2) :
    globalHaarColumn none f = (Real.sqrt (localAverage 0 f ()))⁻¹ • f := by
  unfold globalHaarColumn
  rw [nodeMode_none]
  change fixedHaarColumn 0 none f = _
  simp only [fixedHaarColumn, haarColumn, totalMass, Fintype.sum_unique, pow_zero,
    Nat.cast_one, Real.sqrt_one, one_mul]
  change (Real.sqrt (localAverage 0 f ()))⁻¹ • cellRestriction 0 () f = _
  rw [cellRestriction_zero]

def constantState : CircleL2 →L[ℝ] ColumnState CircleL2 :=
  (((1/2 : ℝ) • localAverageFunctional 0 ()).prod
    ((1/2 : ℝ) • localAverageFunctional 0 ())).prod
    ((ContinuousLinearMap.id ℝ CircleL2).prod 0)

theorem constantState_apply (f : CircleL2) : constantState f =
    ((localAverage 0 f () / 2, localAverage 0 f () / 2), (f,0)) := by
  simp only [constantState, ContinuousLinearMap.prod_apply, smul_apply,
    localAverageFunctional_apply, smul_eq_mul, ContinuousLinearMap.id_apply, zero_apply]
  congr 2 <;> ring

theorem constantState_norm_le (h : CircleL2) : ‖constantState h‖ ≤ ‖h‖ := by
  rw [constantState_apply, Prod.norm_def, Prod.norm_def, Prod.norm_def]
  have hh : ‖localAverage 0 h () / 2‖ ≤ ‖h‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [localAverage_zero_bound h, norm_nonneg h]
  exact max_le (max_le hh hh) (max_le le_rfl (by simp))

theorem constantState_bounded_norm (h : CircleL2) (M : ℝ)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) : ‖constantState h‖ ≤ M :=
  (constantState_norm_le h).trans (circle_norm_le_ae_bound h M hh)

theorem haarLeft_half_equal {a : ℝ} (ha : 0 < a) :
    haarLeft (a/2) (a/2) = (Real.sqrt a)⁻¹ := by
  rw [haarLeft_formula (by positivity) (by positivity)]
  have he : (a/2) / ((a/2)*(a/2+a/2)) = a⁻¹ := by field_simp; ring
  rw [he, Real.sqrt_inv]

theorem globalHaarColumn_constant_state (f : CircleL2) (hf : 0 < localAverage 0 f ()) :
    globalHaarColumn none f = stateColumn (constantState f) := by
  rw [constantState_apply, stateColumn]
  simp only [massCoefficient, Bool.false_eq_true, ↓reduceIte, smul_zero, add_zero]
  rw [haarLeft_half_equal hf, globalHaarColumn_constant_formula]

theorem globalHaarColumn_constant_jet_state (f : CircleL2) (hf : 0 < localAverage 0 f ())
    (j : ℕ) (v : Fin j → CircleL2) :
    iteratedFDeriv ℝ j (globalHaarColumn none) f v =
      iteratedFDeriv ℝ j stateColumn (constantState f) (fun i => constantState (v i)) := by
  have hp : constantState f ∈ statePositive := by
    rw [constantState_apply]
    change 0 < localAverage 0 f () / 2 ∧ 0 < localAverage 0 f () / 2
    exact ⟨by positivity, by positivity⟩
  have hfun : (stateColumn ∘ constantState) =ᶠ[𝓝 f] globalHaarColumn none := by
    have hc : Continuous (fun z : CircleL2 => localAverage 0 z ()) := (localAverageFunctional 0 ()).continuous
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hf] with z hz
    exact (globalHaarColumn_constant_state z hz).symm
  have he := constantState.iteratedFDerivWithin_comp_right
    (fun z hz => (contDiffAt_stateColumn z hz ∞).contDiffWithinAt)
    isOpen_statePositive.uniqueDiffOn (isOpen_statePositive.preimage constantState.continuous).uniqueDiffOn
    hp (i := j) (by simp : (j : WithTop ℕ∞) ≤ ∞)
  have hcomp : ContDiffAt ℝ j (stateColumn ∘ constantState) f :=
    (contDiffAt_stateColumn (constantState f) hp j).comp f constantState.contDiff.contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
      (isOpen_statePositive.preimage constantState.continuous).uniqueDiffOn hcomp hp,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      (contDiffAt_stateColumn (constantState f) hp j) hp] at he
  rw [(hfun.iteratedFDeriv ℝ j).eq_of_nhds] at he
  exact congrArg (fun A => A v) he

/-- The true constant Haar column has the same all-order one-slot bound
as the detail packets, with no scale factor or cancellation requirement. -/
theorem globalHaarColumn_constant_jet_bound (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → CircleL2) (M : Fin (j+1) → ℝ)
    (_hM : ∀ i, 0 ≤ M i) (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i) :
    ‖iteratedFDeriv ℝ (j+1) (globalHaarColumn none) f v‖ ≤
      stateJetBound (m/2) U (by positivity) (j+1) * ‖v 0‖ *
        ∏ i ∈ univ.erase (0 : Fin (j+1)), M i := by
  have hU := elliptic_upper_nonneg f m U hm hf
  have ha := localAverage_bounds_ae 0 f m U hf ()
  have hp : 0 < localAverage 0 f () := hm.trans_le ha.1
  rw [globalHaarColumn_constant_jet_state f hp]
  have hs : (constantState f).1 ∈ massRectangle (m/2) U := by
    rw [constantState_apply]
    exact ⟨⟨by linarith, by linarith⟩,⟨by linarith, by linarith⟩⟩
  have hb : ‖(constantState f).2‖ ≤ U := by
    rw [constantState_apply, Prod.norm_def]
    exact max_le (circle_norm_le_ae_bound f U (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hf))
      (by simpa only [norm_zero] using hU)
  have hn := (iteratedFDeriv ℝ (j+1) stateColumn (constantState f)).le_opNorm (fun i => constantState (v i))
  have hnorm := hn.trans (mul_le_mul_of_nonneg_right (stateColumn_jet_bound (m/2) U (by positivity) (j+1) _ hs hb)
    (prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← mul_prod_erase univ _ (mem_univ (0 : Fin (j+1)))] at hnorm
  have hprod : (∏ i ∈ univ.erase (0 : Fin (j+1)), ‖constantState (v i)‖) ≤
      ∏ i ∈ univ.erase (0 : Fin (j+1)), M i :=
    prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i hi => constantState_bounded_norm (v i) (M i)
      (hv i (mem_erase.mp hi).1))
  exact hnorm.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul (constantState_norm_le (v 0)) hprod (prod_nonneg (fun _ _ => norm_nonneg _))
      (norm_nonneg _)) (stateJetBound_nonneg (m/2) U (by positivity) (j+1))).trans_eq (by ring))

theorem option_energy_sum {α : Type*} (F : Option α → ℝ)
    (hs : Summable (fun p => F (some p))) :
    Summable F ∧ (∑' q, F q) = (∑' p, F (some p)) + F none := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit.{0} α
  let G : α ⊕ PUnit.{1} → ℝ := fun x => F (e.symm x)
  have hL : Summable (G ∘ Sum.inl) := by
    change Summable (fun p => F ((Equiv.optionEquivSumPUnit.{0} α).symm (Sum.inl p)))
    simpa only [Equiv.optionEquivSumPUnit_symm_inl] using hs
  have hR : Summable (G ∘ Sum.inr) := (hasSum_fintype _).summable
  have hG : Summable G := Summable.sum G hL hR
  refine ⟨e.symm.summable_iff.mp hG, ?_⟩
  rw [← e.symm.tsum_eq F]
  exact (hL.tsum_sum hR).trans (by simp only [G, e, Equiv.optionEquivSumPUnit_symm_inl,
    Equiv.optionEquivSumPUnit_symm_inr, tsum_fintype, Fintype.sum_unique])

def higherHeatConstant (m U : ℝ) (hm : 0 < m) (j : ℕ) : ℝ :=
  4 * packetHeatConstant * (stateJetBound m U hm (j+1)) ^ 2 *
      (DyadicTransport.smoothingConstant (1/2)) ^ 2 +
    (stateJetBound (m/2) U (by positivity) (j+1)) ^ 2

/-- The full actual weighted Haar factor, including its constant column,
has heat-regularized higher derivatives in Hilbert--Schmidt class. The
one-slot estimate is uniform in every dyadic finite approximation. -/
theorem globalHaarColumn_all_higher_heat {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (f : DyadicApproximation.RealL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) :
    Summable (fun q : HaarNode => ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn q) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2) ∧
    (∑' q : HaarNode, ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn q) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2) ≤
      higherHeatConstant m U hm j * t ^ (-(1/2:ℝ)) *
        ‖DyadicApproximation.realEmbed (v 0)‖ ^ 2 *
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i) ^ 2 := by
  have hh := globalHaarColumn_higher_heat ht ht1 f m U hm hf j v M hM hv
  have hsum := option_energy_sum (fun q : HaarNode => ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn q) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2) hh.1
  have hconst := pow_le_pow_left₀ (norm_nonneg _) (globalHaarColumn_constant_jet_bound _ m U hm
    (realEmbed_real f) hf j (fun i => DyadicApproximation.realEmbed (v i)) M hM hv) 2
  have htunit : 1 ≤ t ^ (-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hc : ‖heat t (iteratedFDeriv ℝ (j+1) (globalHaarColumn none)
      (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2 ≤
      (stateJetBound (m/2) U (by positivity) (j+1)) ^ 2 * t ^ (-(1/2:ℝ)) *
        ‖DyadicApproximation.realEmbed (v 0)‖ ^ 2 * (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ (j+1) (globalHaarColumn none)
          (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i))‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (heat_contraction t _) 2
      _ ≤ _ := hconst.trans (by
        rw [mul_pow, mul_pow]
        have hh := mul_le_mul_of_nonneg_left htunit (by positivity :
          0 ≤ (stateJetBound (m/2) U (by positivity) (j+1))^2 *
            ‖DyadicApproximation.realEmbed (v 0)‖^2*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2)
        nlinarith only [hh])
  refine ⟨hsum.1, ?_⟩
  rw [hsum.2]
  exact (add_le_add hh.2 hc).trans_eq (by unfold higherHeatConstant; ring)

end SHE.FiniteHaar
