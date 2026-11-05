module

public import SHE.TraceIntegral

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HaarWeightedHeat
open scoped ContDiff
local instance haarNegativeTaylor_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem continuousOn_column_jet_segment (q : HaarNode) (f h : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U)
    (k : ℕ) (v : Fin k → CircleL2) :
    ContinuousOn (fun r : ℝ => iteratedFDeriv ℝ k (globalHaarColumn q) (f+r•h) v) (Icc (0:ℝ) 1) := by
  intro r hr
  have hpos (x : Grid (nodeDepth q)) : 0 < localAverage (nodeDepth q) (f+r•h) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U (affine_field_segment_bounds f h m U r hr hf hfh) x).1
  have hc := (contDiffAt_globalHaarColumn q (f+r•h) hpos (k : WithTop ℕ∞)).continuousAt_iteratedFDeriv le_rfl
  have hline : ContinuousAt (fun r : ℝ => f+r•h) r := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hc' : ContinuousAt (fun r : ℝ => iteratedFDeriv ℝ k (globalHaarColumn q) (f+r•h)) r :=
    ContinuousAt.comp (f := fun r : ℝ => f+r•h) hc hline
  exact ((continuous_eval_const v).continuousAt.comp hc').continuousWithinAt

theorem weighted_columnTaylorRemainder_integral {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B)
    (p : List Bool) (f h : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U) (j : ℕ) :
    weightedHeat Λ ρ t hΛ hρ b B hb (columnTaylorRemainder p f h j) =
      (j.factorial:ℝ)⁻¹ • ∫ r in (0:ℝ)..1, (1-r)^j •
        weightedHeat Λ ρ t hΛ hρ b B hb
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f+r•h) (fun _ => h)) := by
  have hp (x : Grid (nodeDepth (some p))) : 0 < localAverage (nodeDepth (some p)) f x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hp' (x : Grid (nodeDepth (some p))) : 0 < localAverage (nodeDepth (some p)) (f+h) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hfh x).1
  unfold columnTaylorRemainder
  rw [globalHaarColumn_taylor (some p) f h j hp hp',add_sub_cancel_left]
  change ((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ) ((j.factorial:ℝ)⁻¹ • _) = _
  rw [map_smul]
  congr 1
  have hc : ContinuousOn (fun r : ℝ => (1-r)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f+r•h) (fun _ => h)) (Icc (0:ℝ) 1) := ((continuousOn_const.sub continuousOn_id).pow j).smul
    (continuousOn_column_jet_segment (some p) f h m U hm hf hfh (j+1) (fun _ => h))
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [← ((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ).intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact ((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ).map_smul _ _

/-- Actual countable Taylor remainders have the negative-input unified
trace, at every finite order, uniformly in the mass parameter. -/
theorem exists_nonconstant_taylor_negative_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t), t ≤ 1 →
      ∀ (f h : DyadicApproximation.RealL2) (M : ℝ), 0 ≤ M →
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle, m ≤ ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ∧
        ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed h y‖ ≤ M) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      Summable (fun p : List Bool => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (columnTaylorRemainder p (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ∧
      (∑' p : List Bool, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
        (columnTaylorRemainder p (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ≤
        (j.factorial:ℝ)⁻¹^2*C*B^2*t^(-(1/2:ℝ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed h)*M^(2*j) := by
  obtain ⟨C,hC,htrace⟩ := exists_globalHaarColumn_jet_negative_trace m U hm j hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ t hΛ ht ht1 f h M hM hf hfh hh b B hB hb
  let f' := DyadicApproximation.realEmbed f
  let h' := DyadicApproximation.realEmbed h
  let W := (weightedHeat Λ ρ t hΛ hρ.le b B hb).restrictScalars ℝ
  let F : ℝ → List Bool → CircleL2 := fun r p => (1-r)^j •
    W (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f'+r•h') (fun _ => h'))
  let K := C*B^2*t^(-(1/2:ℝ))*StepInput.negativeEnergy 1 Λ ρ h'*M^(2*j)
  have hE : 0 ≤ StepInput.negativeEnergy 1 Λ ρ h' := by
    rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold NegativeNash.energy
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcont (p : List Bool) : ContinuousOn (fun r => F r p) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow j).smul
      (W.continuous.comp_continuousOn (continuousOn_column_jet_segment (some p) f' h' m U hm hf hfh (j+1) (fun _ => h')))
  have hbound (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      Summable (fun p => ‖F r p‖^2) ∧ (∑' p,‖F r p‖^2) ≤ K := by
    have he : DyadicApproximation.realEmbed (f+r•h) = f'+r•h' := by rw [map_add,map_smul]
    have hj := htrace Λ t hΛ ht ht1 (f+r•h) (by
      rw [he]
      exact affine_field_segment_bounds f' h' m U r hr hf hfh)
      (fun _ => h) (fun _ => M) (fun _ => hM) (fun _ _ => hh) b B hB hb
    simp only [negativeJetHeatEnergy,he,prod_const,card_erase_of_mem (mem_univ (0 : Fin (j+1))),
      card_univ,Fintype.card_fin,Nat.add_sub_cancel,pow_mul] at hj
    have hp : ‖(1-r)^j‖^2 ≤ 1 := by
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg (by linarith [hr.2])]
      have hh := pow_le_one₀ (by linarith [hr.2] : 0 ≤ 1-r) (by linarith [hr.1]) (n := j)
      nlinarith [pow_nonneg (by linarith [hr.2] : 0 ≤ 1-r) j]
    have heF (p : List Bool) : ‖F r p‖^2 = ‖(1-r)^j‖^2*
        ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f'+r•h') (fun _ => h'))‖^2 := by
      dsimp only [F]
      rw [norm_smul,mul_pow]
    refine ⟨?_,?_⟩
    · have hs := hj.1.mul_left (‖(1-r)^j‖^2)
      apply hs.congr
      intro p
      simpa only [negativeJetHeatEnergy,he,W,f',h'] using! (heF p).symm
    simp only [heF,tsum_mul_left]
    have hsum : (∑' p, ‖W (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f'+r•h') (fun _ => h'))‖^2) ≤ K := by
      simpa only [K,f',h',show 2*j=j*2 by omega,← pow_mul] using! hj.2
    exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans (by nlinarith only [mul_le_mul_of_nonneg_right hp hK])
  have hi := TraceIntegral.square_trace F K hK hcont hbound
  have he (p : List Bool) : weightedHeat Λ ρ t hΛ hρ.le b B hb
      (columnTaylorRemainder p f' h' j) = (j.factorial:ℝ)⁻¹ • ∫ r in (0:ℝ)..1,F r p :=
    weighted_columnTaylorRemainder_integral hΛ hρ.le b B hb p f' h' m U hm hf hfh j
  have hen (p : List Bool) : ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (columnTaylorRemainder p f' h' j)‖^2 = (j.factorial:ℝ)⁻¹^2*‖∫ r in (0:ℝ)..1,F r p‖^2 := by
    rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  change Summable (fun p => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (columnTaylorRemainder p f' h' j)‖^2) ∧ _
  refine ⟨?_,?_⟩
  · exact (hi.1.mul_left ((j.factorial:ℝ)⁻¹^2)).congr (fun p => (hen p).symm)
  change (∑' p, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (columnTaylorRemainder p f' h' j)‖^2) ≤ _
  simp only [hen,tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hi.2 (sq_nonneg _)).trans_eq (by dsimp only [K,h']; ring)

end SHE.FiniteHaar
