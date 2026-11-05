module

public import SHE.HaarSeparatedGenerations
public import SHE.HaarSeparatedConstant

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov HaarWeightedHeat NegativeNash
local instance haarSeparatedTrace_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem separated_coarse_identity {w L ρ : ℝ} (hw : 0 < w) (hL : 0 ≤ L) :
    w^(ρ-1/2)*(L/w^(-(1/2:ℝ)))^(1-2*ρ) = L^(1-2*ρ) := by
  rw [Real.div_rpow hL (Real.rpow_nonneg hw.le _),← Real.rpow_mul hw.le,
    show (-(1/2:ℝ))*(1-2*ρ)=ρ-1/2 by ring]
  field_simp

theorem separated_fine_identity {δ L ρ : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    δ^(-ρ)*(δ^(-(1/2:ℝ))/L)^(2-2*ρ) = δ⁻¹*L^(2*ρ-2) := by
  rw [Real.div_rpow (Real.rpow_nonneg hδ.le _) hL.le,← Real.rpow_mul hδ.le,div_eq_mul_inv,
    ← Real.rpow_neg hL.le]
  calc
    _ = (δ^(-ρ)*δ^((-(1/2:ℝ))*(2-2*ρ)))*L^(-(2-2*ρ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hδ,show -ρ+(-(1/2:ℝ))*(2-2*ρ) = -1 by ring,Real.rpow_neg_one]
      congr 1
      ring

/-- The actual scale-separated nonconstant Haar trace. The outer
kernel may be arbitrarily rough, subject only to its literal Gaussian
envelope and exact integral representation. Cancellation occurs at the
inner heat age δ before applying that kernel. -/
theorem exists_nonconstant_separated_negative_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel w K hw) (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      Summable (separatedJetEnergy D Λ ρ δ f j v) ∧
      (∑' p : List Bool,separatedJetEnergy D Λ ρ δ f j v p) ≤
        C*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  obtain ⟨Cc,hCc,hcoarse⟩ := exists_separated_coarse_generation m U hm j hρ hρhalf
  obtain ⟨Cm,hCm,hmiddle⟩ := exists_separated_middle_generation m U hm j hρ hρhalf
  obtain ⟨Cf,hCf,hfine⟩ := exists_separated_fine_generation m U hm j hρ hρhalf
  let S := Cc+Cm+Cf
  have hS : 0 < S := by dsimp [S]; positivity
  have hCs := ThreeBandSeries.constant_pos (by linarith : 0 < 1-2*ρ) (by linarith : 0 < 2-2*ρ)
  refine ⟨S*ThreeBandSeries.constant (1-2*ρ) (2-2*ρ),by positivity,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D f hf v M hM hv
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let F := separatedJetEnergy D Λ ρ δ f j v
  let g := fun n : ℕ => ∑ x : Grid n,F (leafPath n x)
  let H := S*K^2*E*P^2*w^(ρ-1/2)*δ^(-ρ)
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hF : ∀ p,0 ≤ F p := by intro p; dsimp [F,separatedJetEnergy,energy]; positivity
  have hg : ∀ n,0 ≤ g n := fun _ => sum_nonneg (fun _ _ => hF _)
  have hA : 1 ≤ w^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos hw hw1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hAB : w^(-(1/2:ℝ)) ≤ δ^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hδ hδw (by norm_num)
  have hc : ∀ n,(2:ℝ)^n ≤ w^(-(1/2:ℝ)) → g n ≤ H*((2:ℝ)^n/w^(-(1/2:ℝ)))^(1-2*ρ) := by
    intro n hn
    have hh := hcoarse Λ δ w K hΛ hδ hw hδw hK D n hn f hf v M hM hv
    have hcs : Cc ≤ S := by dsimp [S]; linarith
    have hm := mul_le_mul_of_nonneg_right hcs (by positivity : 0 ≤ K^2*E*P^2*δ^(-ρ)*((2:ℝ)^n)^(1-2*ρ))
    have he := separated_coarse_identity (ρ := ρ) hw (by positivity : 0 ≤ (2:ℝ)^n)
    have htarget : H*((2:ℝ)^n/w^(-(1/2:ℝ)))^(1-2*ρ) = S*K^2*E*P^2*δ^(-ρ)*((2:ℝ)^n)^(1-2*ρ) := by
      dsimp only [H]
      calc
        _ = S*K^2*E*P^2*δ^(-ρ)*(w^(ρ-1/2)*((2:ℝ)^n/w^(-(1/2:ℝ)))^(1-2*ρ)) := by ring
        _ = _ := by rw [he]
    rw [htarget]
    exact hh.trans (by dsimp only [E,P]; nlinarith only [hm])
  have hm : ∀ n,w^(-(1/2:ℝ)) ≤ (2:ℝ)^n → (2:ℝ)^n ≤ δ^(-(1/2:ℝ)) → g n ≤ H := by
    intro n _ hn
    have hh := hmiddle Λ δ w K hΛ hδ hw hw1 hδw hK D n hn f hf v M hM hv
    have hcs : Cm ≤ S := by dsimp [S]; linarith
    have hm := mul_le_mul_of_nonneg_right hcs (by positivity : 0 ≤ K^2*E*P^2*w^(ρ-1/2)*δ^(-ρ))
    exact hh.trans (by dsimp only [H,E,P]; nlinarith only [hm])
  have hf' : ∀ n,δ^(-(1/2:ℝ)) ≤ (2:ℝ)^n → g n ≤ H*(δ^(-(1/2:ℝ))/(2:ℝ)^n)^(2-2*ρ) := by
    intro n hn
    have hh := hfine Λ δ w K hΛ hδ hw hw1 hδw hK D n hn f hf v M hM hv
    have hcs : Cf ≤ S := by dsimp [S]; linarith
    have hm := mul_le_mul_of_nonneg_right hcs (by positivity : 0 ≤ K^2*E*P^2*w^(ρ-1/2)*δ⁻¹*((2:ℝ)^n)^(2*ρ-2))
    have he := separated_fine_identity (ρ := ρ) hδ (by positivity : 0 < (2:ℝ)^n)
    have htarget : H*(δ^(-(1/2:ℝ))/(2:ℝ)^n)^(2-2*ρ) = S*K^2*E*P^2*w^(ρ-1/2)*δ⁻¹*((2:ℝ)^n)^(2*ρ-2) := by
      dsimp only [H]
      rw [mul_assoc,he]
      ring
    rw [htarget]
    exact hh.trans (by dsimp only [E,P]; nlinarith only [hm])
  have hs := ThreeBandSeries.series hA hAB (by linarith : 0 < 1-2*ρ) (by linarith : 0 < 2-2*ρ) hH g hg hc hm hf'
  have hsig : Summable (fun nx : Σ n,Grid n => F (leafPath nx.1 nx.2)) := by
    apply (summable_sigma_of_nonneg (fun nx => hF _)).mpr
    exact ⟨fun n => (hasSum_fintype (fun x : Grid n => F (leafPath n x))).summable,
      by simpa only [tsum_fintype] using hs.1⟩
  have he : (∑' p,F p) = ∑' n,g n := by
    rw [← generationPathEquiv.tsum_eq F]
    simpa only [generationPathEquiv,Equiv.ofBijective_apply,tsum_fintype] using hsig.tsum_sigma
  have hlog : Real.log (δ^(-(1/2:ℝ))/w^(-(1/2:ℝ))) ≤ Real.log (w/δ) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_rpow hδ,Real.log_rpow hw,Real.log_div hw.ne' hδ.ne']
    have hh := Real.log_le_log hδ hδw
    linarith
  refine ⟨generationPathEquiv.summable_iff.mp hsig,?_⟩
  change (∑' p,F p) ≤ _
  rw [he]
  have hh := hs.2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) (mul_nonneg hH hCs.le))
  exact hh.trans_eq (by dsimp only [H,E,P]; ring)

/-- The complete scale-separated unified trace, including the actual
constant Haar column, with the exact logarithmic middle-scale cost. -/
theorem exists_global_separated_negative_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel w K hw) (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      Summable (fun q : HaarNode => ‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ∧
      (∑' q : HaarNode,‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ≤
        C*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  obtain ⟨C,hC,htrace⟩ := exists_nonconstant_separated_negative_trace m U hm j hρ hρhalf
  let J := 2*(stateJetBound (m/2) U (by positivity) (j+1))^2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨C+J,by positivity,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D f hf v M hM hv
  let F : HaarNode → ℝ := fun q => ‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
    (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
      (fun i => DyadicApproximation.realEmbed (v i)))‖^2
  have he (p : List Bool) : F (some p) = separatedJetEnergy D Λ ρ δ f j v p := by
    change ‖besselHalf Λ ρ hΛ hρ.le _‖^2 = _
    rw [besselHalf_norm_sq]
    rfl
  have hn := htrace Λ δ w K hΛ hδ hw hw1 hδw hK D f hf v M hM hv
  have hn' : Summable (fun p : List Bool => F (some p)) := hn.1.congr (fun p => (he p).symm)
  have hs := option_energy_sum F hn'
  have hA (z : CircleL2) : ‖D.operator z‖ ≤ K*‖z‖ := by
    have hh := HeatDominatedOperator.norm_sq_le hw hK D.operator D.kernel D.measurable_kernel D.kernel_bound D.representation z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
    simpa only [mul_pow] using hh
  have hc := globalHaarColumn_constant_jet_separated_negative hΛ hρ.le (by linarith : ρ ≤ 1)
    hδ (hδw.trans hw1) hK D.operator hA (DyadicApproximation.realEmbed f) m U hm (realEmbed_real f) hf j
    (fun i => DyadicApproximation.realEmbed (v i)) M hv
  rw [energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)] at hc
  have hE : 0 ≤ StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0)) := by
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hwρ : 1 ≤ w^(ρ-1/2) := by
    simpa using Real.rpow_le_rpow_of_nonpos hw hw1 (by linarith : ρ-1/2 ≤ 0)
  have hlog : 0 ≤ Real.log (w/δ) := Real.log_nonneg ((one_le_div hδ).mpr hδw)
  have hfactor : 1 ≤ w^(ρ-1/2)*(1+Real.log (w/δ)) := by
    have hh := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1+Real.log (w/δ)) (Real.rpow_nonneg hw.le (ρ-1/2))
    nlinarith only [hh,hwρ]
  have hc' : F none ≤ J*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*
      StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
      (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
    have hh := mul_le_mul_of_nonneg_right hfactor (by positivity : 0 ≤ J*K^2*δ^(-ρ)*
      StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
      (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2)
    exact hc.trans (by dsimp only [F,J]; nlinarith only [hh])
  refine ⟨hs.1,?_⟩
  change (∑' q,F q) ≤ _
  rw [hs.2]
  have he' : (∑' p : List Bool,F (some p)) = ∑' p : List Bool,separatedJetEnergy D Λ ρ δ f j v p := tsum_congr he
  rw [he']
  exact (add_le_add hn.2 hc').trans_eq (by ring)

end SHE.FiniteHaar
