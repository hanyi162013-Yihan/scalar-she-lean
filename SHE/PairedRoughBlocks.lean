module

public import SHE.JointGaussianBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.PairedRoughBlocks
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianRoughBlockMoments JointGaussianBlocks
  GaussianEnvelopeMoments
open scoped NNReal BigOperators

theorem differences_sub {E : Type*} [Zero E] {r : ℕ} (is : List (Fin r))
    (F G : (Fin r → E) → ℝ) :
    fractionDifferences is (fun y => F y-G y) =
      fun y => fractionDifferences is F y-fractionDifferences is G y := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change fractionDifference i (fractionDifferences is (fun y => F y-G y)) =
      fun y => fractionDifference i (fractionDifferences is F) y-
        fractionDifference i (fractionDifferences is G) y
    rw [ih]
    funext x
    dsimp [fractionDifference]
    ring

theorem min_rpow_le {a b β χ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hχ : 0 ≤ χ) (hχβ : χ ≤ β) :
    min (a^β) (b^β) ≤ a^χ*b^(β-χ) := by
  have hdiff : 0 ≤ β-χ := sub_nonneg.mpr hχβ
  have he (z : ℝ) (hz : 0 ≤ z) : z^β = z^χ*z^(β-χ) := by
    rw [← Real.rpow_add_of_nonneg hz hχ hdiff]
    congr 1
    ring
  rcases le_total a b with hab|hba
  · exact (min_le_left _ _).trans ((le_of_eq (he a ha)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab hdiff) (rpow_nonneg ha _)))
  · exact (min_le_right _ _).trans ((le_of_eq (he b hb)).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb hba hχ) (rpow_nonneg hb _)))

/-- One physical current increment paired with a nonempty old rough
block retains the minimum of the current and original assigned increments. -/
theorem paired_min_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {r k : ℕ}
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (i : Fin r) (hi : i ∈ block choices factor) (a : ℝ → ℝ) {H β : ℝ}
    (hH : 0 ≤ H) (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β)
    (mean e : ℝ) (L : Fin r → V →L[ℝ] ℝ) (x : Fin r → V) :
    |fractionDifferences (block choices factor) (fun y => a (affineSum (mean+e) L y))
        (suppress (suppressed choices factor) x) -
      fractionDifferences (block choices factor) (fun y => a (affineSum mean L y))
        (suppress (suppressed choices factor) x)| ≤
      (2 : ℝ)^((block choices factor).length)*H*min (|e|^β) (|L i (x i)|^β) := by
  let Y := suppress (suppressed choices factor) x
  have hcurrent : ∀ y, |a (affineSum (mean+e) L y)-a (affineSum mean L y)| ≤ H*|e|^β := by
    intro y
    have hh := hholder (affineSum (mean+e) L y) (affineSum mean L y)
    have he : affineSum (mean+e) L y-affineSum mean L y = e := by unfold affineSum; ring
    rwa [he] at hh
  have hc := fractionDifferences_bound (block choices factor)
    (fun y => a (affineSum (mean+e) L y)-a (affineSum mean L y)) (H*|e|^β) hcurrent Y
  rw [differences_sub] at hc
  have h₁ := suppressed_rough_block_bound choices hnd factor i hi a H β hholder (mean+e) L x
  have h₀ := suppressed_rough_block_bound choices hnd factor i hi a H β hholder mean L x
  have hlen : 1 ≤ (block choices factor).length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem hi)
  have hp : (2 : ℝ)^((block choices factor).length) = 2^((block choices factor).length-1)*2 := by
    rw [← pow_succ,Nat.sub_add_cancel hlen]
  have ho := abs_sub
    (fractionDifferences (block choices factor) (fun y => a (affineSum (mean+e) L y)) Y)
    (fractionDifferences (block choices factor) (fun y => a (affineSum mean L y)) Y)
  have hold : |fractionDifferences (block choices factor) (fun y => a (affineSum (mean+e) L y)) Y -
      fractionDifferences (block choices factor) (fun y => a (affineSum mean L y)) Y| ≤
      (2 : ℝ)^((block choices factor).length)*H*|L i (x i)|^β := by
    rw [hp]
    nlinarith
  rw [mul_min_of_nonneg _ _ (mul_nonneg (by positivity) hH)]
  exact le_min (by convert! hc using 1; ring) hold

def value {n r k : ℕ} (choices : List (Fin r × Fin k)) (factor : Fin k) (a : ℝ → ℝ)
    (mean : State n → ℝ) (L : Fin r → State n →L[ℝ] ℝ) (e : ℝ)
    (x : (Fin r → State n) × State n) : ℝ :=
  jointBlock choices factor a (fun y => mean y+e) L x-jointBlock choices factor a mean L x

/-- Fractional current input and the complementary old rough exponent
are retained before expectation. No product independence is used. -/
theorem value_interpolated_bound {n r k : ℕ}
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (i : Fin r) (hi : i ∈ block choices factor) (a : ℝ → ℝ) {H β χ : ℝ}
    (hH : 0 ≤ H) (hχ : 0 ≤ χ) (hχβ : χ ≤ β)
    (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β)
    (mean : State n → ℝ) (L : Fin r → State n →L[ℝ] ℝ) (e : ℝ)
    (x : (Fin r → State n) × State n) :
    |value choices factor a mean L e x| ≤
      (2 : ℝ)^((block choices factor).length)*H*|e|^χ*|L i (x.1 i)|^(β-χ) := by
  have hh := paired_min_bound choices hnd factor i hi a hH hholder (mean x.2) e L x.1
  have hm := mul_le_mul_of_nonneg_left
    (min_rpow_le (abs_nonneg e) (abs_nonneg (L i (x.1 i))) hχ hχβ)
    (show 0 ≤ (2 : ℝ)^((block choices factor).length)*H by positivity)
  convert! hh.trans hm using 1
  ring

theorem value_even_moment {n r k : ℕ} (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r × Fin k))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k) (i : Fin r) (hi : i ∈ block choices factor)
    (a : ℝ → ℝ) (ha : Measurable a) {H β χ : ℝ} (hH : 0 ≤ H) (hχ : 0 ≤ χ) (hχβ : χ ≤ β)
    (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β)
    (mean : State n → ℝ) (hm : Measurable mean) (L : Fin r → State n →L[ℝ] ℝ) (e : ℝ) (p : ℕ) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |value choices factor a mean L e x|^(2*p)) μ ∧
      (∫ x,|value choices factor a mean L e x|^(2*p) ∂μ) ≤
        GaussianAudit.gaussianAbsMoment (((2*p : ℕ) : ℝ)*(β-χ))*
          ((2 : ℝ)^((block choices factor).length)*H*|e|^χ*
            Var[L i;multivariateGaussian 0 (A i)]^((β-χ)/2))^(2*p) := by
  intro μ
  have hv : Measurable (value choices factor a mean L e) :=
    (jointBlock_measurable choices factor a ha _ (hm.add_const e) L).sub
      (jointBlock_measurable choices factor a ha mean hm L)
  have hh := dominated_even_moment μ _ _ (old_projection_hasLaw A B L i) hv
    (show 0 ≤ (2 : ℝ)^((block choices factor).length)*H*|e|^χ by positivity)
    (sub_nonneg.mpr hχβ) (value_interpolated_bound choices hnd factor i hi a hH hχ hχβ hholder mean L e) p
  simpa only [Real.coe_toNNReal _ (variance_nonneg (L i) (multivariateGaussian (0 : State n) (A i)))] using hh

end SHE.PairedRoughBlocks
