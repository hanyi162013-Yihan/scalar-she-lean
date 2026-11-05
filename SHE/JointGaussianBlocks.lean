module

public import SHE.GaussianRootBlockMoments
public import SHE.OldIntervalScoreMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointGaussianBlocks
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianAssignmentBlocks GaussianVectorFractions GaussianRoughBlocks GaussianRoughBlockMoments
  GaussianRootClipBlocks GaussianClipMoments GaussianClipProducts GaussianEnvelopeMoments
open scoped BigOperators NNReal
variable {n r k : ℕ}

def jointBlock (choices : List (Fin r × Fin k)) (factor : Fin k) (a : ℝ → ℝ)
    (mean : State n → ℝ) (L : Fin r → State n →L[ℝ] ℝ)
    (x : (Fin r → State n) × State n) : ℝ :=
  blockFunction choices factor a (mean x.2) L x.1

theorem measurable_parameterDifferences (is : List (Fin r))
    (F : (Fin r → State n) × State n → ℝ) (hF : Measurable F) :
    Measurable (fun x : (Fin r → State n) × State n =>
      fractionDifferences is (fun y => F (y,x.2)) x.1) := by
  induction is with
  | nil => exact hF
  | cons i is ih =>
    change Measurable (fun x : (Fin r → State n) × State n =>
      fractionDifferences is (fun y => F (y,x.2)) x.1 -
        fractionDifferences is (fun y => F (y,x.2)) (Function.update x.1 i 0))
    have ht : Measurable (fun x : (Fin r → State n) × State n =>
        (Function.update x.1 i 0,x.2)) := by fun_prop
    exact ih.sub (ih.comp ht)

theorem jointBlock_measurable (choices : List (Fin r × Fin k)) (factor : Fin k) (a : ℝ → ℝ)
    (ha : Measurable a) (mean : State n → ℝ) (hm : Measurable mean)
    (L : Fin r → State n →L[ℝ] ℝ) : Measurable (jointBlock choices factor a mean L) := by
  have hF : Measurable (fun x : (Fin r → State n) × State n => a (affineSum (mean x.2) L x.1)) := by
    unfold affineSum
    fun_prop
  exact (measurable_parameterDifferences _ _ hF).comp ((measurable_suppress _).prodMap measurable_id)

theorem old_projection_hasLaw (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (L : Fin r → State n →L[ℝ] ℝ) (i : Fin r) :
    HasLaw (fun x : (Fin r → State n) × State n => L i (x.1 i))
      (gaussianReal 0 (Var[L i;multivariateGaussian 0 (A i)]).toNNReal)
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B)) :=
  (selected_projection_hasLaw A L i).fun_comp
    (measurePreserving_fst (μ := Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))
      (ν := multivariateGaussian (0 : State n) B)).hasLaw

/-- The residual base is retained inside every actual rough difference;
the selected old increment still gives the same minimum-gap moment. -/
theorem rough_block_even_moment (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r × Fin k))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k) (i : Fin r)
    (hi : i ∈ block choices factor) (a : ℝ → ℝ) (ha : Measurable a)
    (mean : State n → ℝ) (hm : Measurable mean) (L : Fin r → State n →L[ℝ] ℝ)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β) (p : ℕ) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |jointBlock choices factor a mean L x|^(2*p)) μ ∧
      (∫ x, |jointBlock choices factor a mean L x|^(2*p) ∂μ) ≤
        gaussianAbsMoment (((2*p : ℕ) : ℝ)*β)*
          ((2 : ℝ)^((block choices factor).length-1)*H*
            Var[L i;multivariateGaussian 0 (A i)]^(β/2))^(2*p) := by
  intro μ
  have hb (x : (Fin r → State n) × State n) : |jointBlock choices factor a mean L x| ≤
      ((2 : ℝ)^((block choices factor).length-1)*H)*|L i (x.1 i)|^β :=
    suppressed_rough_block_bound choices hnd factor i hi a H β hholder (mean x.2) L x.1
  have hh := dominated_even_moment μ _ _ (old_projection_hasLaw A B L i)
    (jointBlock_measurable choices factor a ha mean hm L)
    (show 0 ≤ (2 : ℝ)^((block choices factor).length-1)*H by positivity) hβ hb p
  simpa only [Real.coe_toNNReal _ (variance_nonneg (L i) (multivariateGaussian (0 : State n) (A i)))] using hh

/-- Every original root clip survives joint integration over all old
fractions and the residual. No rough-factor/score independence is used. -/
theorem root_block_even_moment (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r × Fin k))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (hlen : 0 < (block choices factor).length) (f : ℕ → ℝ → ℝ)
    {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ∀ j, j < (block choices factor).length → ∀ z, HasDerivAt (f j) (f (j+1) z) z)
    (hfb : ∀ j, j ≤ (block choices factor).length → ∀ z, |f j z| ≤ A0*ν^j)
    (mean : State n → ℝ) (hm : Measurable mean) (L : Fin r → State n →L[ℝ] ℝ) (p : ℕ) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |jointBlock choices factor (f 0) mean L x|^(2*p)) μ ∧
      (∫ x, |jointBlock choices factor (f 0) mean L x|^(2*p) ∂μ) ≤
        clipMomentConstant (p*(block choices factor).length)*
          ((2 : ℝ)^((block choices factor).length)*A0*
            (∏ j : Fin (block choices factor).length, min 1
              (ν*sqrt (Var[L ((block choices factor).get j);
                multivariateGaussian 0 (A ((block choices factor).get j))]))))^(2*p) := by
  intro μ
  let is := block choices factor
  let X := fun (j : Fin is.length) (x : (Fin r → State n) × State n) => L (is.get j) (x.1 (is.get j))
  let v := fun j : Fin is.length => (Var[L (is.get j);multivariateGaussian 0 (A (is.get j))]).toNNReal
  have hX : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) μ := fun j => old_projection_hasLaw A B L (is.get j)
  have hfc : Measurable (f 0) :=
    (continuous_iff_continuousAt.mpr (fun z => (hf 0 hlen z).continuousAt)).measurable
  have hb (x : (Fin r → State n) × State n) :
      |jointBlock choices factor (f 0) mean L x| ≤ ((2 : ℝ)^is.length*A0)*(∏ j,clip ν (X j x)) :=
    root_block_clipped_bound choices hnd factor f hA0 hν hf hfb (mean x.2) L x.1
  have hh := GaussianClipProducts.dominated_even_moment μ hlen X (by intro j; fun_prop) v hX hν
    (show 0 ≤ (2 : ℝ)^is.length*A0 by positivity) _
    (jointBlock_measurable choices factor (f 0) hfc mean hm L) hb p
  have hv (j : Fin is.length) : (v j : ℝ) = Var[L (is.get j);multivariateGaussian 0 (A (is.get j))] :=
    Real.coe_toNNReal _ (variance_nonneg _ _)
  simpa only [hv] using hh

end SHE.JointGaussianBlocks
