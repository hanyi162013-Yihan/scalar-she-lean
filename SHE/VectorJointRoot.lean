module

public import SHE.VectorGaussianClips
public import SHE.JointGaussianBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.VectorJointRoot
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit GaussianVectorFractions
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianClipMoments
open scoped BigOperators NNReal
variable {n d r m : ℕ}

def value (choices : List (Fin r × Fin m)) (factor : Fin m) (F : State d → ℝ)
    (mean : State n → State d) (L : Fin r → State n →L[ℝ] State d)
    (x : (Fin r → State n) × State n) : ℝ :=
  fractionDifferences (block choices factor)
    (fun y => F (VectorRootClips.affineSum (mean x.2) L y))
    (suppress (suppressed choices factor) x.1)

theorem measurable_value (choices : List (Fin r × Fin m)) (factor : Fin m) (F : State d → ℝ)
    (hF : Measurable F) (mean : State n → State d) (hm : Measurable mean)
    (L : Fin r → State n →L[ℝ] State d) : Measurable (value choices factor F mean L) := by
  have h : Measurable (fun x : (Fin r → State n) × State n =>
      F (VectorRootClips.affineSum (mean x.2) L x.1)) := by
    unfold VectorRootClips.affineSum
    fun_prop
  exact (JointGaussianBlocks.measurable_parameterDifferences _ _ h).comp
    ((measurable_suppress _).prodMap measurable_id)

/-- Full finite-cylinder root moments under the actual old/residual
product law. Every original old-gap clip survives, with only a finite
root-dimension constant. The residual remains inside the root cylinder. -/
theorem root_even_moment (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin m)
    (hlen : 0 < (block choices factor).length) (F : State d → ℝ)
    {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hF : ContDiff ℝ (block choices factor).length F)
    (hb : ∀ j, j ≤ (block choices factor).length → ∀ z,
      ‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (mean : State n → State d) (hm : Measurable mean)
    (L : Fin r → State n →L[ℝ] State d) (V : Fin r → ℝ≥0)
    (hv : ∀ j i, Var[(EuclideanSpace.proj (𝕜 := ℝ) i).comp (L j);
      multivariateGaussian 0 (A j)] ≤ (V j : ℝ)) (p : ℕ) (hp : 0 < p) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |value choices factor F mean L x|^(2*p)) μ ∧
      (∫ x,|value choices factor F mean L x|^(2*p) ∂μ) ≤
        clipMomentConstant (p*(block choices factor).length)*
          ((2 : ℝ)^((block choices factor).length)*A0*(d : ℝ)^((block choices factor).length)*
            (∏ j : Fin (block choices factor).length,
              min 1 (ν*sqrt (V ((block choices factor).get j) : ℝ))))^(2*p) := by
  intro μ
  let is := block choices factor
  let X := fun (j : Fin is.length) (x : (Fin r → State n) × State n) =>
    L (is.get j) (x.1 (is.get j))
  let ell := fun (j : Fin is.length) (i : Fin d) =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp (L (is.get j))
  let v := fun (j : Fin is.length) (i : Fin d) =>
    (Var[ell j i;multivariateGaussian 0 (A (is.get j))]).toNNReal
  have hX : ∀ j i, HasLaw (fun x => X j x i) (gaussianReal 0 (v j i)) μ := by
    intro j i
    exact JointGaussianBlocks.old_projection_hasLaw A B (fun _ => ell j i) (is.get j)
  have hcap (j : Fin is.length) (i : Fin d) : v j i ≤ V (is.get j) := by
    exact Real.toNNReal_le_iff_le_coe.mpr (hv (is.get j) i)
  have he (x : (Fin r → State n) × State n) :
      VectorFiniteDifferences.clips ν (is.map (fun i => L i (x.1 i))) =
        ∏ j : Fin is.length,min 1 (ν*‖X j x‖) := by
    have hh := congrArg (fun l : List (Fin r) => l.map (fun i => min 1 (ν*‖L i (x.1 i)‖)))
      (List.ofFn_get is)
    simp only [List.map_ofFn] at hh
    unfold VectorFiniteDifferences.clips
    rw [List.map_map]
    change (is.map (fun i => min 1 (ν*‖L i (x.1 i)‖))).prod = _
    rw [← hh,Fin.prod_ofFn]
    rfl
  have hd (x : (Fin r → State n) × State n) :
      |value choices factor F mean L x| ≤
        ((2 : ℝ)^is.length*A0)*(∏ j : Fin is.length,min 1 (ν*‖X j x‖)) := by
    have hh := VectorRootClips.root_block_clipped_bound choices hnd factor F hA0 hν hF hb (mean x.2) L x.1
    rw [he] at hh
    exact hh
  exact VectorGaussianClips.dominated_even_moment μ hlen X (by intro j; dsimp [X]; fun_prop)
    v (fun j => V (is.get j)) hX hcap hν (by positivity)
    (value choices factor F mean L) (measurable_value choices factor F hF.continuous.measurable mean hm L) hd p hp

end SHE.VectorJointRoot
