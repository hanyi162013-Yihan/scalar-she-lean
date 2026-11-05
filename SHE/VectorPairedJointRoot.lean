module

public import SHE.VectorJointRoot
public import SHE.VectorPairedRootClips
public import SHE.PairedRoughBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.VectorPairedJointRoot
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianClipMoments
open scoped BigOperators NNReal
variable {n d r m : ℕ}

def value (choices : List (Fin r × Fin m)) (factor : Fin m) (F : State d → ℝ)
    (mean : State n → State d) (L : Fin r → State n →L[ℝ] State d)
    (e : State d) (x : (Fin r → State n) × State n) : ℝ :=
  VectorJointRoot.value choices factor F (fun y => mean y+e) L x-
    VectorJointRoot.value choices factor F mean L x

theorem measurable_value (choices : List (Fin r × Fin m)) (factor : Fin m) (F : State d → ℝ)
    (hF : Measurable F) (mean : State n → State d) (hm : Measurable mean)
    (L : Fin r → State n →L[ℝ] State d) (e : State d) :
    Measurable (value choices factor F mean L e) :=
  (VectorJointRoot.measurable_value choices factor F hF _ (hm.add_const e) L).sub
    (VectorJointRoot.measurable_value choices factor F hF mean hm L)

/-- Pairing the actual current root shift with the old block keeps its
fractional current clip and every original assigned old vector clip. -/
theorem pointwise_bound (choices : List (Fin r × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin m) (F : State d → ℝ)
    {A0 ν χ : ℝ} (hA0 : 0≤A0) (hν : 0≤ν) (hχ0 : 0≤χ) (hχ1 : χ≤1)
    (hF : ContDiff ℝ ((block choices factor).length+1) F)
    (hb : ∀ j,j≤(block choices factor).length+1 → ∀ z,
      ‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (mean : State n → State d) (L : Fin r → State n →L[ℝ] State d)
    (e : State d) (x : (Fin r → State n) × State n) :
    |value choices factor F mean L e x| ≤
      (2 : ℝ)^((block choices factor).length+1)*A0*(min 1 (ν*‖e‖))^χ*
        VectorFiniteDifferences.clips ν ((block choices factor).map (fun i => L i (x.1 i))) := by
  let is := block choices factor
  let y := suppress (suppressed choices factor) x.1
  have he : value choices factor F mean L e x =
      fractionDifferences is (fun z => F (VectorRootClips.affineSum (mean x.2) L z+e)-
        F (VectorRootClips.affineSum (mean x.2) L z)) y := by
    rw [PairedRoughBlocks.differences_sub]
    unfold value VectorJointRoot.value
    congr 2
    funext z
    congr 1
    unfold VectorRootClips.affineSum
    simp only [add_assoc,add_comm]
  rw [he]
  have hmix := VectorRootClips.fractionDifferences_eq_mixed is (block_nodup choices hnd factor)
    (fun z => F (z+e)-F z) (mean x.2) L y
  change fractionDifferences is (fun z => (fun w => F (w+e)-F w)
    (VectorRootClips.affineSum (mean x.2) L z)) y = _ at hmix
  rw [hmix,VectorFiniteDifferences.mixed_current_difference]
  have hm : is.map (fun i => L i (y i)) = is.map (fun i => L i (x.1 i)) := by
    apply List.map_congr_left
    intro i hi
    rw [show y i=x.1 i from suppress_assigned_coordinate choices hnd factor hi x.1]
  rw [hm]
  have hf' : ContDiff ℝ ((is.map (fun i => L i (x.1 i))).length+1) F := by simpa using hF
  have hb' : ∀ j,j≤(is.map (fun i => L i (x.1 i))).length+1 → ∀ z,
      ‖iteratedFDeriv ℝ j F z‖≤A0*ν^j := by simpa using hb
  simpa only [Real.norm_eq_abs,List.length_map] using
    VectorFiniteDifferences.paired_mixed_bound_finite F (is.map (fun i => L i (x.1 i)))
      hA0 hν hχ0 hχ1 hf' hb' e (VectorRootClips.affineSum (mean x.2) L (suppress is y))

/-- The paired current/root estimate under the genuine old/residual
Gaussian product. Dependence of all old coordinates and their scores is
retained; the current clip is outside this conditional Gaussian integral. -/
theorem even_moment (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin m)
    (hlen : 0<(block choices factor).length) (F : State d → ℝ)
    {A0 ν χ : ℝ} (hA0 : 0≤A0) (hν : 0≤ν) (hχ0 : 0≤χ) (hχ1 : χ≤1)
    (hF : ContDiff ℝ ((block choices factor).length+1) F)
    (hb : ∀ j,j≤(block choices factor).length+1 → ∀ z,
      ‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (mean : State n → State d) (hm : Measurable mean)
    (L : Fin r → State n →L[ℝ] State d) (V : Fin r → ℝ≥0)
    (hv : ∀ j i,Var[(EuclideanSpace.proj (𝕜:=ℝ) i).comp (L j);
      multivariateGaussian 0 (A j)]≤(V j : ℝ)) (e : State d) (p : ℕ) (hp : 0<p) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |value choices factor F mean L e x|^(2*p)) μ ∧
      (∫ x,|value choices factor F mean L e x|^(2*p) ∂μ) ≤
        clipMomentConstant (p*(block choices factor).length)*
          ((2 : ℝ)^((block choices factor).length+1)*A0*(min 1 (ν*‖e‖))^χ*
            (d : ℝ)^((block choices factor).length)*
            (∏ j : Fin (block choices factor).length,
              min 1 (ν*sqrt (V ((block choices factor).get j) : ℝ))))^(2*p) := by
  intro μ
  let is := block choices factor
  let X := fun (j : Fin is.length) (x : (Fin r → State n) × State n) =>
    L (is.get j) (x.1 (is.get j))
  let ell := fun (j : Fin is.length) (i : Fin d) =>
    (EuclideanSpace.proj (𝕜:=ℝ) i).comp (L (is.get j))
  let v := fun (j : Fin is.length) (i : Fin d) =>
    (Var[ell j i;multivariateGaussian 0 (A (is.get j))]).toNNReal
  have hX : ∀ j i,HasLaw (fun x => X j x i) (gaussianReal 0 (v j i)) μ := by
    intro j i
    exact JointGaussianBlocks.old_projection_hasLaw A B (fun _ => ell j i) (is.get j)
  have hcap (j : Fin is.length) (i : Fin d) : v j i≤V (is.get j) :=
    Real.toNNReal_le_iff_le_coe.mpr (hv (is.get j) i)
  have he (x : (Fin r → State n) × State n) :
      VectorFiniteDifferences.clips ν (is.map (fun i => L i (x.1 i))) =
        ∏ j : Fin is.length,min 1 (ν*‖X j x‖) := by
    have hh := congrArg (fun l : List (Fin r) => l.map (fun i => min 1 (ν*‖L i (x.1 i)‖)))
      (List.ofFn_get is)
    simp only [List.map_ofFn] at hh
    unfold VectorFiniteDifferences.clips
    rw [List.map_map]
    change (is.map (fun i => min 1 (ν*‖L i (x.1 i)‖))).prod = _
    rw [←hh,Fin.prod_ofFn]
    rfl
  have hd (x : (Fin r → State n) × State n) :
      |value choices factor F mean L e x| ≤
        ((2 : ℝ)^(is.length+1)*A0*(min 1 (ν*‖e‖))^χ)*
          (∏ j : Fin is.length,min 1 (ν*‖X j x‖)) := by
    have hh := pointwise_bound choices hnd factor F hA0 hν hχ0 hχ1 hF hb mean L e x
    rw [he] at hh
    exact hh
  exact VectorGaussianClips.dominated_even_moment μ hlen X (by intro j;dsimp [X];fun_prop)
    v (fun j => V (is.get j)) hX hcap hν (by positivity)
    (value choices factor F mean L e)
    (measurable_value choices factor F hF.continuous.measurable mean hm L e) hd p hp

end SHE.VectorPairedJointRoot
