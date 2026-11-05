module

public import SHEStochastic.KernelMarkovFreshLaw
public import SHE.GaussianIncrement

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.KernelMarkovGaussianSum
open MeasureTheory ProbabilityTheory SHE.GaussianIncrement
variable {X : Type*} [MeasurableSpace X] {m : ℕ}

def sum (f : ℕ → X → State m) (M : ℕ) (p : ℕ → X) : State m :=
  ∑ k : Fin (M+1),f k (p k)

theorem sum_measurable (f : ℕ → X → State m) (hf : ∀ k,Measurable (f k)) (M : ℕ) :
    Measurable (sum f M) := by
  exact Finset.measurable_sum _ (fun k _ => (hf k).comp (measurable_pi_apply (k : ℕ)))

/-- Finite Gaussian contributions from a continuation chain may be
summed without replacing the chain by an artificial independent space.
Each fresh statistic must retain its law jointly with the entire prefix. -/
theorem law (Q : Measure (ℕ → X)) [IsProbabilityMeasure Q]
    (f : ℕ → X → State m) (hf : ∀ k,Measurable (f k))
    (A : ℕ → Matrix (Fin m) (Fin m) ℝ) (hA : ∀ k,(A k).PosSemidef)
    (h0 : HasLaw (fun p => f 0 (p 0)) (multivariateGaussian (0 : State m) (A 0)) Q)
    (hFresh : ∀ j,Q.map (fun p => (Preorder.frestrictLe j p,f (j+1) (p (j+1))))=
      (Q.map (Preorder.frestrictLe j)).prod (multivariateGaussian (0 : State m) (A (j+1))))
    (M : ℕ) : HasLaw (sum f M) (multivariateGaussian (0 : State m) (∑ k : Fin (M+1),A k)) Q := by
  induction M with
  | zero =>
    have he : sum f 0=(fun p => f 0 (p 0)) := by
      funext p
      simp [KernelMarkovGaussianSum.sum]
    rw [he]
    simpa using h0
  | succ M ih =>
    let g := fun z : (i : Finset.Iic M) → X =>
      ∑ k : Fin (M+1),f k (z ⟨k,Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩)
    have hg : Measurable g := by
      exact Finset.measurable_sum _ (fun k _ => (hf k).comp
        (measurable_pi_apply (⟨k,Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩ : Finset.Iic M)))
    have hp : Measurable (Preorder.frestrictLe (α := ℕ) (π := fun _ => X) M) := by fun_prop
    have hn : Measurable (fun p : ℕ → X => f (M+1) (p (M+1))) :=
      (hf (M+1)).comp (measurable_pi_apply (M+1))
    have hPair := hFresh M
    have hNext : HasLaw (fun p => f (M+1) (p (M+1)))
        (multivariateGaussian (0 : State m) (A (M+1))) Q := by
      refine ⟨hn.aemeasurable,?_⟩
      have hh := congrArg (fun η => η.map Prod.snd) hPair
      rw [Measure.map_map measurable_snd (hp.prodMk hn),Measure.map_snd_prod] at hh
      simpa only [Function.comp_def,Measure.map_apply hp MeasurableSet.univ,
        Set.preimage_univ,measure_univ,one_smul] using hh
    have hi : IndepFun (Preorder.frestrictLe M) (fun p => f (M+1) (p (M+1))) Q :=
      (indepFun_iff_map_prod_eq_prod_map_map hp.aemeasurable hn.aemeasurable).mpr
        (hPair.trans (congrArg (fun η => (Q.map (Preorder.frestrictLe M)).prod η) hNext.map_eq.symm))
    have hi' : IndepFun (sum f M) (fun p => f (M+1) (p (M+1))) Q :=
      hi.comp hg measurable_id
    have hadd := hi'.hasLaw_add ih hNext
    rw [gaussian_convolution (Matrix.posSemidef_sum (Finset.univ : Finset (Fin (M+1)))
      (fun k _ => hA k)) (hA (M+1))] at hadd
    have he : sum f (M+1)=sum f M+(fun p => f (M+1) (p (M+1))) := by
      funext p
      exact Fin.sum_univ_castSucc (fun k : Fin (M+1+1) => f k (p k))
    have hcov : (∑ k : Fin (M+1+1),A k)=(∑ k : Fin (M+1),A k)+A (M+1) :=
      Fin.sum_univ_castSucc (fun k : Fin (M+1+1) => A k)
    rw [he,hcov]
    exact hadd

end SHEStochastic.KernelMarkovGaussianSum
