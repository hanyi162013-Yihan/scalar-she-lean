module

public import SHEStochastic.MatrixPastedBrownianPast
public import SHEStochastic.MatrixBlockProcessAdapted

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixGlobalBlockIncrementLaw
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0)

def increments {m : ℕ} (k : ℕ) (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0)
    (p : MatrixGlobalBlockPath.Space (n := n) H) : WordRecursion.State m :=
  WithLp.toLp 2 (fun i => MatrixGlobalBlockPath.driver H (a i) ((k : ℝ≥0)*H+t) p-
    MatrixGlobalBlockPath.driver H (a i) ((k : ℝ≥0)*H+s) p)

theorem increments_eq (hH : 0<H) {m : ℕ} (k : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hs : s≤H) (ht : t≤H) (p : MatrixGlobalBlockPath.Space (n := n) H) :
    increments H k a s t p=MatrixFreshBlockBrownian.increments (H := H) a s t (p k) := by
  apply PiLp.ext
  intro i
  have h := MatrixGlobalBlockPath.driver_increment H hH (a i) p k t ht
  have h' := MatrixGlobalBlockPath.driver_increment H hH (a i) p k s hs
  change MatrixGlobalBlockPath.driver H (a i) ((k : ℝ≥0)*H+t) p-
    MatrixGlobalBlockPath.driver H (a i) ((k : ℝ≥0)*H+s) p=_
  dsimp only [MatrixFreshBlockBrownian.increments,WithLp.ofLp_toLp]
  linarith only [h,h']

variable {H} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

/-- Every local window, including the first block, has its Gaussian
increment law jointly independently of the full physical global past. -/
theorem product_law (hH0 : 0<H) (k m : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hst : s≤t) (ht : t≤H) :
    (D.law ρ₀).map (fun p => (MatrixBlockNaturalFiltration.history H ((k : ℝ≥0)*H+s) p,
      increments H k a s t p))=
      ((D.law ρ₀).map (MatrixBlockNaturalFiltration.history H ((k : ℝ≥0)*H+s))).prod
        (multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a (fun _ => t-s))) := by
  let g := CanonicalStateDriverFiltration.history (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H s
  have hg : Measurable[CanonicalStateDriverFiltration.filtration H s] g := Measurable.of_comap_le le_rfl
  have hgm := CanonicalStateDriverFiltration.history_measurable (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H s
  let f := MatrixFreshBlockBrownian.increments (H := H) a s t
  have hfm : Measurable f := MatrixFreshBlockBrownian.increments_measurable a s t
  let ν := multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a (fun _ => t-s))
  cases k with
  | zero =>
    have hPair := MatrixFreshBlockBrownian.block_local_past_law D ρ₀ 0 m a s t hst ht g hg
    rw [←D.marginals ρ₀ 0,Measure.map_map (hgm.prodMk hfm) (measurable_pi_apply 0),
      Measure.map_map hgm (measurable_pi_apply 0)] at hPair
    have hh := KernelFixedStatisticLaw.map_first (D.law ρ₀) (g ∘ fun p => p 0) (f ∘ fun p => p 0)
      (hgm.comp (measurable_pi_apply 0)) (hfm.comp (measurable_pi_apply 0)) ν hPair
      (MatrixBlockPastFactor.initialAssemble H) (MatrixBlockPastFactor.initialAssemble_measurable H)
    have he : MatrixBlockPastFactor.initialAssemble H ∘ (g ∘ fun p => p 0)=
        MatrixBlockNaturalFiltration.history (n := n) H s :=
      funext (fun p => (MatrixBlockPastFactor.initial_history H s (hst.trans ht) p).symm)
    have hf : (f ∘ fun p => p 0)=increments H 0 a s t :=
      (funext (increments_eq H hH0 0 a s t (hst.trans ht) ht)).symm
    change (D.law ρ₀).map (fun p => ((MatrixBlockPastFactor.initialAssemble H ∘ (g ∘ fun p => p 0)) p,
      (f ∘ fun p => p 0) p))=_ at hh
    rw [he,hf] at hh
    simpa only [Nat.cast_zero,zero_mul,zero_add] using hh
  | succ j =>
    have hPair := MatrixFreshBlockBrownian.prefix_local_past_law D ρ₀ j m a s t hst ht g hg
    let past := MatrixPastedBrownianPast.past (n := n) H j s
    have hp := MatrixPastedBrownianPast.past_measurable (n := n) H j s
    have hh := KernelFixedStatisticLaw.map_first (D.law ρ₀) past (f ∘ fun p => p (j+1)) hp
      (hfm.comp (measurable_pi_apply (j+1))) ν hPair
      (MatrixBlockPastFactor.assemble H j s) (MatrixBlockPastFactor.assemble_measurable H j s)
    have he : MatrixBlockPastFactor.assemble H j s ∘ past=
        MatrixBlockNaturalFiltration.history (n := n) H (((j+1 : ℕ) : ℝ≥0)*H+s) :=
      funext (fun p => (MatrixBlockPastFactor.history_eq H hH0 j s (hst.trans ht) p).symm)
    have hf : (f ∘ fun p => p (j+1))=increments H (j+1) a s t :=
      (funext (increments_eq H hH0 (j+1) a s t (hst.trans ht) ht)).symm
    change (D.law ρ₀).map (fun p => ((MatrixBlockPastFactor.assemble H j s ∘ past) p,
      (f ∘ fun p => p (j+1)) p))=_ at hh
    rw [he,hf] at hh
    exact hh

end SHEStochastic.MatrixGlobalBlockIncrementLaw
