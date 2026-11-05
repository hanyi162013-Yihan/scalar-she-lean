module

public import SHEStochastic.MatrixFreshBlockBrownian
public import SHEStochastic.MatrixBlockPastFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixPastedBrownianPast
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0)

def past (j : ℕ) (s : ℝ≥0) (p : MatrixGlobalBlockPath.Space (n := n) H) :=
  (Preorder.frestrictLe j p,CanonicalStateDriverFiltration.history H s (p (j+1)))

theorem past_measurable (j : ℕ) (s : ℝ≥0) : Measurable (past (n := n) H j s) := by
  exact (by fun_prop : Measurable (Preorder.frestrictLe j)).prodMk
    ((CanonicalStateDriverFiltration.history_measurable H s).comp (measurable_pi_apply (j+1)))

def increments {m : ℕ} (j : ℕ) (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0)
    (p : MatrixGlobalBlockPath.Space (n := n) H) : SHE.WordRecursion.State m :=
  WithLp.toLp 2 (fun i =>
    MatrixGlobalBlockPath.driver H (a i) (((j+1 : ℕ) : ℝ≥0)*H+t) p-
      MatrixGlobalBlockPath.driver H (a i) (((j+1 : ℕ) : ℝ≥0)*H+s) p)

/-- The literal global increment on one local window is its original
local driver increment, with all anchoring constants cancelling exactly. -/
theorem increments_eq (hH : 0<H) {m : ℕ} (j : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hs : s≤H) (ht : t≤H) (p : MatrixGlobalBlockPath.Space (n := n) H) :
    increments H j a s t p=MatrixFreshBlockBrownian.increments (H := H) a s t (p (j+1)) := by
  apply PiLp.ext
  intro i
  have h := MatrixGlobalBlockPath.driver_increment H hH (a i) p (j+1) t ht
  have h' := MatrixGlobalBlockPath.driver_increment H hH (a i) p (j+1) s hs
  change MatrixGlobalBlockPath.driver H (a i) (((j+1 : ℕ) : ℝ≥0)*H+t) p-
    MatrixGlobalBlockPath.driver H (a i) (((j+1 : ℕ) : ℝ≥0)*H+s) p=_
  dsimp only [MatrixFreshBlockBrownian.increments,WithLp.ofLp_toLp]
  linarith only [h,h']

variable {H} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

/-- Each genuine local window of the globally pasted driver has
increments independent of the ENTIRE physical state-and-driver past.
No driver-only filtration or new stochastic input is used. -/
theorem independent (hH0 : 0<H) (j m : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hst : s≤t) (ht : t≤H) :
    Indep (MeasurableSpace.comap (increments H j a s t) inferInstance)
      (MatrixBlockNaturalFiltration.filtration H (((j+1 : ℕ) : ℝ≥0)*H+s)) (D.law ρ₀) := by
  let g := CanonicalStateDriverFiltration.history (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H s
  have hg : Measurable[CanonicalStateDriverFiltration.filtration H s] g :=
    Measurable.of_comap_le le_rfl
  have hPair := MatrixFreshBlockBrownian.prefix_local_past_law D ρ₀ j m a s t hst ht g hg
  let f := fun p : MatrixGlobalBlockPath.Space (n := n) H =>
    MatrixFreshBlockBrownian.increments (H := H) a s t (p (j+1))
  let ν := multivariateGaussian (0 : SHE.WordRecursion.State m)
    (BrownianFiniteCovariance.matrix a (fun _ => t-s))
  have hp : Measurable (past (n := n) H j s) := past_measurable H j s
  have hf : Measurable f := (MatrixFreshBlockBrownian.increments_measurable a s t).comp
    (measurable_pi_apply (j+1))
  have he : (D.law ρ₀).map (fun p => (past H j s p,f p))=
      ((D.law ρ₀).map (past H j s)).prod ν := hPair
  have hLaw : (D.law ρ₀).map f=ν := by
    have he' := congrArg (fun η => η.map Prod.snd) he
    rw [Measure.map_map measurable_snd (hp.prodMk hf),Measure.map_snd_prod] at he'
    simpa only [Function.comp_def,Measure.map_apply hp MeasurableSet.univ,Set.preimage_univ,
      measure_univ,one_smul] using he'
  have hInd : IndepFun (past H j s) f (D.law ρ₀) :=
    (indepFun_iff_map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable).mpr
      (he.trans (congrArg (fun η => ((D.law ρ₀).map (past H j s)).prod η) hLaw.symm))
  have hInd' := (IndepFun_iff_Indep _ _ _).mp hInd
  have hPhys := (indep_of_indep_of_le_left hInd'
    (MatrixBlockPastFactor.past_le H hH0 j s (hst.trans ht))).symm
  have hfun : increments H j a s t=f := funext (increments_eq H hH0 j a s t (hst.trans ht) ht)
  rw [hfun]
  exact hPhys

end SHEStochastic.MatrixPastedBrownianPast
