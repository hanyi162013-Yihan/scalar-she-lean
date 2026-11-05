module

public import SHEStochastic.SequentialIndependence
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import all Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FiniteIncrementLawComparison
open MeasureTheory ProbabilityTheory

variable {Ω E T : Type*} [MeasurableSpace Ω] [LinearOrder T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (F : Filtration T ‹MeasurableSpace Ω›) (X : T → Ω → E)

/-- Ordered increments are jointly independent because all previous
increments are measurable at the next left endpoint. -/
theorem increments_indep
    (hX : ∀ t, Measurable[F t] (X t))
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ X t ω-X s ω) inferInstance) (F s) μ)
    {n : ℕ} (t : Fin (n+1) → T) (ht : Monotone t) :
    iIndepFun (fun i : Fin n ↦ fun ω ↦ X (t i.succ) ω-X (t i.castSucc) ω) μ := by
  apply SequentialIndependence.iIndepFun μ (fun i : Fin n ↦ F (t i.castSucc))
  · intro i j hji
    have hj : j.succ ≤ i.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.succ_le_of_lt hji
    have hj' : j.castSucc ≤ i.castSucc := (Fin.castSucc_le_succ j).trans hj
    exact ((hX _).mono (F.mono (ht hj)) le_rfl).sub
      ((hX _).mono (F.mono (ht hj')) le_rfl)
  · intro i
    exact hInd _ _ (ht (Fin.castSucc_le_succ i))

section Comparison
variable {Ξ : Type*} [MeasurableSpace Ξ] [OrderBot T]
  (ν : Measure Ξ) [IsProbabilityMeasure ν]
  (G : Filtration T ‹MeasurableSpace Ξ›) (Y : T → Ξ → E)

/-- Equality of all increment laws together with full-past independence
determines all finite-dimensional process laws. Existing telescoping and
product-law results supply the reconstruction. -/
theorem restrict_law
    (hX : ∀ t, Measurable[F t] (X t)) (hY : ∀ t, Measurable[G t] (Y t))
    (hzeroX : ∀ᵐ ω ∂μ, X ⊥ ω = 0) (hzeroY : ∀ᵐ ω ∂ν, Y ⊥ ω = 0)
    (hInc : ∀ s t, s ≤ t →
      IdentDistrib (fun ω ↦ X t ω-X s ω) (fun ω ↦ Y t ω-Y s ω) μ ν)
    (hIndX : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ X t ω-X s ω) inferInstance) (F s) μ)
    (hIndY : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ Y t ω-Y s ω) inferInstance) (G s) ν)
    (I : Finset T) :
    IdentDistrib (fun ω ↦ I.restrict (X · ω)) (fun ω ↦ I.restrict (Y · ω)) μ ν := by
  classical
  let t := I.orderEmbOfFinWithBot
  have ht : Monotone t := Finset.monotone_orderEmbOfFinWithBot I
  let DX := fun (i : Fin I.card) ω ↦ X (t i.succ) ω-X (t i.castSucc) ω
  let DY := fun (i : Fin I.card) ω ↦ Y (t i.succ) ω-Y (t i.castSucc) ω
  have hDX := increments_indep μ F X hX hIndX t ht
  have hDY := increments_indep ν G Y hY hIndY t ht
  have hD (i : Fin I.card) : IdentDistrib (DX i) (DY i) μ ν :=
    hInc _ _ (ht (Fin.castSucc_le_succ i))
  have hLX (i : Fin I.card) : HasLaw (DX i) (μ.map (DX i)) μ :=
    ⟨(hD i).aemeasurable_fst, rfl⟩
  have hLY (i : Fin I.card) : HasLaw (DY i) (μ.map (DX i)) ν :=
    ⟨(hD i).aemeasurable_snd, (hD i).map_eq.symm⟩
  have hpx := hDX.hasLaw_pi hLX
  have hpy := hDY.hasLaw_pi hLY
  have hJoint : IdentDistrib (fun ω i ↦ DX i ω) (fun ω i ↦ DY i ω) μ ν :=
    ⟨hpx.aemeasurable, hpy.aemeasurable, hpx.map_eq.trans hpy.map_eq.symm⟩
  have hMap := hJoint.comp (incrementsToRestrict ℝ I).measurable
  have hx : AEMeasurable (fun ω ↦ I.restrict (X · ω)) μ :=
    .of_eval fun i ↦ ((hX i).mono (F.le i) le_rfl).aemeasurable
  have hy : AEMeasurable (fun ω ↦ I.restrict (Y · ω)) ν :=
    .of_eval fun i ↦ ((hY i).mono (G.le i) le_rfl).aemeasurable
  exact (IdentDistrib.of_ae_eq hx
    (incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict ℝ hzeroX I)).trans
      (hMap.trans (IdentDistrib.of_ae_eq hy
        (incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict ℝ hzeroY I)).symm)

end Comparison
end SHEStochastic.FiniteIncrementLawComparison
