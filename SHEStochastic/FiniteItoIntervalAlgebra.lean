module

public import SHEStochastic.FiniteItoStoppedVersions
public import SHEStochastic.FiniteItoTestExtension

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FiniteItoIntervalAlgebra
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.GaussianItoTest SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

/-- Time clipping cancels every pre-interval spatial jet against the
same jet frozen at the left endpoint. Applies to gradients and Hessians
without separately redoing the interval case split. -/
theorem jet_difference {Ω A : Type*} [AddGroup A] {n : ℕ}
    (a b : ℝ≥0) (hab : a ≤ b) (Ψ : ℝ → State n → A)
    (Y : ℝ≥0 × Ω → State n) (p : ℝ≥0 × Ω) :
    (if p.1 < b then Ψ (ClampedAbsoluteContinuity.clamp a b p.1) (Y (min p.1 b, p.2)) else 0) -
      (if p.1 < a then Ψ a (Y (min p.1 a, p.2)) else 0) =
      (if p.1 < b then Ψ p.1 (Y p) else 0) - (if p.1 < a then Ψ p.1 (Y p) else 0) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  by_cases hpa : p.1 < a
  · have hpb : p.1 < b := hpa.trans_le hab
    have hpr : (p.1 : ℝ) ≤ a := by exact_mod_cast hpa.le
    simp only [hpa, hpb, ite_true, min_eq_left hpa.le, min_eq_left hpb.le,
      ClampedAbsoluteContinuity.of_le_left habR hpr, sub_self]
  · by_cases hpb : p.1 < b
    · have hpr : (p.1 : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) :=
        ⟨by exact_mod_cast le_of_not_gt hpa, by exact_mod_cast hpb.le⟩
      simp only [hpa, hpb, ite_false, ite_true, min_eq_left hpb.le,
        ClampedAbsoluteContinuity.of_mem hpr, sub_zero]
    · simp only [hpa, hpb, ite_false, sub_self]

section Inputs
variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

def stoppedGradient (t : ℝ≥0) (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun r ↦ Y (r, ω))) (G : ℝ → State n → ℝ)
    (hG : FiniteItoNoise.AdmissibleGradient G) : Process (E := C) F μ H :=
  FiniteItoNoise.gradientProcess F μ H (FiniteItoStoppedVersions.stopped Y t)
    (FiniteItoStoppedVersions.predictable Y hY hc t) (fun i ↦ stop F μ H t (R i)) G hG

/-- A stopped gradient input has its literal predictable-row formula on
all nonzero time cells. No stochastic transport is involved here. -/
theorem stoppedGradient_ae (t : ℝ≥0) (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun r ↦ Y (r, ω))) (G : ℝ → State n → ℝ)
    (hG : FiniteItoNoise.AdmissibleGradient G) :
    stoppedGradient t R Y hY hc G hG =ᵐ[energyMeasure μ H] (fun p ↦ if p.1 < t then
      ∑ i : Fin n, fderiv ℝ (G p.1) (Y (min p.1 t, p.2))
        (EuclideanSpace.basisFun (Fin n) ℝ i) • R i p else 0) := by
  have hg := FiniteItoNoise.gradientProcess_ae F μ H (FiniteItoStoppedVersions.stopped Y t)
    (FiniteItoStoppedVersions.predictable Y hY hc t) (fun i ↦ stop F μ H t (R i)) G hG
  filter_upwards [hg, ae_all_iff.mpr (fun i : Fin n ↦ stop_ae F μ H t (R i))] with p hg hp
  change stoppedGradient t R Y hY hc G hG p = _ at hg
  rw [hg]
  dsimp [FiniteItoNoise.gradientRow, FiniteItoNoise.gradientCoefficient, FiniteItoStoppedVersions.stopped]
  by_cases ht : p.1 < t
  · rw [if_pos ht]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hp i, Set.indicator_of_mem (show p ∈ before (Ω := Ω) t from by exact_mod_cast ht)]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hp i, Set.indicator_of_notMem (show p ∉ before (Ω := Ω) t from by exact_mod_cast ht), smul_zero]

/-- Subtracting the frozen-left stopped gradient from the clipped-time
stopped gradient gives EXACTLY the original gradient restricted to [a,b]. -/
theorem gradient_difference (a b : ℝ≥0) (hab : a ≤ b)
    (R : Fin n → Process (E := C) F μ H) (Y : ℝ≥0 × Ω → State n)
    (hY : StronglyMeasurable[F.predictable] Y) (hc : ∀ ω, Continuous (fun r ↦ Y (r, ω)))
    (G dG : ℝ → State n → ℝ) (hG : RegularTest (a : ℝ) (b : ℝ) G dG) :
    stoppedGradient b R Y hY hc (FiniteItoTestExtension.value a b G)
        (FiniteItoNoise.regular_admissible (FiniteItoTestExtension.regular (by exact_mod_cast hab) hG H)) -
      stoppedGradient a R Y hY hc (FiniteItoTestExtension.constant G a)
        (FiniteItoNoise.regular_admissible (FiniteItoTestExtension.constant_regular hG a H)) =
      stop F μ H b (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)) -
        stop F μ H a (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)) := by
  let U := FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)
  let hB := FiniteItoNoise.regular_admissible (FiniteItoTestExtension.regular (by exact_mod_cast hab) hG H)
  let hA := FiniteItoNoise.regular_admissible (FiniteItoTestExtension.constant_regular hG a H)
  let UB := stoppedGradient b R Y hY hc (FiniteItoTestExtension.value a b G) hB
  let UA := stoppedGradient a R Y hY hc (FiniteItoTestExtension.constant G a) hA
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub UB UA),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub (stop F μ H b U) (stop F μ H a U)),
    stoppedGradient_ae b R Y hY hc (FiniteItoTestExtension.value a b G) hB,
    stoppedGradient_ae a R Y hY hc (FiniteItoTestExtension.constant G a) hA,
    stop_ae F μ H b U, stop_ae F μ H a U,
    FiniteItoNoise.gradientProcess_ae F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)]
      with p hl hr hBω hAω hsB hsA hU
  change U p = FiniteItoNoise.gradientRow F μ H Y R G p at hU
  rw [hl, hr]
  change UB p - UA p = stop F μ H b U p - stop F μ H a U p
  rw [hBω, hAω, hsB, hsA]
  have hj := jet_difference a b hab (fun r z ↦ ∑ i : Fin n,
    fderiv ℝ (G r) z (EuclideanSpace.basisFun (Fin n) ℝ i) • R i p) Y p
  change _ = _ at hj
  dsimp only [FiniteItoTestExtension.value, FiniteItoTestExtension.constant]
  convert hj using 1 <;>
    (by_cases hpb : p.1 < b <;> by_cases hpa : p.1 < a <;>
      simp only [Set.indicator_apply, before, Set.mem_setOf_eq, NNReal.coe_lt_coe,
        hpb, hpa, ite_true, ite_false, hU, FiniteItoNoise.gradientRow, FiniteItoNoise.gradientCoefficient, sub_self, sub_zero])

end Inputs
end SHEStochastic.FiniteItoIntervalAlgebra
