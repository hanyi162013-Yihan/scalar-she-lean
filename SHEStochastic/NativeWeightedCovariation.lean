module

public import SHEStochastic.NativeWeightedQuadraticVariation
public import SHEStochastic.ConvergenceInMeasureAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.NativeWeightedCovariation
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def sum (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, w (unifPart H n i) ω *
    (J.integral (stop F μ H (unifPart H n (i + 1)) u) ω - J.integral (stop F μ H (unifPart H n i) u) ω) *
    (J.integral (stop F μ H (unifPart H n (i + 1)) v) ω - J.integral (stop F μ H (unifPart H n i) v) ω)

def energy (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ r, w r ω * inner ℝ (u (r, ω)) (v (r, ω)) ∂timeMeasure H

/-- Polarization retains the actual stopped integrals on both sides. -/
theorem sum_polarization (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    sum J u v w n =ᵐ[μ] (fun ω ↦
      (NativeWeightedQuadraticVariation.sum J u w n ω + NativeWeightedQuadraticVariation.sum J v w n ω -
        NativeWeightedQuadraticVariation.sum J (u - v) w n ω) / 2) := by
  have ht (t : ℝ≥0) : (J.integral (stop F μ H t (u - v)) : Ω → ℝ) =ᵐ[μ]
      (fun ω ↦ J.integral (stop F μ H t u) ω - J.integral (stop F μ H t v) ω) := by
    rw [StoppedDampingClock.stop_sub, map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦ ht (unifPart H n i)),
    ae_all_iff.mpr (fun i : Fin n ↦ ht (unifPart H n (i + 1)))] with ω hl hr
  calc
    _ = ∑ i : Fin n,
        (w (unifPart H n i) ω *
          (J.integral (stop F μ H (unifPart H n (i + 1)) u) ω - J.integral (stop F μ H (unifPart H n i) u) ω) ^ 2 +
        w (unifPart H n i) ω *
          (J.integral (stop F μ H (unifPart H n (i + 1)) v) ω - J.integral (stop F μ H (unifPart H n i) v) ω) ^ 2 -
        w (unifPart H n i) ω *
          (J.integral (stop F μ H (unifPart H n (i + 1)) (u - v)) ω -
            J.integral (stop F μ H (unifPart H n i) (u - v)) ω) ^ 2) / 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hl i, hr i]
      ring
    _ = _ := by
      simp only [NativeWeightedQuadraticVariation.sum]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Polarization of the original weighted Hilbert row energy. -/
theorem energy_polarization (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (B : ℝ) (hwb : ∀ t ω, |w t ω| ≤ B) :
    energy u v w =ᵐ[μ] (fun ω ↦ (NativeWeightedEnergy.integral u w ω +
      NativeWeightedEnergy.integral v w ω - NativeWeightedEnergy.integral (u - v) w ω) / 2) := by
  have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2) := by
    simpa only [Function.uncurry_def] using hp.mono (predictable_le_product F)
  have hi (r : Process (E := C) F μ H) :
      Integrable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2 * ‖r p‖ ^ 2) (energyMeasure μ H) :=
    ((memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp r)).norm.integrable_sq).bdd_mul
      hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ by
        simpa only [Real.norm_eq_abs] using hwb p.1 p.2)
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v))
  filter_upwards [(hi u).prod_left_ae, (hi v).prod_left_ae, (hi (u - v)).prod_left_ae,
    Measure.ae_ae_of_ae_prod he] with ω hu hv hd heω
  change (∫ r, w r ω * inner ℝ (u (r, ω)) (v (r, ω)) ∂timeMeasure H) =
    ((∫ r, w r ω * ‖u (r, ω)‖ ^ 2 ∂timeMeasure H) +
      (∫ r, w r ω * ‖v (r, ω)‖ ^ 2 ∂timeMeasure H) -
      (∫ r, w r ω * ‖(u - v) (r, ω)‖ ^ 2 ∂timeMeasure H)) / 2
  have hlin : (∫ r, w r ω * ‖u (r, ω)‖ ^ 2 + w r ω * ‖v (r, ω)‖ ^ 2 -
      w r ω * ‖(u - v) (r, ω)‖ ^ 2 ∂timeMeasure H) =
      (∫ r, w r ω * ‖u (r, ω)‖ ^ 2 + w r ω * ‖v (r, ω)‖ ^ 2 ∂timeMeasure H) -
        ∫ r, w r ω * ‖(u - v) (r, ω)‖ ^ 2 ∂timeMeasure H := by
    simpa only [Pi.add_apply, Pi.sub_apply] using integral_sub (hu.add hv) hd
  rw [integral_add hu hv] at hlin
  have hdiv := congrArg (fun x : ℝ ↦ x / 2) hlin
  have hlin' : (∫ r, (w r ω * ‖u (r, ω)‖ ^ 2 + w r ω * ‖v (r, ω)‖ ^ 2 -
      w r ω * ‖(u - v) (r, ω)‖ ^ 2) / 2 ∂timeMeasure H) =
      ((∫ r, w r ω * ‖u (r, ω)‖ ^ 2 ∂timeMeasure H) +
        (∫ r, w r ω * ‖v (r, ω)‖ ^ 2 ∂timeMeasure H) -
        (∫ r, w r ω * ‖(u - v) (r, ω)‖ ^ 2 ∂timeMeasure H)) / 2 := by
    rw [integral_div]
    simpa only [Pi.add_apply, Pi.sub_apply] using hdiv
  rw [← hlin']
  apply integral_congr_ae
  filter_upwards [heω] with r hr
  change w r ω * inner ℝ (u (r, ω)) (v (r, ω)) = _
  change (u - v) (r, ω) = u (r, ω) - v (r, ω) at hr
  rw [hr, norm_sub_sq_real]
  ring

/-- All mixed quadratic variations follow by polarization, with no
finite-dimensional covariance law or additional stochastic theorem. -/
theorem tendstoInMeasure (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    TendstoInMeasure μ (sum (FiniteCylindricalIto.terminalIto P.toCoordinates e) u v w)
      Filter.atTop (energy u v w) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hq (r : Process (E := C) F μ H) :=
    NativeWeightedQuadraticVariation.tendstoInMeasure P e r w hw hp hc B hB hwb
  have hm (r : Process (E := C) F μ H) (n : ℕ) :
      AEStronglyMeasurable (NativeWeightedQuadraticVariation.sum J r w n) μ :=
    (NativeWeightedQuadraticVariation.stronglyMeasurable_sum J r w hw n).aestronglyMeasurable
  have hadd := ConvergenceInMeasureAlgebra.continuous_map₂ (hq u) (hq v) (hm u) (hm v)
    (fun p ↦ p.1 + p.2) (continuous_fst.add continuous_snd)
  have hpol := ConvergenceInMeasureAlgebra.continuous_map₂ hadd (hq (u - v))
    (fun n ↦ (hm u n).add (hm v n)) (hm (u - v))
    (fun p ↦ (p.1 - p.2) / 2) ((continuous_fst.sub continuous_snd).div_const 2)
  exact TendstoInMeasure.congr (fun n ↦ (sum_polarization J u v w n).symm)
    (energy_polarization u v w hp B hwb).symm hpol

end SHEStochastic.NativeWeightedCovariation
