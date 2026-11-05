module

public import SHEStochastic.NativeClockLocality
public import SHEStochastic.NativeIntegralUniqueness
public import SHEStochastic.NativeMartingaleVersion
public import SHEStochastic.NativeTerminalLevy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.NativeTimeDilatedFamily
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (c : ℝ≥0) (hc : 0 < c) (H : ℝ≥0)

local notation "FN" => filtration F (clock c hc)

def row (e : ι → C) (i : ι) : Process (E := C) F μ H :=
  Real.sqrt (c : ℝ) • RawCylindricalCoordinates.row F μ H e i

theorem row_ae (e : ι → C) (i : ι) : row F μ c H e i =ᵐ[energyMeasure μ H]
    (fun _ ↦ Real.sqrt (c : ℝ) • e i) := by
  filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.sqrt (c : ℝ))
    (RawCylindricalCoordinates.row F μ H e i)),
    RotatedCylindricalCoordinates.constant_ae F μ H (e i)] with p hp hr
  exact hp.trans (congrArg (fun v ↦ Real.sqrt (c : ℝ) • v) hr)

theorem input (e : ι → C) (i : ι) (t : ℝ≥0) :
    processIsometry F μ c hc H (StoppedItoInputs.stop FN μ (c*H) t
      (RawCylindricalCoordinates.row FN μ (c*H) e i)) =
        StoppedItoInputs.stop F μ H ((clock c hc).symm t) (row F μ c H e i) := by
  have hs := (energyMeasure_clock_preserving c hc H μ).quasiMeasurePreserving.ae
    (StoppedItoInputs.stop_ae FN μ (c*H) t (RawCylindricalCoordinates.row FN μ (c*H) e i))
  have hr := (energyMeasure_clock_preserving c hc H μ).quasiMeasurePreserving.ae
    (RotatedCylindricalCoordinates.constant_ae FN μ (c*H) (e i))
  have hs' := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp hs
  have hr' := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp hr
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [processIsometry_ae F μ c hc H
    (StoppedItoInputs.stop FN μ (c*H) t (RawCylindricalCoordinates.row FN μ (c*H) e i)),
    hs', hr', StoppedItoInputs.stop_ae F μ H ((clock c hc).symm t) (row F μ c H e i),
    row_ae F μ c H e i] with p hp hs hr ht hrow
  change RawCylindricalCoordinates.row FN μ (c*H) e i (clock c hc p.1, p.2) = e i at hr
  rw [hp, hs, ht]
  have hi : (clock c hc p.1, p.2) ∈ StoppedItoInputs.before (Ω := Ω) t ↔
      p ∈ StoppedItoInputs.before (Ω := Ω) ((clock c hc).symm t) := by
    change (clock c hc p.1 : ℝ) < (t : ℝ) ↔ (p.1 : ℝ) < ((clock c hc).symm t : ℝ≥0)
    have hh := (clock c hc).lt_iff_lt (x := p.1) (y := (clock c hc).symm t)
    exact_mod_cast (by simpa only [OrderIso.apply_symm_apply] using hh)
  by_cases h : p ∈ StoppedItoInputs.before (Ω := Ω) ((clock c hc).symm t)
  · rw [Set.indicator_of_mem (hi.mpr h), Set.indicator_of_mem h, hr, hrow]
  · rw [Set.indicator_of_notMem (fun h' ↦ h (hi.mp h')), Set.indicator_of_notMem h, smul_zero]

/-- Native cylindrical Brownian integration is invariant under the
literal deterministic Brownian clock, including the square-root
Jacobian and full-past independence. -/
theorem exists_family (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Q : FiniteScalarIto.Family FN μ (c*H) ι,
      ∀ u : Process (E := C) FN μ (c*H),
        (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral u =
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
            (processIsometry F μ c hc H u) := by
  choose M hMcont hMa hMp hMm hMr using fun i : ι ↦
    NativeMartingaleVersion.exists_version P e hnull (row F μ c H (e : ι → C) i)
  have hLaw (n : ℕ) (a : Fin n → ι) :
      FiniteBrownianLawOn F μ H (fun i ↦ M (a i))
        (fun i j ↦ (c : ℝ) * if a i = a j then 1 else 0) := by
    apply NativeTerminalLevy.finiteBrownianLaw P e
      (fun i ↦ row F μ c H (e : ι → C) (a i)) (fun i ↦ M (a i)) _
    · intro t _
      exact ae_all_iff.mpr (fun i ↦ hMr (a i) t)
    · filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦ row_ae F μ c H (e : ι → C) (a i))] with p hp i j
      rw [hp i, hp j, real_inner_smul_left, real_inner_smul_right]
      rw [show Real.sqrt (c : ℝ) * (Real.sqrt (c : ℝ) * inner ℝ (e (a i)) (e (a j))) =
        (c : ℝ) * inner ℝ (e (a i)) (e (a j)) by
          rw [← mul_assoc, ← pow_two, Real.sq_sqrt (show (0 : ℝ) ≤ c from c.2)]]
      rw [orthonormal_iff_ite.mp e.orthonormal]
  let Q : FiniteScalarIto.Family FN μ (c*H) ι :=
    { W := fun i t ↦ M i ((clock c hc).symm t)
      adapted := fun i t ↦ (hMa i ((clock c hc).symm t)).measurable
      continuous := fun i sample ↦ (hMcont i sample).comp (clock_symm_continuous c hc)
      law := by
        intro n a
        constructor
        · intro t ht
          have ht' (i : Fin n) : (clock c hc).symm (t i) ≤ H := by
            apply (clock c hc).le_iff_le.mp
            rw [OrderIso.apply_symm_apply]
            exact ht i
          have hl := (hLaw n a).1 (fun i ↦ (clock c hc).symm (t i)) ht'
          have hcov : (fun i j ↦ (min (t i) (t j) : ℝ≥0) * (if a i = a j then (1 : ℝ) else 0)) =
              (fun i j ↦ (min ((clock c hc).symm (t i)) ((clock c hc).symm (t j)) : ℝ≥0) *
                ((c : ℝ) * if a i = a j then 1 else 0)) := by
            funext i j
            change (min (t i) (t j) : ℝ≥0) * _ =
              (min (c⁻¹ * t i) (c⁻¹ * t j) : ℝ≥0) * ((c : ℝ) * _)
            have hmin : min (c⁻¹*t i) (c⁻¹*t j) = c⁻¹*min (t i) (t j) :=
              (map_inf (clock c hc).symm (t i) (t j)).symm
            rw [hmin, NNReal.coe_mul, NNReal.coe_inv]
            field_simp [show (c : ℝ) ≠ 0 from (show (0 : ℝ) < c from hc).ne']
          rw [hcov]
          exact hl
        · intro s t hst ht
          exact (hLaw n a).2 ((clock c hc).symm s) ((clock c hc).symm t)
            ((clock c hc).symm.monotone hst)
            (by apply (clock c hc).le_iff_le.mp; rw [OrderIso.apply_symm_apply]; exact ht) }
  let J := PredictableTimeDilation.integral F μ c hc H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e)
  have hcoord (i : ι) (t : ℝ≥0) (_ : t ≤ c*H) :
      RawCylindricalCoordinates.value FN μ (c*H) (e : ι → C) J i t =ᵐ[μ] Q.W i t := by
    change (fun sample ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (processIsometry F μ c hc H (StoppedItoInputs.stop FN μ (c*H) t
        (RawCylindricalCoordinates.row FN μ (c*H) (e : ι → C) i))) sample) =ᵐ[μ] _
    rw [input]
    exact (hMr i ((clock c hc).symm t)).symm
  exact ⟨Q, fun u ↦ (NativeIntegralUniqueness.integral Q e J
    (NativeClockLocality.locality F μ c hc H _ (FiniteCylindricalIto.pastLocality P e)) hcoord u).symm⟩

end SHEStochastic.NativeTimeDilatedFamily
