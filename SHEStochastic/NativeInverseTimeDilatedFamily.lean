module

public import SHEStochastic.NativeTimeDilatedFamily
public import SHE.ClockedItoAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.NativeInverseTimeDilatedFamily
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (c : ℝ≥0) (hc : 0<c) (H : ℝ≥0)

local notation "FN" => filtration F (clock c hc)
local notation "v" => processEquivalence (C := C) F μ c hc H

omit [Countable ι] [DecidableEq ι] [CompleteSpace C] [SecondCountableTopology C] in
private theorem row_ae (e : ι → C) (i : ι) :
    (v).symm (RawCylindricalCoordinates.row F μ H e i) =ᵐ[energyMeasure μ (c*H)]
      (fun _ => Real.sqrt (c : ℝ)⁻¹ • e i) := by
  have hrev := ScaledLpPull.inverse_preserving (energyMeasure μ H) (energyMeasure μ (c*H))
    (c : ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc H μ)
  have ha : ∀ᵐ p ∂energyMeasure μ (c*H),
      RawCylindricalCoordinates.row F μ H e i ((clock c hc).symm p.1,p.2)=e i :=
    ScaledLpPull.ae_comp (energyMeasure μ (c*H)) (energyMeasure μ H) (c : ℝ)⁻¹
      (inv_pos.mpr (show (0 : ℝ)<c from hc)) (ambientEquiv c hc).symm hrev
        (RotatedCylindricalCoordinates.constant_ae F μ H (e i))
  filter_upwards [processEquivalence_symm_ae F μ c hc H (RawCylindricalCoordinates.row F μ H e i),ha]
    with p hp ha
  rw [hp,ha]

omit [CompleteSpace C] in
private theorem stop_equivalence (u : Process (E := C) F μ H) (t : ℝ≥0) :
    (v).symm (StoppedItoInputs.stop F μ H t u) =
      StoppedItoInputs.stop FN μ (c*H) (clock c hc t) ((v).symm u) := by
  apply (v).injective
  rw [LinearIsometryEquiv.apply_symm_apply,processEquivalence_apply,ClockedItoAlgebra.map_stop F μ c hc H]
  have ht : (clock c hc t : ℝ≥0) / (c : ℝ) = (t : ℝ) := by
    change ((c : ℝ)*(t : ℝ))/(c : ℝ) = _
    rw [mul_comm,mul_div_cancel_right₀ _ (show (c : ℝ)≠0 from (show (0 : ℝ)<c from hc).ne')]
  rw [ht,←processEquivalence_apply,LinearIsometryEquiv.apply_symm_apply]

/-- Recover a Brownian family on the original slower clock. Every
terminal stochastic integral uses the exact inverse input isometry. -/
theorem exists_family (Q : FiniteScalarIto.Family FN μ (c*H) ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets FN μ) :
    ∃ P : FiniteScalarIto.Family F μ H ι,
      ∀ u : Process (E := C) FN μ (c*H),
        (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral u =
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
            (processIsometry F μ c hc H u) := by
  let b (i : ι) := (v).symm (RawCylindricalCoordinates.row F μ H (e : ι → C) i)
  choose M hMcont hMa hMp hMm hMr using fun i : ι =>
    NativeMartingaleVersion.exists_version Q e hnull (b i)
  have hLaw (n : ℕ) (a : Fin n → ι) :
      FiniteBrownianLawOn FN μ (c*H) (fun i => M (a i))
        (fun i j => (c : ℝ)⁻¹ * if a i = a j then 1 else 0) := by
    apply NativeTerminalLevy.finiteBrownianLaw Q e
      (fun i => b (a i)) (fun i => M (a i)) _
    · intro t _
      exact ae_all_iff.mpr (fun i => hMr (a i) t)
    · filter_upwards [ae_all_iff.mpr (fun i : Fin n => row_ae F μ c hc H (e : ι → C) (a i))]
        with p hp i j
      rw [hp i,hp j,real_inner_smul_left,real_inner_smul_right]
      rw [show Real.sqrt (c : ℝ)⁻¹ * (Real.sqrt (c : ℝ)⁻¹ * inner ℝ (e (a i)) (e (a j))) =
        (c : ℝ)⁻¹ * inner ℝ (e (a i)) (e (a j)) by
          rw [←mul_assoc,←pow_two,Real.sq_sqrt (inv_nonneg.mpr (show (0 : ℝ)≤c from c.2))]]
      rw [orthonormal_iff_ite.mp e.orthonormal]
  let P : FiniteScalarIto.Family F μ H ι :=
    { W := fun i t => M i (clock c hc t)
      adapted := fun i t => by
        have ha := (hMa i (clock c hc t)).measurable
        rwa [filtration_clock] at ha
      continuous := fun i ω => (hMcont i ω).comp (clock_continuous c hc)
      law := by
        intro n a
        constructor
        · intro t ht
          have hl := (hLaw n a).1 (fun i => clock c hc (t i)) (fun i => (clock c hc).monotone (ht i))
          have hcov (i j : Fin n) :
              (min (clock c hc (t i)) (clock c hc (t j)) : ℝ≥0) *
                ((c : ℝ)⁻¹ * if a i = a j then (1 : ℝ) else 0) =
              (min (t i) (t j) : ℝ≥0) * (if a i = a j then (1 : ℝ) else 0) := by
            rw [←map_inf]
            change ((c : ℝ) * (min (t i) (t j) : ℝ≥0)) * _ = _
            field_simp [(show (0 : ℝ)<c from hc).ne']
          simpa only [hcov] using hl
        · intro s t hst ht
          have hl := (hLaw n a).2 (clock c hc s) (clock c hc t)
            ((clock c hc).monotone hst) ((clock c hc).monotone ht)
          rwa [filtration_clock] at hl }
  let J := inverseIntegral F μ c hc H (FiniteCylindricalIto.terminalIto Q.toCoordinates e)
  have hcoord (i : ι) (t : ℝ≥0) (_ : t≤H) :
      RawCylindricalCoordinates.value F μ H (e : ι → C) J i t =ᵐ[μ] P.W i t := by
    change (fun ω => (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral
      ((v).symm (StoppedItoInputs.stop F μ H t (RawCylindricalCoordinates.row F μ H (e : ι → C) i))) ω)
      =ᵐ[μ] M i (clock c hc t)
    rw [stop_equivalence F μ c hc H]
    exact (hMr i (clock c hc t)).symm
  refine ⟨P,fun u => ?_⟩
  have hu := NativeIntegralUniqueness.integral P e J
    (InverseClockLocality.locality F μ c hc H _ (FiniteCylindricalIto.pastLocality Q e))
    hcoord (processIsometry F μ c hc H u)
  change (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral
    ((v).symm (processIsometry F μ c hc H u)) = _ at hu
  rw [←processEquivalence_apply,LinearIsometryEquiv.symm_apply_apply] at hu
  exact hu

end SHEStochastic.NativeInverseTimeDilatedFamily
