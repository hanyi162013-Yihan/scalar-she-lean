module

public import SHE.PredictableItoCells
public import SHE.TimeMeasureMass
public import SHE.LpEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.PredictableItoCells
open MeasureTheory Set PredictableL2 ApproximationCells
open scoped NNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ] {h : ℝ≥0}

theorem output_slice_ae (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (n : ℕ)
    (v : ℕ → Process (E := C) 𝓕 μ h)
    (hs : ∀ k,∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → v k p=0) :
    ∀ᵐ t ∂timeMeasure h,(fun ω => output I n v hs (t,ω)) =ᵐ[μ] I.integral (v (index n t)) := by
  have he := Measure.ae_ae_of_ae_prod (output_ae I n v hs)
  filter_upwards [timeMeasure_ae_mem h,he] with t ht hout
  filter_upwards [hout,integral_ae_version I _ (v (index n t)) (hs _)] with ω hω hZ
  rw [hω,sum_at n ht.1 ht.2]
  exact hZ.symm

/-- Exact physical time/probability Itô energy for two finite predictable
approximations, including unequal time grids. No continuity or joint
measurable choice of a parameterized stochastic integral is assumed. -/
theorem output_difference_energy (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (n m : ℕ) (v w : ℕ → Process (E := C) 𝓕 μ h)
    (hv : ∀ k,∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → v k p=0)
    (hw : ∀ k,∀ᵐ p ∂energyMeasure μ h,point m (k-1) < p.1 → w k p=0) :
    ENNReal.ofReal (‖output I n v hv-output I m w hw‖^2)=
      ∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal
        (‖v (index n t) (s,ω)-w (index m t) (s,ω)‖^2) ∂μ ∂timeMeasure h ∂timeMeasure h := by
  rw [process_difference_lintegral_energy]
  apply lintegral_congr_ae
  filter_upwards [output_slice_ae I n v hv,output_slice_ae I m w hw] with t ht hu
  calc
    (∫⁻ ω,ENNReal.ofReal (‖output I n v hv (t,ω)-output I m w hw (t,ω)‖^2) ∂μ) =
        ∫⁻ ω,ENNReal.ofReal (‖I.integral (v (index n t)) ω-I.integral (w (index m t)) ω‖^2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht,hu] with ω hω hω'
      rw [hω,hω']
    _ = ENNReal.ofReal (‖I.integral (v (index n t))-I.integral (w (index m t))‖^2) :=
      (LpEnergy.difference_energy _ _).symm
    _ = _ := I.difference_energy _ _

end SHE.PredictableItoCells
