module

public import SHE.ApproximationCells
public import SHE.StandardTerminalIto

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.PredictableItoCells
open MeasureTheory Set PredictableL2 ApproximationCells
open scoped NNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ] {h : ℝ≥0}

def version (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (l : ℝ≥0) (v : Process (E := C) 𝓕 μ h)
    (hs : ∀ᵐ p ∂energyMeasure μ h,l < p.1 → v p=0) : Ω → E :=
  Classical.choose (I.adapted l v hs)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [SFinite μ] in
theorem version_stronglyMeasurable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (l : ℝ≥0) (v : Process (E := C) 𝓕 μ h)
    (hs : ∀ᵐ p ∂energyMeasure μ h,l < p.1 → v p=0) :
    StronglyMeasurable[𝓕 l] (version I l v hs) :=
  (Classical.choose_spec (I.adapted l v hs)).1

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [SFinite μ] in
theorem integral_ae_version (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (l : ℝ≥0) (v : Process (E := C) 𝓕 μ h)
    (hs : ∀ᵐ p ∂energyMeasure μ h,l < p.1 → v p=0) :
    I.integral v =ᵐ[μ] version I l v hs :=
  (Classical.choose_spec (I.adapted l v hs)).2

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [SFinite μ] in
theorem version_memLp (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (l : ℝ≥0) (v : Process (E := C) 𝓕 μ h)
    (hs : ∀ᵐ p ∂energyMeasure μ h,l < p.1 → v p=0) :
    MemLp (version I l v hs) 2 μ :=
  MemLp.ae_eq (integral_ae_version I l v hs) (Lp.memLp _)

def output (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (n : ℕ)
    (v : ℕ → Process (E := C) 𝓕 μ h)
    (hs : ∀ k,∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → v k p=0) :
    Process (E := E) 𝓕 μ h :=
  ∑ k ∈ Finset.Icc 1 (index n h),PredictableSteps.process 𝓕 μ h (point n (k-1)) (point n k)
    (version I _ (v k) (hs k)) (version_stronglyMeasurable I _ (v k) (hs k))
    (version_memLp I _ (v k) (hs k))

theorem output_ae (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (n : ℕ)
    (v : ℕ → Process (E := C) 𝓕 μ h)
    (hs : ∀ k,∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → v k p=0) :
    output I n v hs =ᵐ[energyMeasure μ h]
      ApproximationCells.sum n h (fun k => version I _ (v k) (hs k)) := by
  classical
  have he := ae_eq_of_ae_eq_trim (Lp.coeFn_finsetSum (Finset.Icc 1 (index n h))
    (fun k => PredictableSteps.process 𝓕 μ h (point n (k-1)) (point n k)
      (version I _ (v k) (hs k)) (version_stronglyMeasurable I _ (v k) (hs k))
      (version_memLp I _ (v k) (hs k))))
  have hv := ae_all_iff.mpr (fun k : ℕ => PredictableSteps.process_ae 𝓕 μ h
    (point n (k-1)) (point n k) (version I _ (v k) (hs k))
    (version_stronglyMeasurable I _ (v k) (hs k)) (version_memLp I _ (v k) (hs k)))
  filter_upwards [he,hv] with p hp hZ
  unfold output
  rw [hp]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact hZ k

end SHE.PredictableItoCells
