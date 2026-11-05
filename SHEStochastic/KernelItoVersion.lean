module

public import SHE.KernelItoLimit
public import SHE.ProductLpIdentification

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.KernelItoVersion
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.KernelItoLimit
open scoped NNReal ENNReal Topology
variable {Ω C E A : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsFiniteMeasure μ] {H : ℝ≥0}

/-- A joint measurable family of fixed-time integral limits represents
the constructed predictable convolution. This reuses the existing
product-L2 identification, independently of any continuity theorem. -/
theorem convolution_ae_version (K : Model A C F μ H)
    (I : StandardTerminalIto (C := C) (E := E) F μ H) (a : A)
    (V : ∀ t : ℝ≥0, t ≤ H → Lp E 2 μ)
    (hV : ∀ (t : ℝ≥0) (ht : 0 < t) (htH : t ≤ H),
      Tendsto (fun n => I.integral (K.input a n (ApproximationCells.index n t))) atTop (𝓝 (V t htH)))
    (Y : ℝ≥0 × Ω → E) (hY : StronglyMeasurable Y)
    (hversion : ∀ (t : ℝ≥0) (htH : t ≤ H), (fun ω => Y (t,ω)) =ᵐ[μ] V t htH) :
    convolution K I a =ᵐ[energyMeasure μ H] Y := by
  let A := ambientIsometry (E := E) (energyMeasure μ H) (predictable_le_product F)
  let v : ℕ → Lp E 2 (energyMeasure μ H) := fun n => A (output K I a n)
  let Z : Lp E 2 (energyMeasure μ H) := A (convolution K I a)
  have hv : Tendsto v atTop (𝓝 Z) :=
    A.continuous.continuousAt.tendsto.comp (approximation_tendsto K I a)
  have hslices : ∀ᵐ t ∂timeMeasure H, ∀ n,
      (fun ω => v n (t,ω)) =ᵐ[μ] I.integral (K.input a n (ApproximationCells.index n t)) := by
    apply ae_all_iff.mpr
    intro n
    have ha : ∀ᵐ t ∂timeMeasure H, (fun ω => v n (t,ω)) =ᵐ[μ]
        (fun ω => output K I a n (t,ω)) :=
      Measure.ae_ae_of_ae_prod (ambient_ae (energyMeasure μ H) (predictable_le_product F) (output K I a n))
    have hb := PredictableItoCells.output_slice_ae I n (K.input a n) (K.input_stopped a n)
    filter_upwards [ha,hb] with t ht ht'
    exact ht.trans ht'
  have hs : ∀ᵐ t ∂timeMeasure H,
      TendstoInMeasure μ (fun n ω => v n (t,ω)) atTop (fun ω => Y (t,ω)) := by
    filter_upwards [timeMeasure_ae_mem H,hslices] with t ht hs
    exact TendstoInMeasure.congr_right (hversion t ht.2).symm
      (TendstoInMeasure.congr_left (fun n => (hs n).symm)
        (tendstoInMeasure_of_tendsto_Lp (hV t ht.1 ht.2)))
  have he : Z =ᵐ[energyMeasure μ H] Y :=
    ProductLpIdentification.ae_eq_of_slice_limits (timeMeasure H) μ v Z hv Y hY hs
  exact (ambient_ae (energyMeasure μ H) (predictable_le_product F) (convolution K I a)).symm.trans he

end SHEStochastic.KernelItoVersion
