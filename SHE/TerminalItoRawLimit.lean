module

public import SHE.TerminalItoClosedLimit
public import SHE.ProductLpIdentification

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.TerminalItoRawLimit
open Set Filter MeasureTheory PredictableL2
open scoped ENNReal Topology NNReal
variable {Ω C:Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Strong terminal convergence and pointwise convergence of the
explicit inputs identify the limiting original input. No arbitrary
closed-range witness can replace the literal limiting kernel. -/
theorem original_input (input:ℕ→Process (E:=C) 𝓕 μ H) (F:ℕ→Ω→ℝ) (G:Ω→ℝ)
    (hg:MemLp G 2 μ) (hrep:∀n,J.integral (input n)=ᵐ[μ] F n)
    (hlim:Tendsto (fun n=>∫ω,‖F n ω-G ω‖^2 ∂μ) atTop (𝓝 0))
    (raw:ℕ→(ℝ≥0×Ω)→C)(raw₀:(ℝ≥0×Ω)→C)
    (hraw:∀n,input n=ᵐ[energyMeasure μ H] raw n)
    (hrawlim:∀ᵐz∂energyMeasure μ H,Tendsto (fun n=>raw n z) atTop (𝓝 (raw₀ z))):
    ∃V:Process (E:=C) 𝓕 μ H,
      V=ᵐ[energyMeasure μ H] raw₀ ∧ J.integral V=ᵐ[μ] G:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨V,hV⟩:=TerminalItoClosedLimit.original_input 𝓕 μ H J input F G hg hrep hlim
  have ht:Tendsto input atTop (𝓝 V):=by
    apply KernelEnergyCauchy.tendsto_of_energy_error input V
      (fun n=>ENNReal.ofReal (∫ω,‖F n ω-G ω‖^2 ∂μ))
      (by simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim)
    intro n
    apply le_of_eq
    congr 1
    rw [←J.integral.norm_map (input n-V),map_sub,realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (J.integral (input n)) (J.integral V),hrep n,hV] with ω hs hn hv
    rw [hs,Pi.sub_apply,hn,hv]
  let A:=PredictableL2.ambientIsometry (E:=C) (energyMeasure μ H) (predictable_le_product 𝓕)
  have hta:Tendsto (fun n=>A (input n)) atTop (𝓝 (A V)):=A.continuous.continuousAt.tendsto.comp ht
  have hpoint:∀ᵐz∂energyMeasure μ H,Tendsto (fun n=>A (input n) z) atTop (𝓝 (raw₀ z)):=by
    have hall:∀ᵐz∂energyMeasure μ H,∀n,A (input n) z=raw n z:=
      ae_all_iff.mpr (fun n=>(PredictableL2.ambient_ae (energyMeasure μ H)
        (predictable_le_product 𝓕) (input n)).trans (hraw n))
    filter_upwards [hall,hrawlim] with z hz hl
    simpa only [hz] using hl
  have heq:A V=ᵐ[energyMeasure μ H] raw₀:=tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_Lp hta)
    (tendstoInMeasure_of_tendsto_ae (fun n=>(Lp.stronglyMeasurable (A (input n))).aestronglyMeasurable) hpoint)
  exact ⟨V,(PredictableL2.ambient_ae (energyMeasure μ H) (predictable_le_product 𝓕) V).symm.trans heq,hV⟩

end SHE.TerminalItoRawLimit
