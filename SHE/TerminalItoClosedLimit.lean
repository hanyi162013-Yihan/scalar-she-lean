module

public import SHE.StandardTerminalIto
public import SHE.EnergyConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.TerminalItoClosedLimit
open Set Filter MeasureTheory PredictableL2
open scoped ENNReal Topology NNReal
variable {Ω C:Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- A strong cutoff limit of actual original-J integrals is still an
integral of that SAME J. The predictable input is constructed from the
closed isometric Hilbert range, without a new stochastic limit package. -/
theorem original_input (input:ℕ→Process (E:=C) 𝓕 μ H) (F:ℕ→Ω→ℝ) (G:Ω→ℝ)
    (hg:MemLp G 2 μ)
    (hrep:∀n,J.integral (input n)=ᵐ[μ] F n)
    (hlim:Tendsto (fun n=>∫ω,‖F n ω-G ω‖^2 ∂μ) atTop (𝓝 0)):
    ∃V:Process (E:=C) 𝓕 μ H,J.integral V=ᵐ[μ] G:=by
  let Z:Lp ℝ 2 μ:=hg.toLp G
  have ht:Tendsto (fun n=>J.integral (input n)) atTop (𝓝 Z):=by
    apply KernelEnergyCauchy.tendsto_of_energy_error _ Z
      (fun n=>ENNReal.ofReal (∫ω,‖F n ω-G ω‖^2 ∂μ))
      (by simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim)
    intro n
    apply le_of_eq
    congr 1
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (J.integral (input n)) Z,hrep n,hg.coeFn_toLp] with ω hs hf hgg
    rw [hs,Pi.sub_apply,hf,hgg]
  have hclosed:IsClosed (range J.integral):=J.integral.isometry.isClosedEmbedding.isClosed_range
  have hm:Z∈range J.integral:=hclosed.mem_of_tendsto ht (Eventually.of_forall (fun n=>⟨input n,rfl⟩))
  obtain ⟨V,hV⟩:=hm
  exact ⟨V,by rw [hV];exact hg.coeFn_toLp⟩

end SHE.TerminalItoClosedLimit
