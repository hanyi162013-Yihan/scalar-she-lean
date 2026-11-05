module
public import SHE.ProcessEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.PredictableProcessLimit
open MeasureTheory PredictableL2 Filter Topology
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

theorem product_energy_eq(u v:Process (E:=E) 𝓕 μ H):
    (∫p,‖u p-v p‖^2 ∂energyMeasure μ H)=‖u-v‖^2:=by
  rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product 𝓕)]
  exact integral_congr_ae ((ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v)).symm.mono
    (fun p hp=>congrArg (fun x:E=>‖x‖^2) hp))

/-- Ordinary predictable-L2 convergence is exactly the unweighted
physical time/sample energy convergence required for law transfer. -/
theorem energy_tendsto(u:ℕ→Process (E:=E) 𝓕 μ H)(v:Process (E:=E) 𝓕 μ H)
    (hu:Tendsto u atTop (𝓝 v)):
    Tendsto (fun n=>∫p,‖u n p-v p‖^2 ∂energyMeasure μ H) atTop (𝓝 0):=by
  have ht:=((hu.sub (tendsto_const_nhds (x:=v))).norm).pow 2
  simpa only [sub_self,norm_zero,zero_pow (by decide:2≠0),product_energy_eq] using ht

/-- Actual versions inherit integrable squared differences and the
same physical product-energy limit. Version equalities are sufficient;
no pathwise convergence of stochastic Picard iterates is assumed. -/
theorem versions(u:ℕ→Process (E:=E) 𝓕 μ H)(v:Process (E:=E) 𝓕 μ H)
    (U:ℕ→ℝ≥0×Ω→E)(V:ℝ≥0×Ω→E)
    (hU:∀n,U n=ᵐ[energyMeasure μ H] u n)(hV:V=ᵐ[energyMeasure μ H] v)
    (hu:Tendsto u atTop (𝓝 v)):
    (∀n,Integrable (fun p=>‖U n p-V p‖^2) (energyMeasure μ H)) ∧
    Tendsto (fun n=>∫p,‖U n p-V p‖^2 ∂energyMeasure μ H) atTop (𝓝 0):=by
  have he(n:ℕ):(fun p=>‖U n p-V p‖^2)=ᵐ[energyMeasure μ H] (fun p=>‖u n p-v p‖^2):=by
    filter_upwards [hU n,hV] with p hp hq
    rw [hp,hq]
  refine ⟨fun n=>?_,?_⟩
  · have hmU:MemLp (u n) 2 (energyMeasure μ H):=
      memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp (u n))
    have hmV:MemLp v 2 (energyMeasure μ H):=
      memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp v)
    exact (hmU.sub hmV).norm.integrable_sq.congr (he n).symm
  · have ht:=energy_tendsto 𝓕 μ H u v hu
    have hi(n:ℕ):(∫p,‖U n p-V p‖^2 ∂energyMeasure μ H)=
        ∫p,‖u n p-v p‖^2 ∂energyMeasure μ H:=integral_congr_ae (he n)
    simpa only [hi] using ht

end SHE.PredictableProcessLimit
