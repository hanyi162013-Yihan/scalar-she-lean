module

public import SHE.HilbertDyadicRemainder

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.HilbertDyadicConvergence
open Set Filter MeasureTheory Real PredictableL2
open scoped ENNReal BigOperators Topology
variable {X E:Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (μ:Measure X) (F:ℕ→X→E) (hF:∀j,Measurable (F j))
variable (hi:∀j,Integrable (fun x=>‖F j x‖^2) μ)
local notation "V"=>HilbertBandTails.vector μ F hF hi

/-- The actual finite sums converge in the original product L2 norm,
with the same literal sample/parameter representatives. -/
theorem actual_l2 (hs:Summable V):
    (∀L:ℕ,Integrable (fun x=>‖(∑j∈Finset.range L,F j x)-(∑'j,V j) x‖^2) μ) ∧
      Tendsto (fun L:ℕ=>∫x,‖(∑j∈Finset.range L,F j x)-(∑'j,V j) x‖^2 ∂μ) atTop (𝓝 0):=by
  have hr:∀ᵐx∂μ,∀j,V j x=F j x:=by
    rw [ae_all_iff]
    intro j
    exact ((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp
  have he (L:ℕ):
      (fun x=>((∑j∈Finset.range L,V j)-(∑'j,V j)) x)=ᵐ[μ]
        fun x=>(∑j∈Finset.range L,F j x)-(∑'j,V j) x:=by
    filter_upwards [Lp.coeFn_sub (∑j∈Finset.range L,V j) (∑'j,V j),
      Lp.coeFn_fun_finsetSum (Finset.range L) V,hr] with x hx hy hz
    exact hx.trans (congrArg (fun e:E=>e-(∑'j,V j) x)
      (hy.trans (Finset.sum_congr rfl (fun j _=>hz j))))
  have hmass (L:ℕ):
      Integrable (fun x=>‖(∑j∈Finset.range L,F j x)-(∑'j,V j) x‖^2) μ ∧
        (∫x,‖(∑j∈Finset.range L,F j x)-(∑'j,V j) x‖^2 ∂μ)=
          ‖(∑j∈Finset.range L,V j)-(∑'j,V j)‖^2:=by
    let W:Lp E 2 μ:=(∑j∈Finset.range L,V j)-(∑'j,V j)
    have hh:Integrable (fun x=>‖W x‖^2) μ:=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable W)).mp (Lp.memLp W)
    refine ⟨hh.congr ((he L).mono (fun x hx=>congrArg (fun e:E=>‖e‖^2) hx)),?_⟩
    rw [realLp_norm_sq]
    exact integral_congr_ae ((he L).mono (fun x hx=>congrArg (fun e:E=>‖e‖^2) hx.symm))
  refine ⟨fun L=>(hmass L).1,?_⟩
  have ht:=((hs.tendsto_sum_tsum_nat.sub_const (∑'j,V j)).norm.pow 2)
  have ht0:Tendsto (fun L:ℕ=>‖(∑j∈Finset.range L,V j)-(∑'j,V j)‖^2) atTop (𝓝 0):=by
    simpa only [sub_self,norm_zero,zero_pow (by decide:(2:ℕ)≠0)] using ht
  exact ht0.congr' (Eventually.of_forall (fun L=>(hmass L).2.symm))

end SHE.HilbertDyadicConvergence
