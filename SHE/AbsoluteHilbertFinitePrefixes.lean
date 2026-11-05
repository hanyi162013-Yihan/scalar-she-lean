module
public import SHE.HilbertBandTails
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.AbsoluteHilbertFinitePrefixes
open MeasureTheory PredictableL2 Real
open scoped ENNReal BigOperators
variable {X E:Type*}[MeasurableSpace X][NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
/-- Absolute band RMS control bounds every literal finite prefix, before
any infinite sum is formed. -/
theorem rms(μ:Measure X)(F:ℕ→X→E)(hF:∀j,Measurable (F j))
    (hi:∀j,Integrable (fun z=>‖F j z‖^2) μ)
    (hs:Summable (fun j=>sqrt (∫z,‖F j z‖^2 ∂μ)))(C:ℝ)
    (hC:(∑'j,sqrt (∫z,‖F j z‖^2 ∂μ))≤C):
    ∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,F j z‖^2) μ ∧
      sqrt (∫z,‖∑j∈Finset.range L,F j z‖^2 ∂μ)≤C:=by
  let V:=HilbertBandTails.vector μ F hF hi
  have hn(j:ℕ):‖V j‖=sqrt (∫z,‖F j z‖^2 ∂μ):=by
    rw [←HilbertBandTails.vector_norm_sq μ F hF hi j,sqrt_sq (norm_nonneg _)]
  have hrep:∀ᵐz∂μ,∀j,V j z=F j z:=by
    rw [ae_all_iff]
    intro j
    exact ((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp
  intro L
  let W:Lp E 2 μ:=∑j∈Finset.range L,V j
  have he:(fun z=>W z)=ᵐ[μ] (fun z=>∑j∈Finset.range L,F j z):=by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range L) V,hrep] with z hz hr
    exact hz.trans (Finset.sum_congr rfl (fun j _=>hr j))
  have hiW:Integrable (fun z=>‖W z‖^2) μ:=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable W)).mp (Lp.memLp W)
  have hEq:(∫z,‖∑j∈Finset.range L,F j z‖^2 ∂μ)=‖W‖^2:=by
    rw [realLp_norm_sq]
    exact integral_congr_ae (he.symm.mono (fun _ hz=>congrArg (fun e:E=>‖e‖^2) hz))
  refine ⟨hiW.congr (he.mono (fun _ hz=>congrArg (fun e:E=>‖e‖^2) hz)),?_⟩
  rw [hEq,sqrt_sq (norm_nonneg _)]
  calc
    ‖W‖≤∑j∈Finset.range L,‖V j‖:=norm_sum_le _ _
    _=∑j∈Finset.range L,sqrt (∫z,‖F j z‖^2 ∂μ):=Finset.sum_congr rfl (fun j _=>hn j)
    _≤∑'j,sqrt (∫z,‖F j z‖^2 ∂μ):=hs.sum_le_tsum _ (fun _ _=>sqrt_nonneg _)
    _≤C:=hC
end SHE.AbsoluteHilbertFinitePrefixes
