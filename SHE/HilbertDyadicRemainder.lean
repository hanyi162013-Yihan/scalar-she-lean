module

public import SHE.HilbertBandTails
public import SHE.DyadicRemainderTail
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.HilbertDyadicRemainder
open Set Filter MeasureTheory Real PredictableL2
open scoped ENNReal BigOperators Topology
variable {X E:Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (μ:Measure X) (F:ℕ→X→E) (hF:∀j,Measurable (F j))
variable (hi:∀j,Integrable (fun x=>‖F j x‖^2) μ)
local notation "V"=>HilbertBandTails.vector μ F hF hi

theorem vector_bound (J:ℕ) {D:ℝ} (hD:0≤D)
    (hb:∀j,(∫x,‖F j x‖^2 ∂μ)≤D*((2:ℝ)^(J+j))^(-8:ℝ)) (j:ℕ):
    ‖V j‖≤sqrt D*((2:ℝ)^(J+j))^(-4:ℝ):=by
  have hh:=hb j
  rw [←HilbertBandTails.vector_norm_sq μ F hF hi j] at hh
  have he:((2:ℝ)^(J+j))^(-8:ℝ)=((((2:ℝ)^(J+j))^(-4:ℝ))^2):=by
    rw [←rpow_mul_natCast (show 0≤(2:ℝ)^(J+j) by positivity)]
    norm_num
  have hs:(sqrt D*((2:ℝ)^(J+j))^(-4:ℝ))^2=D*(((2:ℝ)^(J+j))^(-8:ℝ)):=by
    rw [mul_pow,sq_sqrt hD,he]
  have hn:0≤sqrt D*((2:ℝ)^(J+j))^(-4:ℝ):=by positivity
  nlinarith [norm_nonneg (V j)]

/-- Genuine Hilbert L2 summation of correlated dyadic fields on ANY
original parameter/sample measure. The field itself converges almost
everywhere, and the true tail energy keeps factor256/225 R^-8. -/
theorem summation (J:ℕ) {D:ℝ} (hD:0≤D)
    (hb:∀j,(∫x,‖F j x‖^2 ∂μ)≤D*((2:ℝ)^(J+j))^(-8:ℝ)):
    Summable V ∧ Summable (fun j=>‖V j‖) ∧
      (∀ᵐx∂μ,HasSum (fun j=>F j x) ((∑'j,V j) x)) ∧
      Integrable (fun x=>‖(∑'j,V j) x‖^2) μ ∧
      (∫x,‖(∑'j,V j) x‖^2 ∂μ)≤D*(256/225:ℝ)*((2:ℝ)^J)^(-8:ℝ):=by
  have hv:=vector_bound μ F hF hi J hD hb
  have hmajor:HasSum (fun j=>sqrt D*((2:ℝ)^(J+j))^(-4:ℝ))
      (sqrt D*((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ))):=(DyadicRemainderTail.hasSum_rms J).mul_left _
  have hnorm:Summable (fun j=>‖V j‖):=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hv hmajor.summable
  have hs:Summable V:=hnorm.of_norm
  have hae:=Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  have hrep:∀ᵐx∂μ,∀j,V j x=F j x:=by
    rw [ae_all_iff]
    intro j
    exact ((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp
  have hnormTail:‖∑'j,V j‖≤sqrt D*((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ)):=
    tsum_of_norm_bounded hmajor hv
  have hsq:‖∑'j,V j‖^2≤D*(256/225:ℝ)*((2:ℝ)^J)^(-8:ℝ):=by
    have hn:0≤sqrt D*((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ)):=by positivity
    have h:=pow_le_pow_left₀ (norm_nonneg (∑'j,V j)) hnormTail 2
    have he:(((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ)))^2=(256/225:ℝ)*((2:ℝ)^J)^(-8:ℝ):=by
      rw [←DyadicRemainderTail.tsum_rms J]
      exact DyadicRemainderTail.squared_tail J
    rw [mul_pow,sq_sqrt hD,he] at h
    simpa only [mul_assoc] using h
  refine ⟨hs,hnorm,?_,?_,?_⟩
  · filter_upwards [hae,hrep] with x hx hr
    simpa only [hr] using hx
  · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (∑'j,V j))).mp (Lp.memLp _)
  · rw [←realLp_norm_sq]
    exact hsq

include hF hi

/-- The same bound holds for every actual finite upper cutoff;
there is no factor depending on the number of bands. -/
theorem finite_energy (J L:ℕ) {D:ℝ} (hD:0≤D)
    (hb:∀j,(∫x,‖F j x‖^2 ∂μ)≤D*((2:ℝ)^(J+j))^(-8:ℝ)):
    Integrable (fun x=>‖∑j∈Finset.range L,F j x‖^2) μ ∧
      (∫x,‖∑j∈Finset.range L,F j x‖^2 ∂μ)≤D*(256/225:ℝ)*((2:ℝ)^J)^(-8:ℝ):=by
  let W:Lp E 2 μ:=∑j∈Finset.range L,V j
  have hrep:∀ᵐx∂μ,W x=∑j∈Finset.range L,F j x:=by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range L) V,
      ae_all_iff.mpr (fun j=>((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp)] with x hx hr
    exact hx.trans (Finset.sum_congr rfl (fun j _=>hr j))
  have hnorm:‖W‖≤sqrt D*((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ)):=by
    calc
      _≤∑j∈Finset.range L,‖V j‖:=norm_sum_le _ _
      _≤∑j∈Finset.range L,sqrt D*((2:ℝ)^(J+j))^(-4:ℝ):=
        Finset.sum_le_sum (fun j _=>vector_bound μ F hF hi J hD hb j)
      _≤_:=by
        rw [←Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (DyadicRemainderTail.finite_rms J L) (sqrt_nonneg _)
  have hiW:Integrable (fun x=>‖W x‖^2) μ:=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable W)).mp (Lp.memLp W)
  refine ⟨hiW.congr (hrep.mono (fun x hx=>congrArg (fun e:E=>‖e‖^2) hx)),?_⟩
  rw [←integral_congr_ae (hrep.mono (fun x hx=>congrArg (fun e:E=>‖e‖^2) hx)),←realLp_norm_sq]
  have hh:=pow_le_pow_left₀ (norm_nonneg W) hnorm 2
  have he:(((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ)))^2=(256/225:ℝ)*((2:ℝ)^J)^(-8:ℝ):=by
    rw [←DyadicRemainderTail.tsum_rms J]
    exact DyadicRemainderTail.squared_tail J
  rw [mul_pow,sq_sqrt hD,he] at hh
  simpa only [mul_assoc] using hh

end SHE.HilbertDyadicRemainder
