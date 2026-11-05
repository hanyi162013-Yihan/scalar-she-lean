module
public import SHE.HilbertENNRateTails
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.HilbertENNFinitePrefixes
open MeasureTheory PredictableL2 Real
open scoped ENNReal BigOperators
variable {X E ι:Type*}[MeasurableSpace X][NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E][Fintype ι]

/-- Actual finite band prefixes retain each separate energy mechanism.
The bound is proved for every literal partial field before taking any
infinite-series norm. -/
theorem rms(μ:Measure X)(F:ℕ→X→E)(hF:∀j,Measurable (F j))
    (hi:∀j,Integrable (fun x=>‖F j x‖^2) μ)(J0:ℕ)
    (q:ι→ℝ)(K:ι→ℝ≥0∞)(hq:∀i,0<q i)(hK:∀i,K i≠∞)
    (hb:∀j,(∫⁻x,ENNReal.ofReal (‖F j x‖^2) ∂μ)≤
      ∑i,K i*ENNReal.ofReal (((2:ℝ)^(j+J0))^(-q i))):
    ∀L:ℕ,Integrable (fun x=>‖∑j∈Finset.range L,F j x‖^2) μ ∧
      Real.sqrt (∫x,‖∑j∈Finset.range L,F j x‖^2 ∂μ)≤
        ∑i,Real.sqrt (K i).toReal*StateBands.geometricConstant (q i/2)*
          ((2:ℝ)^J0)^(-(q i/2)):=by
  let V:=HilbertBandTails.vector μ F hF hi
  have hr(j:ℕ):(∫z,‖F j z‖^2 ∂μ)≤
      ∑i,(K i).toReal*((2:ℝ)^(j+J0))^(-q i):=by
    have he:=ofReal_integral_eq_lintegral_ofReal (hi j) (ae_of_all _ (fun _=>sq_nonneg _))
    have ht:∀i:ι,K i*ENNReal.ofReal (((2:ℝ)^(j+J0))^(-q i))≠∞:=
      fun i=>ENNReal.mul_ne_top (hK i) ENNReal.ofReal_ne_top
    have hh:=ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _=>ht i)) (hb j)
    rw [←he,ENNReal.toReal_ofReal (integral_nonneg (fun _=>sq_nonneg _)),
      ENNReal.toReal_sum (fun i _=>ht i)] at hh
    have hp(i:ι):(ENNReal.ofReal (((2:ℝ)^(j+J0))^(-q i))).toReal=((2:ℝ)^(j+J0))^(-q i):=
      ENNReal.toReal_ofReal (Real.rpow_nonneg (show 0≤(2:ℝ)^(j+J0) by positivity) _)
    simpa only [ENNReal.toReal_mul,hp] using hh
  have hv(j:ℕ):‖V j‖≤∑i,Real.sqrt (K i).toReal*((2:ℝ)^(j+J0))^(-(q i/2)):=by
    have hh:=hr j
    rw [←HilbertBandTails.vector_norm_sq μ F hF hi j] at hh
    have he:(∑i,(K i).toReal*((2:ℝ)^(j+J0))^(-q i))=
        ∑i,(Real.sqrt (K i).toReal*((2:ℝ)^(j+J0))^(-(q i/2)))^2:=by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg,←rpow_mul_natCast (show 0≤(2:ℝ)^(j+J0) by positivity)]
      congr 2
      ring
    rw [he] at hh
    have hpos(i:ι):0≤Real.sqrt (K i).toReal*((2:ℝ)^(j+J0))^(-(q i/2)):=by positivity
    have hs:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (fun i _=>hpos i)
    have hsum:0≤∑i,Real.sqrt (K i).toReal*((2:ℝ)^(j+J0))^(-(q i/2)):=
      Finset.sum_nonneg (fun i _=>hpos i)
    nlinarith [norm_nonneg (V j)]
  have hmajor:Summable (fun j:ℕ=>∑i,Real.sqrt (K i).toReal*((2:ℝ)^(j+J0))^(-(q i/2))):=by
    have hh:∀i:ι,Summable (fun j:ℕ=>Real.sqrt (K i).toReal*
        ((2:ℝ)^J0*(2:ℝ)^j)^(-(q i/2))):=fun i=>
      (StateBands.geometric_bands (div_pos (hq i) (by norm_num)) (by positivity:(0:ℝ)<(2:ℝ)^J0)).1.mul_left _
    have hs':=summable_sum (s:=Finset.univ) (fun i _=>hh i)
    simpa only [pow_add,mul_comm ((2:ℝ)^J0)] using hs'
  have hnorm:Summable (fun j=>‖V j‖):=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hv hmajor
  have htotal:(∑'j,‖V j‖)≤∑i,Real.sqrt (K i).toReal*
      StateBands.geometricConstant (q i/2)*((2:ℝ)^J0)^(-(q i/2)):=by
    calc
      _≤∑'j,∑i,Real.sqrt (K i).toReal*((2:ℝ)^(j+J0))^(-(q i/2)):=
        hnorm.tsum_le_tsum hv hmajor
      _=∑i,Real.sqrt (K i).toReal*StateBands.geometricConstant (q i/2)*
          ((2:ℝ)^J0)^(-(q i/2)):=by
        rw [Summable.tsum_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [tsum_mul_left]
          have he: (∑'j:ℕ,((2:ℝ)^(j+J0))^(-(q i/2)))=
              StateBands.geometricConstant (q i/2)*((2:ℝ)^J0)^(-(q i/2)):=by
            simpa only [pow_add,mul_comm ((2:ℝ)^J0)] using
              (StateBands.geometric_bands (div_pos (hq i) (by norm_num))
                (by positivity:(0:ℝ)<(2:ℝ)^J0)).2
          rw [he]
          ring
        · intro i _
          simpa only [pow_add,mul_comm ((2:ℝ)^J0)] using
            (StateBands.geometric_bands (div_pos (hq i) (by norm_num))
              (by positivity:(0:ℝ)<(2:ℝ)^J0)).1.mul_left (Real.sqrt (K i).toReal)
  have hrep:∀ᵐx∂μ,∀j,V j x=F j x:=by
    rw [ae_all_iff]
    intro j
    exact ((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp
  intro L
  let W:Lp E 2 μ:=∑j∈Finset.range L,V j
  have he:(fun x=>W x)=ᵐ[μ] (fun x=>∑j∈Finset.range L,F j x):=by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range L) V,hrep] with x hx hr
    exact hx.trans (Finset.sum_congr rfl (fun j _=>hr j))
  have hiW:Integrable (fun x=>‖W x‖^2) μ:=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable W)).mp (Lp.memLp W)
  have hEq:(∫x,‖∑j∈Finset.range L,F j x‖^2 ∂μ)=‖W‖^2:=by
    rw [PredictableL2.realLp_norm_sq]
    exact integral_congr_ae (he.symm.mono (fun _ hx=>congrArg (fun e:E=>‖e‖^2) hx))
  refine ⟨hiW.congr (he.mono (fun _ hx=>congrArg (fun e:E=>‖e‖^2) hx)),?_⟩
  rw [hEq,Real.sqrt_sq (norm_nonneg _)]
  exact (norm_sum_le (Finset.range L) V).trans
    ((hnorm.sum_le_tsum (Finset.range L) (fun j _=>norm_nonneg _)).trans htotal)
end SHE.HilbertENNFinitePrefixes
