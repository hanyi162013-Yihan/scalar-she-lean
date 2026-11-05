module
public import SHE.HilbertFiniteRateTails

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SHE.HilbertENNRateTails
open Classical Filter MeasureTheory Real PredictableL2
open scoped BigOperators ENNReal Topology
variable {X E ι:Type*}[MeasurableSpace X][NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E][Fintype ι]
variable (μ:Measure X)(F:ℕ→X→E)(hF:∀j,Measurable (F j))
variable (q:ι→ℝ)(K:ι→ℝ≥0∞)(hK:∀i,K i≠∞)
variable (hb:∀j,(∫⁻x,ENNReal.ofReal (‖F j x‖^2) ∂μ)≤
  ∑i,K i*ENNReal.ofReal (((2:ℝ)^j)^(-q i)))

include hF hK hb in
/-- A finite physical ENN energy cap gives genuine L2 integrability;
none of the rates is interpreted through a convention-zero integral. -/
theorem integrable(j:ℕ):Integrable (fun x=>‖F j x‖^2) μ:=by
  refine ⟨((hF j).norm.pow_const 2).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
  apply lt_of_le_of_lt (hb j)
  apply lt_top_iff_ne_top.mpr
  exact ENNReal.sum_ne_top.mpr (fun i _=>ENNReal.mul_ne_top (hK i) ENNReal.ofReal_ne_top)

include hK hb in
/-- The actual native noise fields sum strongly in the original product
L2 space. Current, past, relative and arbitrary bad tails retain their
own exponents and their true correlated global energy weights. -/
theorem dyadic(hq:∀i,0<q i):
    let hi:=integrable μ F hF q K hK hb
    let V:=HilbertBandTails.vector μ F hF hi
    Summable V ∧
      (∀J:ℕ,‖∑'n,V (n+J)‖≤∑i,Real.sqrt (K i).toReal*
        StateBands.geometricConstant (q i/2)*((2:ℝ)^J)^(-(q i/2))) ∧
      (∀L:ℕ,Integrable (fun x=>‖(∑j∈Finset.range L,F j x)-(∑'j,V j) x‖^2) μ) ∧
      Tendsto (fun L:ℕ=>∫x,‖(∑j∈Finset.range L,F j x)-(∑'j,V j) x‖^2 ∂μ) atTop (𝓝 0):=by
  intro hi V
  have hr(j:ℕ):(∫x,‖F j x‖^2 ∂μ)≤
      ∑i,(Real.sqrt (K i).toReal)^2*((2:ℝ)^j)^(-2*(q i/2)):=by
    have he:=ofReal_integral_eq_lintegral_ofReal (hi j) (ae_of_all _ (fun _=>sq_nonneg _))
    have ht:∀i:ι,K i*ENNReal.ofReal (((2:ℝ)^j)^(-q i))≠∞:=
      fun i=>ENNReal.mul_ne_top (hK i) ENNReal.ofReal_ne_top
    have hh:=ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _=>ht i)) (hb j)
    rw [←he,ENNReal.toReal_ofReal (integral_nonneg (fun _=>sq_nonneg _)),
      ENNReal.toReal_sum (fun i _=>ht i)] at hh
    have hp(i:ι):(ENNReal.ofReal (((2:ℝ)^j)^(-q i))).toReal=((2:ℝ)^j)^(-q i):=
      ENNReal.toReal_ofReal (Real.rpow_nonneg (show 0≤(2:ℝ)^j by positivity) _)
    calc
      _≤∑i,(K i).toReal*(((2:ℝ)^j)^(-q i)):=by
        simpa only [ENNReal.toReal_mul,hp] using hh
      _=_:=by
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.sq_sqrt ENNReal.toReal_nonneg]
        congr 2
        ring
  obtain ⟨hs,ht⟩:=HilbertFiniteRateTails.dyadic μ F hF hi (fun i=>q i/2)
    (fun i=>Real.sqrt (K i).toReal) (fun i=>div_pos (hq i) (by norm_num)) (fun i=>Real.sqrt_nonneg _) hr
  obtain ⟨ha,hlim⟩:=HilbertDyadicConvergence.actual_l2 μ F hF hi hs
  exact ⟨hs,ht,ha,hlim⟩

end SHE.HilbertENNRateTails
