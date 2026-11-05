module
public import SHE.HaarFixedTerminalEnergy
public import SHE.ApproximationCells
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.LeftFrozenHaarKernel
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

/-- The actual deterministic left endpoint, including time zero. -/
def past(n:ℕ)(s:ℝ≥0):ℝ≥0:=(ApproximationClock.left n (s:ℝ)).toNNReal

theorem past_le(n:ℕ)(s:ℝ≥0):past n s≤s:=by
  by_cases hs:0<s
  · exact Real.toNNReal_le_iff_le_coe.mpr (ApproximationClock.left_bounds n (show 0<(s:ℝ) from hs)).2.1.le
  · have hz:s=0:=le_antisymm (le_of_not_gt hs) zero_le
    subst s
    apply Real.toNNReal_le_iff_le_coe.mpr
    change ApproximationClock.left n 0≤0
    simp only [ApproximationClock.left,ApproximationClock.right,zero_div,Nat.ceil_zero,
      Nat.cast_zero,mul_zero,zero_sub]
    exact neg_nonpos.mpr (ApproximationClock.delta_pos n).le

theorem past_measurable(n:ℕ):Measurable (past n):=
  measurable_real_toNNReal.comp ((ApproximationClock.left_measurable n).comp measurable_coe_nnreal_real)

theorem past_tendsto(s:ℝ≥0):Tendsto (fun n=>past n s) atTop (𝓝 s):=by
  simpa only [past,Real.toNNReal_coe,Function.comp_def] using
    (continuous_real_toNNReal.tendsto (s:ℝ)).comp (ApproximationClock.left_tendsto s.2)

variable {Ω:Type*}[MeasurableSpace Ω]
variable {a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)
variable(U:ℝ≥0→Ω→StateL2)

/-- The literal heat-Haar kernel with the nonlinear coefficient known
at the left endpoint of each cell. Unlike terminal-time approximation,
this can be integrated as finite original Brownian increments. -/
def value(n:ℕ)(p:ℝ≥0×(ℝ≥0×Ω)):RealHaarIntegrand.Columns:=
  if p.2.1<p.1 then
    kernel a ha ell M hell hb ((p.1:ℝ)-(past n p.2.1:ℝ),U (past n p.2.1) p.2.2)
  else 0

variable {Holder β:ℝ}(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)

include hβ hHolder hholder in
theorem value_measurable (hU:Measurable (Function.uncurry U))(n:ℕ):
    Measurable (value ha hell hb U n):=by
  have hs:Measurable (fun p:ℝ≥0×(ℝ≥0×Ω)=>past n p.2.1):=
    (past_measurable n).comp measurable_snd.fst
  exact ((kernel_measurable ha hell hb hβ hHolder hholder).comp
    (((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_coe_nnreal_real.comp hs)).prodMk
      (hU.comp (hs.prodMk measurable_snd.snd)))).ite
        (measurableSet_lt measurable_snd.fst measurable_fst) measurable_const

variable {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))

include hLip in
/-- Actual continuous states give pointwise consistency, including the
positive heat singularity, with no convergence premise supplied. -/
theorem value_tendsto (hc:∀ω,Continuous (fun s=>U s ω))
    (t s:ℝ≥0)(ht:(t:ℝ)≤1)(ω:Ω):
    Tendsto (fun n=>value ha hell hb U n (t,(s,ω))) atTop
      (𝓝 (kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),U s ω))):=by
  by_cases hs:s<t
  · have hage:0<(t:ℝ)-(s:ℝ):=sub_pos.mpr (by exact_mod_cast hs)
    have hages(n:ℕ):(t:ℝ)-(s:ℝ)≤(t:ℝ)-(past n s:ℝ):=
      sub_le_sub_left (by exact_mod_cast past_le n s) _
    have haget(n:ℕ):(t:ℝ)-(past n s:ℝ)≤1:=by linarith [(past n s).2]
    have hstate:Tendsto (fun n=>U (past n s) ω-U s ω) atTop (𝓝 (0:StateL2)):=by
      simpa only [Function.comp_def,sub_self] using
        (((hc ω).tendsto s).comp (past_tendsto s)).sub_const (U s ω)
    have hbound(n:ℕ):
        ‖kernel a ha ell M hell hb ((t:ℝ)-(past n s:ℝ),U (past n s) ω)-
          kernel a ha ell M hell hb ((t:ℝ)-(past n s:ℝ),U s ω)‖^2≤
        (CompanionHeat.picardConstant ell M L*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)))*
          ‖U (past n s) ω-U s ω‖^2:=by
      rw [kernel_difference_norm_sq ha hell hb (hage.trans_le (hages n))]
      exact (CompanionHeat.columnEnergy_bound ha hell hb (absBound hell hb) hLip
        (hage.trans_le (hages n)) (haget n) _ _).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hage (hages n) (by norm_num))
            (CompanionHeat.picardConstant_nonneg (hell.le.trans ((hb 0).1.trans (hb 0).2)) L))
          (sq_nonneg _))
    have hsquare:Tendsto (fun n=>
        ‖kernel a ha ell M hell hb ((t:ℝ)-(past n s:ℝ),U (past n s) ω)-
          kernel a ha ell M hell hb ((t:ℝ)-(past n s:ℝ),U s ω)‖^2) atTop (𝓝 0):=by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (show Tendsto (fun n=>(CompanionHeat.picardConstant ell M L*
          ((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)))*‖U (past n s) ω-U s ω‖^2) atTop (𝓝 0) from by
          simpa using (hstate.norm.pow 2).const_mul _)
      · exact fun n=>sq_nonneg _
      · exact hbound
    have hdiff:Tendsto (fun n=>
        kernel a ha ell M hell hb ((t:ℝ)-(past n s:ℝ),U (past n s) ω)-
          kernel a ha ell M hell hb ((t:ℝ)-(past n s:ℝ),U s ω)) atTop (𝓝 0):=by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsquare.sqrt
    have htime:Tendsto (fun n=>kernel a ha ell M hell hb
        ((t:ℝ)-(past n s:ℝ),U s ω)) atTop
        (𝓝 (kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),U s ω))):=by
      exact (HaarKernelApproximation.continuousAt_real_kernel hell hage
        (coefficientField a ha ell M hell hb (U s ω))).tendsto.comp
          (tendsto_const_nhds.sub ((continuous_subtype_val.tendsto s).comp (past_tendsto s)))
    have hadd:=hdiff.add htime
    simpa only [value,ite_eq_left hs,sub_add_cancel,zero_add] using hadd
  · have hzero:kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),U s ω)=0:=
      HaarKernelApproximation.kernel_zero hell (sub_nonpos.mpr (by exact_mod_cast le_of_not_gt hs)) _
    simpa only [value,ite_eq_right hs,hzero] using
      (tendsto_const_nhds (x:=(0:RealHaarIntegrand.Columns)))

/-- A deterministic integrable heat majorant is independent of every
state, including its past frozen value. -/
theorem value_bound (n:ℕ)(t s:ℝ≥0)(ht:(t:ℝ)≤1)(hs:s<t)(ω:Ω):
    ‖value ha hell hb U n (t,(s,ω))‖^2≤
      HaarIntegrandEnergy.singleConstant M*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)):=by
  rw [value,ite_eq_left hs]
  have hage:0<(t:ℝ)-(s:ℝ):=sub_pos.mpr (by exact_mod_cast hs)
  have hlo:(t:ℝ)-(s:ℝ)≤(t:ℝ)-(past n s:ℝ):=
    sub_le_sub_left (by exact_mod_cast past_le n s) _
  exact (HaarIntegrandEnergy.kernel_small_bound hell (hage.trans_le hlo)
    (by linarith [(past n s).2]) _).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hage hlo (by norm_num))
      (HaarIntegrandEnergy.singleConstant_nonneg (hell.le.trans ((hb 0).1.trans (hb 0).2))))
end SHE.LeftFrozenHaarKernel
