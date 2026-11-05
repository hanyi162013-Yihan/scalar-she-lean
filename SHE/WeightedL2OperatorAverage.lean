module
public import SHE.L2ParameterAverage
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.WeightedL2OperatorAverage
open MeasureTheory
open scoped ENNReal
variable {X P Ω C:Type*}[MeasurableSpace X][MeasurableSpace P][MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][CompleteSpace C]
variable (η:Measure X)[IsProbabilityMeasure η](ν:Measure P)[IsFiniteMeasure ν]
variable (μ:Measure Ω)[IsFiniteMeasure μ]

/-- Bounded parameter weights commute with the original L2 operator
using only genuine joint representatives; no L2-space separability or
strong measurability of the family into probability-L2 is assumed. -/
theorem commutes (T:Lp C 2 ν→L[ℝ]Lp ℝ 2 μ)
    (K:X→Lp C 2 ν)(raw:X×P→C)(hraw:MemLp raw 2 (η.prod ν))
    (hK:∀x,K x=ᵐ[ν] fun p=>raw (x,p))
    (Y:X×Ω→ℝ)(hYs:StronglyMeasurable Y)(hY:MemLp Y 2 (η.prod μ))
    (hRep:∀ᵐx∂η,T (K x)=ᵐ[μ] fun ω=>Y (x,ω))
    (φ:X→ℝ)(hφ:Measurable φ)(M:ℝ)(hφM:∀x,‖φ x‖≤M)
    (Kavg:Lp C 2 ν)(hKa:Kavg=ᵐ[ν] fun p=>∫x,φ x • raw (x,p) ∂η):
    T Kavg=ᵐ[μ] fun ω=>∫x,φ x*Y (x,ω) ∂η:=by
  let R:X×P→C:=fun z=>φ z.1 • raw z
  let W:X×Ω→ℝ:=fun z=>φ z.1*Y z
  have hR:MemLp R 2 (η.prod ν):=
    (memLp_top_of_bound (hφ.comp measurable_fst).stronglyMeasurable.aestronglyMeasurable M
      (ae_of_all _ (fun z=>hφM z.1))).smul hraw
  have hWs:StronglyMeasurable W:=(hφ.comp measurable_fst).stronglyMeasurable.mul hYs
  have hW:MemLp W 2 (η.prod μ):=by
    have hh:MemLp ((fun z:X×Ω=>φ z.1) • Y) 2 (η.prod μ):=
      (memLp_top_of_bound (hφ.comp measurable_fst).stronglyMeasurable.aestronglyMeasurable M
        (ae_of_all _ (fun z=>hφM z.1))).smul hY
    apply hh.ae_eq
    filter_upwards with z
    rfl
  have hW2:Integrable (fun z=>‖W z‖^2) (η.prod μ):=
    (memLp_two_iff_integrable_sq_norm hWs.aestronglyMeasurable).mp hW
  let Yavg:=L2ParameterAverage.value η μ W hWs hW2
  have hKr:∀x,φ x • K x=ᵐ[ν] fun p=>R (x,p):=by
    intro x
    filter_upwards [Lp.coeFn_smul (φ x) (K x),hK x] with p hp hq
    simp only [hp,Pi.smul_apply,hq,R]
  have hTr:∀ᵐx∂η,T (φ x • K x)=ᵐ[μ] fun ω=>W (x,ω):=by
    filter_upwards [hRep] with x hx
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (φ x) (T (K x)),hx] with ω hp hq
    simp only [hp,Pi.smul_apply,hq,W,smul_eq_mul]
  have he:=LpOperatorParameterAverage.commutes η ν μ T (fun x=>φ x • K x) R hR hKr
    W hW hTr Kavg hKa Yavg (L2ParameterAverage.value_ae η μ W hWs hW2)
  rw [he]
  exact L2ParameterAverage.value_ae η μ W hWs hW2
end SHE.WeightedL2OperatorAverage
