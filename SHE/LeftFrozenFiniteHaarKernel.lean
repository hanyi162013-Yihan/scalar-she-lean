module
public import SHE.LeftFrozenHaarKernel
public import SHE.FiniteHaarColumnProjection
public import SHE.ApproximationCells
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.LeftFrozenFiniteHaarKernel
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

variable {Ω:Type*}[MeasurableSpace Ω]
variable {a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(U:ℝ≥0→Ω→StateL2)

/-- Both the time coefficients and the noise coordinates are now literal
finite approximations of the original heat-Haar kernel. -/
def value(n:ℕ)(p:ℝ≥0×(ℝ≥0×Ω)):RealHaarIntegrand.Columns:=
  FiniteHaarColumnProjection.projection (FiniteHaar.nodesBelow n)
    (LeftFrozenHaarKernel.value ha hell hb U n p)

variable {Holder β:ℝ}(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
include hβ hHolder hholder in
theorem value_measurable(hU:Measurable (Function.uncurry U))(n:ℕ):
    Measurable (value ha hell hb U n):=
  (FiniteHaarColumnProjection.projection (FiniteHaar.nodesBelow n)).continuous.measurable.comp
    (LeftFrozenHaarKernel.value_measurable ha hell hb U hβ hHolder hholder hU n)

variable {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))
include hLip in
theorem value_tendsto(hc:∀ω,Continuous (fun s=>U s ω))
    (t s:ℝ≥0)(ht:(t:ℝ)≤1)(ω:Ω):
    Tendsto (fun n=>value ha hell hb U n (t,(s,ω))) atTop
      (𝓝 (kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),U s ω))):=by
  let Z:=kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),U s ω)
  let V:ℕ→RealHaarIntegrand.Columns:=fun n=>LeftFrozenHaarKernel.value ha hell hb U n (t,(s,ω))
  have hv:Tendsto V atTop (𝓝 Z):=LeftFrozenHaarKernel.value_tendsto ha hell hb U hLip hc t s ht ω
  have hp:=FiniteHaarColumnProjection.tendsto Z
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbnd(n:ℕ):‖value ha hell hb U n (t,(s,ω))-Z‖≤
      ‖V n-Z‖+‖FiniteHaarColumnProjection.projection (FiniteHaar.nodesBelow n) Z-Z‖:=by
    exact FiniteHaarColumnProjection.norm_sub_le
      (E:=DyadicApproximation.RealL2) (FiniteHaar.nodesBelow n) (V n) Z
  exact squeeze_zero (fun _=>norm_nonneg _) hbnd (by
    simpa only [sub_self,norm_zero,zero_add] using
      (hv.sub_const Z).norm.add (hp.sub_const Z).norm)

theorem value_bound(n:ℕ)(t s:ℝ≥0)(ht:(t:ℝ)≤1)(hs:s<t)(ω:Ω):
    ‖value ha hell hb U n (t,(s,ω))‖^2≤
      HaarIntegrandEnergy.singleConstant M*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)):=
  (pow_le_pow_left₀ (norm_nonneg _) (FiniteHaarColumnProjection.norm_le (E:=DyadicApproximation.RealL2) (FiniteHaar.nodesBelow n) _) 2).trans
    (LeftFrozenHaarKernel.value_bound ha hell hb U n t s ht hs ω)
end SHE.LeftFrozenFiniteHaarKernel
