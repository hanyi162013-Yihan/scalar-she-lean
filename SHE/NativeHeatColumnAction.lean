module
public import SHE.NativeHeatObservation
public import SHE.AdditivePhysicalFactor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeHeatColumnAction
open MeasureTheory FiniteHaar CircleHeat DyadicApproximation NativeHeatObservation
open scoped ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- Actual square-summable columns synthesize under every real scalar
observation; this identity is proved on the original Haar coordinates. -/
theorem inner_map {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    (K:HilbertColumns.Space HaarNode E)(A:RealHaarInput→L[ℝ]E)
    (hA:∀q,A (lp.single 2 q (1:ℝ))=K q)(L:E→L[ℝ]ℝ)(u:RealHaarInput):
    inner ℝ (HilbertColumns.mapCLM L K) u=L (A u):=by
  classical
  have hs:=lp.hasSum_single (by norm_num:(2:ENNReal)≠∞) u
  have hleft:HasSum (fun q=>inner ℝ (HilbertColumns.mapCLM L K) (lp.single 2 q (u q)))
      (inner ℝ (HilbertColumns.mapCLM L K) u):=
    (innerSL ℝ (HilbertColumns.mapCLM L K)).hasSum hs
  have hright:= (L.comp A).hasSum hs
  apply hleft.unique
  convert hright using 1
  funext q
  have he:(lp.single 2 q (u q):RealHaarInput)=(u q) • lp.single 2 q (1:ℝ):=by
    simpa only [smul_eq_mul,mul_one] using
      lp.single_smul (E:=fun _:HaarNode=>ℝ) 2 q (u q) (1:ℝ)
  rw [lp.inner_single_right]
  simp only [HilbertColumns.mapCLM_apply,Real.inner_apply]
  rw [he,map_smul]
  simp only [ContinuousLinearMap.comp_apply,hA,smul_eq_mul]
  ring
  rfl

/-- Positive native-time heat columns act on an arbitrary original real
Haar input as heat applied to the literal physical Haar factor. -/
theorem additive {κ t:ℝ}(hκ:0<κ)(ht:0<t)(L:RealL2→L[ℝ]ℝ)(u:RealHaarInput):
    inner ℝ (HilbertColumns.mapCLM L
      (NativeHeatObservation.kernel κ κ hκ (t,AdditiveHaarForcing.constantField κ hκ))) u=
    L (NativeHeatObservation.heat t
      (realPart (fieldFactor κ κ hκ (AdditiveHaarForcing.constantField κ hκ) (realInputEmbed u)))):=by
  let W:=AdditivePhysicalFactor.whiteCoordinates κ hκ
  let A:RealHaarInput→L[ℝ]RealL2:=
    (NativeHeatObservation.heat t).comp
      ((Real.sqrt κ) • W.toLinearIsometry.toContinuousLinearMap)
  have hA(q:HaarNode):A (lp.single 2 q (1:ℝ))=
      NativeHeatObservation.kernel κ κ hκ (t,AdditiveHaarForcing.constantField κ hκ) q:=by
    have he:realInputEmbed (lp.single 2 q (1:ℝ):RealHaarInput)=(lp.single 2 q (1:ℂ):HaarInput):=by
      apply lp.ext
      funext r
      by_cases h:q=r
      · subst r
        simp [realInputEmbed,lp.single_apply]
      · simp [realInputEmbed,lp.single_apply,Pi.single_eq_of_ne (Ne.symm h)]
    have hf:=AdditivePhysicalFactor.factor_constant κ hκ (lp.single 2 q (1:ℝ))
    rw [he,fieldFactor,factor_single] at hf
    have hr:=globalHaarColumn_real_ae q (AdditiveHaarForcing.constantField κ hκ).1
      (AdditiveHaarForcing.constantField κ hκ).2.1
    change RealHeat.realHeat (t/timeScale) (Real.sqrt κ • W (lp.single 2 q (1:ℝ)))=_
    rw [←hf]
    change realPart (CircleHeat.heat (t/timeScale)
      (realEmbed (realPart (globalHaarColumn q (AdditiveHaarForcing.constantField κ hκ).1))))=_
    rw [realEmbed_realPart_of_real _ hr]
    change _=realPart (HaarHeatIntegrand.kernel κ κ hκ (t/timeScale,AdditiveHaarForcing.constantField κ hκ) q)
    rw [HaarHeatIntegrand.kernel_apply,if_pos (div_pos ht timeScale_pos)]
  rw [inner_map _ A hA L u]
  rw [AdditivePhysicalFactor.factor_constant]
  rfl
end SHE.NativeHeatColumnAction
