module
public import SHE.SmoothMildFixedTime
import all SHE.SmoothMildFixedTime
public import SHE.ConstantHaarCoefficient
public import SHE.AdditiveResidualPair
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
namespace SHE.AdditiveSmoothMild
open MeasureTheory PredictableL2 LowBands ContinuousHeatMild
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

def coefficient(κ:ℝ)(a:ℝ→ℝ):Bool→ℝ→ℝ:=Bool.rec a (fun _=>κ)
def lower(κ ell:ℝ):Bool→ℝ:=Bool.rec ell κ
def upper(κ M:ℝ):Bool→ℝ:=Bool.rec M κ
def holder(K:ℝ):Bool→ℝ:=Bool.rec K 0
theorem measurable(κ:ℝ){a:ℝ→ℝ}(ha:Measurable a):∀b,Measurable (coefficient κ a b):=by
  intro b
  cases b
  · exact ha
  · exact measurable_const
theorem positive{κ ell:ℝ}(hκ:0<κ)(hell:0<ell):∀b,0<lower κ ell b:=by
  intro b
  cases b
  · exact hell
  · exact hκ
theorem bounds(κ:ℝ){a:ℝ→ℝ}{ell M:ℝ}(hb:∀z,ell≤a z∧a z≤M):
    ∀b z,lower κ ell b≤coefficient κ a b z∧coefficient κ a b z≤upper κ M b:=by
  intro b z
  cases b
  · exact hb z
  · exact ⟨le_refl _,le_refl _⟩
theorem holder_nonneg{K:ℝ}(hK:0≤K):∀b,0≤holder K b:=by
  intro b
  cases b
  · exact hK
  · exact le_refl _
theorem holder_bound(κ:ℝ){a:ℝ→ℝ}{K β:ℝ}(h:∀z w,|a z-a w|≤K*|z-w|^β):
    ∀b z w,|coefficient κ a b z-coefficient κ a b w|≤holder K b*|z-w|^β:=by
  intro b z w
  cases b
  · exact h z w
  · simp [coefficient,holder]

variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
  (H:ℝ≥0)(hH:(H:ℝ)≤1)(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
  {ell M K β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hK:0≤K)
  (hholder:∀z w,|a z-a w|≤K*|z-w|^β)
variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
  (B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
  (hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)

structure Solution(u₀:StateL2) where
  model:SmoothPicardCommonLaw.Mild 𝓕 μ H (coefficient κ a) (measurable κ ha)
      (lower κ ell) (upper κ M) (holder K) (positive hκ hell) (bounds κ hb)
      β hβ (holder_nonneg hK) (holder_bound κ hholder) I
      (fun t=>RealHeat.realHeat (t:ℝ) u₀)
  predictable:StronglyMeasurable[𝓕.predictable] (Function.uncurry model.value)
  coefficient:StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb model.value)
  mild:        ∀(t:ℝ≥0)(ht:t≤H),model.value t=ᵐ[μ] fun ω=>RealHeat.realHeat (t:ℝ) u₀+
          AdditiveResidualPair.additiveTerminal 𝓕 μ H hH (Λ:=0) (by norm_num) κ hκ (I true) t ht ω+
          DampedFixedIntegral.value 𝓕 μ H hH (Λ:=0) (by norm_num) hell
            (hell.le.trans ((hb 0).1.trans (hb 0).2))
            (coefficientFunction ha hell hb model.value) coefficient (I false) t ht ω

include hH hBDG hpos hnull in
/-- Actual full-horizon smooth construction, retaining both common law
and the exact fixed-time additive/residual equation. -/
theorem exists_solution {L:ℝ≥0}(hLip:LipschitzWith L (fun x=>(a x:ℂ)))(u₀:StateL2):
    Nonempty (Solution (a:=a) (ell:=ell) (M:=M) (K:=K) (β:=β) (𝓕:=𝓕) (μ:=μ) (H:=H) (hH:=hH) (κ:=κ) (hκ:=hκ) (ha:=ha)
      (hell:=hell) (hb:=hb) (hβ:=hβ) (hK:=hK) (hholder:=hholder) (I:=I) u₀) := by
  have hp:Continuous (fun t:ℝ≥0=>((t:ℝ),u₀)):=continuous_subtype_val.prodMk continuous_const
  have hz:=RealHeat.continuous_realHeat_action.comp hp
  change Continuous (fun t:ℝ≥0=>RealHeat.realHeat (t:ℝ) u₀) at hz
  have hLip':LipschitzWith L (fun x=>(coefficient κ a false x:ℂ)):=by
    change LipschitzWith L (fun x=>(a x:ℂ))
    exact hLip
  let Z:Process (E:=StateL2) 𝓕 μ H:=HeatInitialProcess.process 𝓕 μ H u₀
  have hZ:(fun p:ℝ≥0×Ω=>RealHeat.realHeat (p.1:ℝ) u₀)=ᵐ[energyMeasure μ H] Z:=
    (HeatInitialProcess.process_ae 𝓕 μ H u₀).symm
  have hex:=SmoothMildFixedTime.exists_mild_equation (L:=L)
    𝓕 μ H hH (coefficient κ a) (measurable κ ha) (lower κ ell) (upper κ M) (holder K)
    (positive hκ hell) (bounds κ hb) β hβ (holder_nonneg hK) (holder_bound κ hholder)
    I B hBDG hpos hnull (fun t=>RealHeat.realHeat (t:ℝ) u₀) hz hLip' Z hZ
  obtain ⟨A,hdet,hpred,hfield,heq⟩:=hex
  change StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb A.value) at hfield
  refine ⟨⟨A,hpred,hfield,?_⟩⟩
  intro t ht
  have he:=heq t ht
  convert he using 1 <;>
    simp only [coefficient,lower,upper,holder,NonlinearConvolution.field,ConstantHaarCoefficient.field] <;> rfl
end SHE.AdditiveSmoothMild
