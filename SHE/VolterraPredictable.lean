module

public import SHE.VolterraPath
public import SHE.ContinuousPredictable
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.VolterraPredictable
open MeasureTheory Set LowBands VolterraPath
open scoped NNReal ENNReal
local instance volterraPredictable_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance volterraPredictable_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance volterraPredictable_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

def clip (r : ℝ) : ℝ := max 0 (min r 1)

theorem clip_mem (r : ℝ) : clip r ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem clip_eq {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : clip r=r := by
  rw [clip,min_eq_left hr.2,max_eq_right hr.1]

theorem clip_continuous : Continuous clip := by unfold clip; fun_prop

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Λ : ℝ) (U : ℝ≥0 → Ω → StateL2)

theorem value_adapted (ha : StronglyAdapted 𝓕 U)
    (hc : ∀ ω,Continuous (fun t => U t ω)) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] (fun ω => value Λ (fun s => U s ω) t) := by
  letI : MeasurableSpace Ω := 𝓕 t
  let F : ℝ → Ω → StateL2 := fun r ω => unitIntegrand Λ (fun s => U s ω) t (clip r)
  have hFcont : ∀ ω,Continuous (fun r => F r ω) := by
    intro ω
    have hp : Continuous (fun r : ℝ => (t,clip r)) := continuous_const.prodMk clip_continuous
    have he := (unitIntegrand_continuous Λ (hc ω)).comp hp
    exact he
  have hFmeas : ∀ r,StronglyMeasurable (F r) := by
    intro r
    have hst : t*(clip r).toNNReal ≤ t := by
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_mul,Real.coe_toNNReal _ (clip_mem r).1]
      nlinarith [t.2,(clip_mem r).2]
    have hu : StronglyMeasurable (U (t*(clip r).toNNReal)) :=
      (ha (t*(clip r).toNNReal)).mono (𝓕.mono hst)
    have hh := (RealHeat.realHeat ((t:ℝ)*(1-clip r))).continuous.comp_stronglyMeasurable hu
    exact hh.const_smul (Real.exp (-Λ*((t:ℝ)*(1-clip r))))
  have hjoint : StronglyMeasurable (Function.uncurry F) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hFcont hFmeas
  have hi : StronglyMeasurable (fun ω => ∫ r in Icc (0:ℝ) 1,F r ω) :=
    hjoint.integral_prod_left (μ := (volume:Measure ℝ).restrict (Icc 0 1))
  have hm := hi.const_smul (t:ℝ)
  have he : (fun ω => value Λ (fun s => U s ω) t)=
      (fun ω => (t:ℝ) • ∫ r in Icc (0:ℝ) 1,F r ω) := by
    funext ω
    rw [value_eq_unit]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    dsimp only [F]
    rw [clip_eq hr]
  rw [he]
  exact hm

/-- The actual deterministic convolution of a continuous adapted input
is again continuous, adapted and predictable. -/
theorem value_predictable (ha : StronglyAdapted 𝓕 U)
    (hc : ∀ ω,Continuous (fun t => U t ω)) :
    StronglyMeasurable[𝓕.predictable]
      (fun p : ℝ≥0 × Ω => value Λ (fun s => U s p.2) p.1) :=
  ContinuousPredictable.stronglyMeasurable 𝓕 (fun t ω => value Λ (fun s => U s ω) t)
    (value_adapted 𝓕 Λ U ha hc) (fun ω => continuous_value Λ (hc ω))

end SHE.VolterraPredictable
