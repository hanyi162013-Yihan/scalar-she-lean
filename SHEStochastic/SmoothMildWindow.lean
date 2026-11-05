module

public import SHEStochastic.SmoothMildSegment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.SmoothMildWindow
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H v h : ℝ≥0)
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ} (hell : 0 < ell)
  (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap) (Z : Ω → StateL2)

structure Data where
  value : ℝ≥0 → Ω → StateL2
  continuous : ∀ ω, Continuous (value · ω)
  predictable : StronglyMeasurable[(SHE.DeterministicItoShift.filtration F v).predictable]
    (Function.uncurry value)
  input : (t : ℝ≥0) → t ≤ h → Process (E := RealHaarIntegrand.Columns) F μ H
  input_ae : ∀ t ht, input t ht =ᵐ[energyMeasure μ H]
    SHE.DeterministicItoShift.extend v h (SmoothMildSegment.kernel ha hell hb value t)
  equation : ∀ t ht, value t =ᵐ[μ] fun ω ↦ RealHeat.realHeat (t : ℝ) (Z ω)+I.integral (input t ht) ω

variable {F μ H v h I ha hell hb Z}

theorem initial (D : Data F μ H v h I ha hell hb Z) : D.value 0 =ᵐ[μ] Z := by
  have hz : D.input 0 zero_le = 0 := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [D.input_ae 0 zero_le, ae_eq_of_ae_eq_trim
      (Lp.coeFn_zero RealHaarIntegrand.Columns 2 ((energyMeasure μ H).trim (predictable_le_product F)))]
      with p hp h0
    rw [hp, h0]
    unfold SHE.DeterministicItoShift.extend
    split_ifs <;> try rfl
    exact HaarKernelApproximation.kernel_zero hell
      (by simp only [NNReal.coe_zero, zero_sub]; exact neg_nonpos.mpr (SHE.DeterministicItoShift.relative v p).1.2) _
  have hh := D.equation 0 zero_le
  rw [hz, map_zero] at hh
  filter_upwards [hh, Lp.coeFn_zero StateL2 2 μ] with ω he h0
  simpa only [NNReal.coe_zero, RealHeat.realHeat_zero, ContinuousLinearMap.id_apply, h0,
    Pi.zero_apply, add_zero] using he

/-- A local smooth solution represented in the original global integral,
with its actual globally extended heat-column inputs. -/
theorem exists_data (hvh : v+h ≤ H) (hh : (h : ℝ) ≤ 1) (hp : 0 < h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {K β : ℝ} (hβ : 0 < β) (hK : 0 ≤ K) (hholder : ∀ z w, |a z-a w| ≤ K*|z-w|^β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
    (hZ₀ : StronglyMeasurable[F v] Z) (hZ : MemLp Z 2 μ) :
    Nonempty (Data F μ H v h I ha hell hb Z) := by
  obtain ⟨U, hc, hpU, hf, heq⟩ := SmoothMildRestart.exists_window F μ H v h hvh I B hBDG
    hh hp hnull ha hell hb hβ hK hholder hLip Z hZ₀ hZ
  let FV := SHE.DeterministicItoShift.filtration F v
  let localInput (t : ℝ≥0) (ht : t ≤ h) := DampedFixedIntegral.input FV μ h hh
    (Λ := 0) (by norm_num) hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
      (ContinuousHeatMild.coefficientFunction ha hell hb U) hf t ht
  refine ⟨{
    value := U
    continuous := hc
    predictable := hpU
    input := fun t ht ↦ SHE.DeterministicItoShift.input F μ H v h hvh (localInput t ht)
    input_ae := ?_
    equation := heq }⟩
  intro t ht
  have hm : @Measurable _ _ (FV).predictable _ (SmoothMildSegment.kernel ha hell hb U t) := by
    rw [SmoothMildSegment.kernel_eq_damped]
    exact (DampedFixedIntegral.kernel_predictable FV hell hf t).measurable
  have hl : localInput t ht =ᵐ[energyMeasure μ h] SmoothMildSegment.kernel ha hell hb U t := by
    rw [SmoothMildSegment.kernel_eq_damped]
    exact DampedFixedIntegral.input_ae FV μ h hh (Λ := 0) (by norm_num) hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2)) _ hf t ht
  exact (SHE.DeterministicItoShift.input_ae F μ H v h hvh (localInput t ht)).trans
    (SHE.DeterministicItoShift.extend_ae F μ H v h hvh (Lp.stronglyMeasurable (localInput t ht)).measurable hm hl)

end SHEStochastic.SmoothMildWindow
