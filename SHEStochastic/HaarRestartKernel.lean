module

public import SHEStochastic.SmoothMildSegment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.HaarRestartKernel
open MeasureTheory SHE SHE.FiniteHaar SHE.LowBands
open scoped NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

local instance : SecondCountableTopology SHE.CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ} (hell : 0 < ell)
  (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)

open SmoothMildSegment

theorem congr_state (U V : ℝ≥0 → Ω → StateL2) (t : ℝ≥0) (p : ℝ≥0 × Ω)
    (h : U p.1 p.2 = V p.1 p.2) : kernel ha hell hb U t p = kernel ha hell hb V t p := by
  simp only [kernel, ContinuousHeatMild.coefficientFunction, h]

theorem zero_after (U : ℝ≥0 → Ω → StateL2) (t : ℝ≥0) (p : ℝ≥0 × Ω) (ht : t ≤ p.1) :
    kernel ha hell hb U t p = 0 := by
  exact HaarKernelApproximation.kernel_zero hell (sub_nonpos.mpr (show (t : ℝ) ≤ p.1 from ht)) _

/-- Earlier inputs are unchanged by deterministic path gluing, including
their zero extension after their terminal time. -/
theorem past (v h : ℝ≥0) (U V : ℝ≥0 → Ω → StateL2) (t : ℝ≥0) (ht : t ≤ v)
    (p : ℝ≥0 × Ω) : kernel ha hell hb (AdaptedRestartGluing.value v h U V) t p =
      kernel ha hell hb U t p := by
  by_cases hp : p.1 ≤ v
  · apply congr_state ha hell hb
    exact congrFun (AdaptedRestartGluing.before v h U V p.1 hp) p.2
  · rw [zero_after ha hell hb _ t p (ht.trans (le_of_not_ge hp)),
      zero_after ha hell hb U t p (ht.trans (le_of_not_ge hp))]

/-- The new full heat input is the propagated old input plus the
literally translated new-window input. Only the single joining time is
excluded; it has zero Lebesgue measure in the stochastic integral. -/
theorem split (v h : ℝ≥0) (U V : ℝ≥0 → Ω → StateL2) (t : ℝ≥0)
    (hvt : v ≤ t) (hth : t ≤ v+h) (p : ℝ≥0 × Ω) (hpv : p.1 ≠ v)
    (hInitial : V 0 p.2 = U v p.2) :
    kernel ha hell hb (AdaptedRestartGluing.value v h U V) t p =
      HilbertColumns.mapCLM (RealHeat.realHeat ((t-v : ℝ≥0) : ℝ)) (kernel ha hell hb U v p) +
        SHE.DeterministicItoShift.extend v h (kernel ha hell hb V (t-v)) p := by
  by_cases hp : p.1 ≤ v
  · have hp' : p.1 < v := lt_of_le_of_ne hp hpv
    have hraw : kernel ha hell hb (AdaptedRestartGluing.value v h U V) t p = kernel ha hell hb U t p :=
      congr_state ha hell hb _ _ t p (congrFun (AdaptedRestartGluing.before v h U V p.1 hp) p.2)
    rw [hraw, SHE.DeterministicItoShift.extend, if_neg (not_lt.mpr hp), add_zero]
    have he := RealHaarSemigroup.map_kernel hell (t-v : ℝ≥0).property
      (sub_pos.mpr (show (p.1 : ℝ) < v from hp'))
      (ContinuousHeatMild.coefficientFunction ha hell hb U p)
    have hage : ((t-v : ℝ≥0) : ℝ) + ((v : ℝ)-(p.1 : ℝ)) = (t : ℝ)-(p.1 : ℝ) := by
      rw [NNReal.coe_sub hvt]
      ring
    have hk := congrArg (fun r : ℝ ↦ RealHaarIntegrand.kernel ell cap hell
      (r, ContinuousHeatMild.coefficientFunction ha hell hb U p)) hage.symm
    exact hk.trans (by convert! he.symm using 1 <;> rfl)
  · have hp' : v < p.1 := lt_of_not_ge hp
    rw [zero_after ha hell hb U v p hp'.le, map_zero, zero_add]
    by_cases hph : p.1 ≤ v+h
    · rw [SHE.DeterministicItoShift.extend, if_pos hp', if_pos hph]
      have hlocal : p.1-v ≤ h := (tsub_le_iff_right).mpr (by simpa only [add_comm] using hph)
      have hstate : AdaptedRestartGluing.value v h U V p.1 p.2 = V (p.1-v) p.2 := by
        rw [AdaptedRestartGluing.after v h U V p.1 hp'.le]
        change U v p.2 + (V (min (p.1-v) h) p.2 - V 0 p.2) = _
        rw [min_eq_left hlocal, hInitial]
        abel
      unfold kernel ContinuousHeatMild.coefficientFunction SHE.DeterministicItoShift.relative
      rw [hstate]
      congr 1
      apply Prod.ext
      · rw [NNReal.coe_sub hvt, NNReal.coe_sub hp'.le]
        ring
      · rfl
    · rw [SHE.DeterministicItoShift.extend, if_pos hp', if_neg hph]
      exact zero_after ha hell hb _ t p (hth.trans (le_of_not_ge hph))

end SHEStochastic.HaarRestartKernel
