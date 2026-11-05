module
public import SHE.OrderedIncrementIndependence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.BrownianConditionalGrid
open MeasureTheory ProbabilityTheory Set OrderedIncrementIndependence
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P:Type*}[MeasurableSpace Ω][MeasurableSpace P]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable{n:ℕ}(X:Fin n→ℝ≥0→Ω→ℝ)(G:Matrix (Fin n) (Fin n) ℝ)(T:ℕ→ℝ≥0)

def increments(ω:Ω)(k:ℕ):WordRecursion.State n:=
  WithLp.toLp 2 (fun i=>X i (T (k+1)) ω-X i (T k) ω)

/-- The entire ordered increment sequence, including every finite grid,
is independent of the genuine original initial past sigma algebra. -/
theorem independent
    (hBrown:FiniteBrownianLawOn 𝓕 μ H X G)
    (hX:∀i t,Measurable[𝓕 t] (X i t))(hT:Monotone T)(hTH:∀k,T k≤H)
    (Z:Ω→P)(hZ:Measurable[𝓕 (T 0)] Z):
    IndepFun Z (increments X T) μ:=by
  let m:=sigma 𝓕 X T
  have hm(k:ℕ):m k≤‹MeasurableSpace Ω›:=by
    cases k with
    | zero =>exact 𝓕.le (T 0)
    | succ k =>
      apply Measurable.comap_le
      apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
      exact measurable_pi_iff.mpr (fun i=>
        ((hX i (T (k+1))).mono (𝓕.le _) le_rfl).sub
          ((hX i (T k)).mono (𝓕.le _) le_rfl))
  have hs:Disjoint ({0}:Set ℕ) (Ioi 0):=by simp
  have hi:=indep_iSup_of_disjoint hm (brownian_grid μ 𝓕 H X G T hBrown hX hT hTH) hs
  have hz:MeasurableSpace.comap Z ‹MeasurableSpace P›≤⨆i∈({0}:Set ℕ),m i:=
    hZ.comap_le.trans (le_iSup_of_le 0 (le_iSup_of_le (by simp:0∈({0}:Set ℕ)) le_rfl))
  have hd:@Measurable Ω (ℕ→WordRecursion.State n) (⨆i∈Ioi (0:ℕ),m i) _ (increments X T):=by
    letI:MeasurableSpace Ω:=⨆i∈Ioi (0:ℕ),m i
    apply measurable_pi_iff.mpr
    intro k
    apply Measurable.of_comap_le
    exact le_iSup_of_le (k+1) (le_iSup_of_le (Nat.succ_pos k) le_rfl)
  exact indep_of_indep_of_le hi hz hd.comap_le

/-- Conditional finite-grid future laws are the ORIGINAL unconditional
Brownian-grid law on ONE almost-everywhere canonical prefix event. The
kernel equality is proved from actual Brownian increment independence. -/
theorem conditional
    (hBrown:FiniteBrownianLawOn 𝓕 μ H X G)
    (hX:∀i t,Measurable[𝓕 t] (X i t))(hT:Monotone T)(hTH:∀k,T k≤H)
    (Z:Ω→P)(hZ:Measurable[𝓕 (T 0)] Z):
    condDistrib (increments X T) Z μ=ᵐ[μ.map Z]
      Kernel.const P (μ.map (increments X T)):=by
  have hzm:Measurable Z:=hZ.mono (𝓕.le _) le_rfl
  have hdm:Measurable (increments X T):=by
    apply measurable_pi_iff.mpr
    intro k
    exact (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
      (measurable_pi_iff.mpr (fun i=>
        ((hX i (T (k+1))).mono (𝓕.le _) le_rfl).sub ((hX i (T k)).mono (𝓕.le _) le_rfl)))
  exact BrownianConditionalIncrement.kernel_of_independent μ Z _ hzm.aemeasurable hdm.aemeasurable
    (independent 𝓕 μ H X G T hBrown hX hT hTH Z hZ)
end SHE.BrownianConditionalGrid
