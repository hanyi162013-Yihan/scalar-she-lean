module
public import SHE.NativePathCoupling
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativePathLawComparison
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (H : ℝ≥0)
local instance twoFinite : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance integratedSigma : MeasurableSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))) := borel _
local instance integratedBorel : BorelSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))) := ⟨rfl⟩

/-- The genuine continuous-path law of a supplied native trajectory. -/
def law (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℝ≥0→Ω→E)
    (hc : ∀ω,Continuous (fun t=>U t ω)) : ProbabilityMeasure C(Icc (0:ℝ) (H:ℝ),E) :=
  ProbabilityMeasure.map (⟨μ,inferInstance⟩:ProbabilityMeasure Ω)
    (NativeContinuousPath.path H U hc)

theorem integrated_law (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℝ≥0→Ω→E)
    (hc : ∀ω,Continuous (fun t=>U t ω)) (hU : Measurable (Function.uncurry U)) :
    ProbabilityMeasure.map (law H μ U hc)
      (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ) =
      ProbabilityMeasure.map (⟨μ,inferInstance⟩:ProbabilityMeasure Ω)
        (NativeContinuousPath.integrated H U hc) := by
  apply Subtype.ext
  change Measure.map (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ)
    (μ.map (NativeContinuousPath.path H U hc)) = _
  rw [Measure.map_map (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ).continuous.measurable
    (NativeContinuousPath.measurable_path H U hc hU)]
  rfl

/-- Final native-path consumer for the actual comparison estimates.
Both original spaces may differ. Its remaining inputs are explicit true
energy limits and canonical changed-law bounds, not stochastic axioms. -/
theorem laws_eq
    (hH:0<H) (μ:Measure Ω) (ν:Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U:ℝ≥0→Ω→E) (U':ℝ≥0→Ω'→E)
    (hc:∀ω,Continuous (fun t=>U t ω)) (hc':∀ω,Continuous (fun t=>U' t ω))
    (hU:Measurable (Function.uncurry U)) (hU':Measurable (Function.uncurry U'))
    (V:ℕ→ℝ≥0→Ω→E) (V':ℕ→ℝ≥0→Ω'→E)
    (hd:∀n ω,Continuous (fun t=>V n t ω)) (hd':∀n ω,Continuous (fun t=>V' n t ω))
    (hV:∀n,Measurable (Function.uncurry (V n))) (hV':∀n,Measurable (Function.uncurry (V' n)))
    (hi:∀n,Integrable (fun z:ℝ≥0×Ω=>‖U z.1 z.2-V n z.1 z.2‖^2) (PredictableL2.energyMeasure μ H))
    (hi':∀n,Integrable (fun z:ℝ≥0×Ω'=>‖U' z.1 z.2-V' n z.1 z.2‖^2) (PredictableL2.energyMeasure ν H))
    (he:Tendsto (fun n=>∫z:ℝ≥0×Ω,‖U z.1 z.2-V n z.1 z.2‖^2 ∂PredictableL2.energyMeasure μ H) atTop (𝓝 0))
    (he':Tendsto (fun n=>∫z:ℝ≥0×Ω',‖U' z.1 z.2-V' n z.1 z.2‖^2 ∂PredictableL2.energyMeasure ν H) atTop (𝓝 0))
    (canonical:ℕ→ProbabilityMeasure (Lp E 2 (SHE.timeMeasure (H:ℝ))))
    (cost cost':ℕ→ℝ) (hcost:∀n,0≤cost n) (hcost':∀n,0≤cost' n)
    (hcl:Tendsto cost atTop (𝓝 0)) (hcl':Tendsto cost' atTop (𝓝 0))
    (hchange:∀n (f:Lp E 2 (SHE.timeMeasure (H:ℝ))→ᵇℝ),
      |(∫ω,f (NativeContinuousPath.integrated H (V n) (hd n) ω) ∂μ)-
        (∫x,f x ∂canonical n)|≤2*‖f‖*(Real.sqrt (cost n)+cost n))
    (hchange':∀n (f:Lp E 2 (SHE.timeMeasure (H:ℝ))→ᵇℝ),
      |(∫ω,f (NativeContinuousPath.integrated H (V' n) (hd' n) ω) ∂ν)-
        (∫x,f x ∂canonical n)|≤2*‖f‖*(Real.sqrt (cost' n)+cost' n)) :
    law H μ U hc=law H ν U' hc' := by
  apply SHE.interval_path_laws_eq_of_integrated_laws (by exact_mod_cast hH)
  rw [integrated_law H μ U hc hU,integrated_law H ν U' hc' hU']
  refine laws_eq_of_coupling_families
    (ProbabilityMeasure.map (⟨μ,inferInstance⟩:ProbabilityMeasure Ω) (NativeContinuousPath.integrated H U hc))
    (ProbabilityMeasure.map (⟨ν,inferInstance⟩:ProbabilityMeasure Ω') (NativeContinuousPath.integrated H U' hc'))
    (fun n=>NativePathCoupling.joint μ H U (V n) hc (hd n))
    (fun n=>NativePathCoupling.joint ν H U' (V' n) hc' (hd' n)) canonical cost cost'
    (fun n=>NativePathCoupling.first_marginal μ H U (V n) hc (hd n) hU (hV n))
    (fun n=>NativePathCoupling.first_marginal ν H U' (V' n) hc' (hd' n) hU' (hV' n))
    (fun n=>NativePathCoupling.moment μ H U (V n) hc (hd n) hU (hV n) (hi n))
    (fun n=>NativePathCoupling.moment ν H U' (V' n) hc' (hd' n) hU' (hV' n) (hi' n))
    hcost hcost' ?_ ?_ hcl hcl' ?_ ?_
  · convert he using 1
    funext n
    exact NativePathCoupling.energy_identity μ H U (V n) hc (hd n) hU (hV n) (hi n)
  · convert he' using 1
    funext n
    exact NativePathCoupling.energy_identity ν H U' (V' n) hc' (hd' n) hU' (hV' n) (hi' n)
  · intro n f
    rw [NativePathCoupling.second_marginal μ H U (V n) hc (hd n) hU (hV n)]
    change |(∫x,f x ∂μ.map (NativeContinuousPath.integrated H (V n) (hd n)))-
      (∫x,f x ∂canonical n)|≤_
    rw [integral_map (NativeContinuousPath.measurable_integrated H (V n) (hd n) (hV n)).aemeasurable
      f.continuous.aestronglyMeasurable]
    exact hchange n f
  · intro n f
    rw [NativePathCoupling.second_marginal ν H U' (V' n) hc' (hd' n) hU' (hV' n)]
    change |(∫x,f x ∂ν.map (NativeContinuousPath.integrated H (V' n) (hd' n)))-
      (∫x,f x ∂canonical n)|≤_
    rw [integral_map (NativeContinuousPath.measurable_integrated H (V' n) (hd' n) (hV' n)).aemeasurable
      f.continuous.aestronglyMeasurable]
    exact hchange' n f

end SHE.NativePathLawComparison
