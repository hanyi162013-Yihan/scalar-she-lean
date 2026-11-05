module
public import SHE.StandardTerminalLevy
public import Mathlib.Probability.Kernel.CondDistrib
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.BrownianConditionalIncrement
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory
variable{Ω P F:Type*}[MeasurableSpace Ω][MeasurableSpace P][MeasurableSpace F]
variable[StandardBorelSpace F][Nonempty F]
variable(μ:Measure Ω)[IsProbabilityMeasure μ]

/-- Independence identifies the actual regular conditional law; it is
not an assumed transition-kernel equality. -/
theorem kernel_of_independent (Z:Ω→P)(Y:Ω→F)
    (hZ:AEMeasurable Z μ)(hY:AEMeasurable Y μ)(hi:IndepFun Z Y μ):
    condDistrib Y Z μ=ᵐ[μ.map Z] Kernel.const P (μ.map Y):=by
  apply condDistrib_ae_eq_of_measure_eq_compProd hZ hY
  rw [Measure.compProd_const]
  exact hi.map_prod_eq_prod_map_map hZ hY

/-- Every genuine finite Brownian vector has its true future-increment
law under almost every canonical prefix. The prefix may retain the
entire adapted state/noise history up to the restart time. -/
theorem brownian_increment
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(H:ℝ≥0)
    {n:ℕ}(X:Fin n→ℝ≥0→Ω→ℝ)(G:Matrix (Fin n) (Fin n) ℝ)
    (hBrown:FiniteBrownianLawOn 𝓕 μ H X G)
    (v t:ℝ≥0)(hvt:v≤t)(ht:t≤H)
    (Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    let inc:Ω→WordRecursion.State n:=fun ω=>WithLp.toLp 2 (fun i=>X i t ω-X i v ω)
    condDistrib inc Z μ=ᵐ[μ.map Z] Kernel.const P (μ.map inc):=by
  dsimp only
  have hmZ:AEMeasurable Z μ:=(hZ.mono (𝓕.le v) le_rfl).aemeasurable
  have hi:IndepFun Z (fun ω=>WithLp.toLp 2 (fun i=>X i t ω-X i v ω)) μ:=
    (indep_of_indep_of_le_right (hBrown.2 v t hvt ht) hZ.comap_le).symm
  have hmt:AEMeasurable (fun ω=>WithLp.toLp 2 (fun i=>X i t ω)) μ:=
    (hBrown.1 (fun _=>t) (fun _=>ht)).aemeasurable
  have hmv:AEMeasurable (fun ω=>WithLp.toLp 2 (fun i=>X i v ω)) μ:=
    (hBrown.1 (fun _=>v) (fun _=>hvt.trans ht)).aemeasurable
  have hm:AEMeasurable (fun ω=>WithLp.toLp 2 (fun i=>X i t ω-X i v ω)) μ:=by
    exact hmt.sub hmv
  exact kernel_of_independent μ Z _ hmZ hm hi
end SHE.BrownianConditionalIncrement
