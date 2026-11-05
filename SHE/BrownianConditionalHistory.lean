module
public import SHE.ConditionalIncrementIndependence
public import SHE.BrownianFuturePath
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.BrownianConditionalHistory
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P R Y:Type*}[MeasurableSpace Ω][MeasurableSpace P]
variable[MeasurableSpace R][StandardBorelSpace R][Nonempty R]
variable[MeasurableSpace Y][StandardBorelSpace Y][Nonempty Y]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)

/-- Applying ORIGINAL full-past Brownian independence at the later
current time yields independence under conditional canonical future
laws from retained STATE+DRIVER history, not only the initial prefix. -/
theorem increment{n:ℕ}(X:Fin n→ℝ≥0→Ω→ℝ)(G:Matrix (Fin n) (Fin n) ℝ)
    (hBrown:FiniteBrownianLawOn 𝓕 μ H X G)
    (v s t:ℝ≥0)(hvs:v≤s)(hst:s≤t)(ht:t≤H)
    (Z:Ω→P)(V:Ω→R)(y:R→Y)(d:R→WordRecursion.State n)
    (hZ:Measurable[𝓕 v] Z)(hV:Measurable V)(hy:Measurable y)(hd:Measurable d)
    (hys:Measurable[𝓕 s] (y∘V))
    (he:∀ω,d (V ω)=WithLp.toLp 2 (fun i=>X i t ω-X i s ω)):
    ∀ᵐp∂μ.map Z,IndepFun y d (condDistrib V Z μ p):=by
  have hz:Measurable[𝓕 s] Z:=hZ.mono (𝓕.mono hvs) le_rfl
  have hi:IndepFun (fun ω=>(Z ω,y (V ω))) (d∘V) μ:=by
    have hi:=hBrown.2 s t hst ht
    have hp:Measurable[𝓕 s] (fun ω=>(Z ω,y (V ω))):=hz.prodMk hys
    have hh:=indep_of_indep_of_le_right hi hp.comap_le
    have he':(d∘V)=(fun ω=>WithLp.toLp 2 (fun i=>X i t ω-X i s ω)):=funext he
    rw[he']
    exact hh.symm
  exact ConditionalIncrementIndependence.under_conditional μ Z V y d
    (hZ.mono (𝓕.le _) le_rfl) hV hy hd hi
end SHE.BrownianConditionalHistory
