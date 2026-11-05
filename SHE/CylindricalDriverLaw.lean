module
public import SHE.FiniteCoordinateLaw
public import SHE.StandardTerminalLevy
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.CylindricalDriverLaw
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω Ω' ι:Type*}[MeasurableSpace Ω][MeasurableSpace Ω'][DecidableEq ι]

/-- The common finite laws of an actual countable cylindrical driver,
with arbitrary repeated coordinates and arbitrary observation times. -/
def Law (μ:Measure Ω)(H:ℝ≥0)(X:ι→ℝ≥0→Ω→ℝ):Prop:=
  ∀(n:ℕ)(a:Fin n→ι)(t:Fin n→ℝ≥0),(∀i,t i≤H)→
    HasLaw (fun ω=>WithLp.toLp 2 (fun i=>X (a i) (t i) ω))
      (multivariateGaussian (0:WordRecursion.State n)
        (fun i j=>(min (t i) (t j):ℝ≥0)*(if a i=a j then 1 else 0:ℝ))) μ

/-- The full driver law on its supplied terminal interval is independent
of the original probability space, once the actual finite Brownian laws
are established. No common SPDE solution law is assumed or inferred. -/
theorem map_eq (μ:Measure Ω)(ν:Measure Ω')[IsFiniteMeasure μ][IsFiniteMeasure ν]
    (H:ℝ≥0)(X:ι→ℝ≥0→Ω→ℝ)(Y:ι→ℝ≥0→Ω'→ℝ)
    (hX:∀i t,Measurable (X i t))(hY:∀i t,Measurable (Y i t))
    (hLX:Law μ H X)(hLY:Law ν H Y):
    μ.map (fun ω=>fun p:ι×Set.Iic H=>X p.1 p.2.1 ω)=
      ν.map (fun ω=>fun p:ι×Set.Iic H=>Y p.1 p.2.1 ω):=by
  apply FiniteCoordinateLaw.map_eq μ ν
    (fun p:ι×Set.Iic H=>X p.1 p.2.1) (fun p:ι×Set.Iic H=>Y p.1 p.2.1)
    (fun p=>hX _ _) (fun p=>hY _ _)
  intro n a
  let b:Fin n→ι:=fun i=>(a i).1
  let t:Fin n→ℝ≥0:=fun i=>(a i).2.1
  have ht:∀i,t i≤H:=fun i=>(a i).2.2
  have hx:=hLX n b t ht
  have hy:=hLY n b t ht
  have he:=congrArg (fun P:Measure (WordRecursion.State n)=>P.map (WithLp.ofLp))
    (hx.map_eq.trans hy.map_eq.symm)
  have hmX:Measurable (fun ω=>WithLp.toLp 2 (fun i=>X (b i) (t i) ω)):=
    (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp (measurable_pi_iff.mpr (fun i=>hX _ _))
  have hmY:Measurable (fun ω=>WithLp.toLp 2 (fun i=>Y (b i) (t i) ω)):=
    (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp (measurable_pi_iff.mpr (fun i=>hY _ _))
  rw [Measure.map_map (WithLp.measurable_ofLp 2 (Fin n→ℝ)) hmX,
    Measure.map_map (WithLp.measurable_ofLp 2 (Fin n→ℝ)) hmY] at he
  simpa only [Function.comp_def,WithLp.ofLp_toLp,b,t] using he
end SHE.CylindricalDriverLaw
