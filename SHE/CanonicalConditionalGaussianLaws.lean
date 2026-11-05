module
public import SHE.CanonicalConditionalBrownianFiltration
public import SHE.BrownianShiftedFiniteLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.CanonicalConditionalGaussianLaws
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P E ι:Type*}[MeasurableSpace Ω][MeasurableSpace P][Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω))
variable(X:ι→ℝ≥0→Ω→ℝ)(hd:∀i ω,Continuous (fun t=>X i t ω))
variable(hU:∀t,Measurable[𝓕 t] (U t))(hX:∀i t,Measurable[𝓕 t] (X i t))
variable(hBrown:∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>X (a i))
  (fun i j=>if a i=a j then 1 else 0))

def vector{h:ℝ≥0}{n:ℕ}(a:Fin n→ι)(t:Fin n→Icc (0:ℝ) (h:ℝ))
    (w:ι→C(Icc (0:ℝ) (h:ℝ),ℝ)):WordRecursion.State n:=
  WithLp.toLp 2 (fun i=>w (a i) (t i))

theorem vector_measurable{h:ℝ≥0}{n:ℕ}(a:Fin n→ι)(t:Fin n→Icc (0:ℝ) (h:ℝ)):
    Measurable (vector a t):=by
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  exact measurable_pi_iff.mpr (fun i=>(ContinuousMap.measurable_eval (t i)).comp
    (measurable_pi_apply (a i)))

include hU hX hBrown in
/-- On ONE prefix event, EVERY actual conditional finite-dimensional
future-driver law is centered Gaussian with the exact RELATIVE-time
Brownian covariance, including repeated coordinates and time zero. -/
theorem finite_laws(v h:ℝ≥0)(hvh:v+h≤H)(Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    ∀ᵐp∂μ.map Z,∀n (a:Fin n→ι)(t:Fin n→Icc (0:ℝ) (h:ℝ)),
      HasLaw (fun r:CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h=>vector a t r.2)
        (multivariateGaussian (0:WordRecursion.State n)
          (BrownianFiniteCovariance.matrix a (fun i=>(t i).val.toNNReal)))
        (condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ p):=by
  have hz:Measurable Z:=hZ.mono (𝓕.le _) le_rfl
  have hb:=CanonicalFutureStateDriver.measurable_bundle 𝓕 U hc X hd hU hX v h
  have hp:=condDistrib_comp (μ:=μ) (X:=Z)
    (Y:=CanonicalFutureStateDriver.bundle U hc X hd v h)
    hz.aemeasurable hb.aemeasurable measurable_snd
  have hf:=BrownianFuturePath.conditional 𝓕 μ H X hd hX hBrown v h hvh Z hZ
  filter_upwards[hp,hf] with p hp hf
  have hm:(condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ p).map Prod.snd=
      μ.map (BrownianFuturePath.value X hd v h):=by
    rw[←Kernel.map_apply _ measurable_snd,←hp]
    change condDistrib (BrownianFuturePath.value X hd v h) Z μ p= _
    rw[hf,Kernel.const_apply]
  intro n a t
  have ht:∀i,(t i).val.toNNReal≤h:=fun i=>by
    simpa only[Real.toNNReal_coe] using Real.toNNReal_le_toNNReal (t i).property.2
  have hl:=BrownianShiftedFiniteLaw.law 𝓕 μ H X hBrown v h hvh a _ ht
  refine ⟨((vector_measurable a t).comp measurable_snd).aemeasurable,?_⟩
  calc
    _=((condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ p).map Prod.snd).map
        (vector a t):=(Measure.map_map (vector_measurable a t) measurable_snd).symm
    _=(μ.map (BrownianFuturePath.value X hd v h)).map (vector a t):=by rw[hm]
    _=μ.map (fun ω=>WithLp.toLp 2
        (fun i=>X (a i) (v+(t i).val.toNNReal) ω-X (a i) v ω)):=by
      rw[Measure.map_map (vector_measurable a t) (BrownianFuturePath.measurable 𝓕 X hd hX v h)]
      rfl
    _= _:=hl.map_eq
end SHE.CanonicalConditionalGaussianLaws
