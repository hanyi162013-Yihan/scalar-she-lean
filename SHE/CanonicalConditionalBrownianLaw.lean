module
public import SHE.CanonicalConditionalGaussianLaws
public import SHE.CanonicalStateDriverFiltration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
namespace SHE.CanonicalConditionalBrownianLaw
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

include hU hX hBrown in
/-- The canonical conditional future driver is a genuine cylindrical
Brownian motion in the FULL future state-and-driver filtration, on ONE
prefix event. All Gaussian finite laws and all-real past independence
are derived from the actual original Brownian driver. -/
theorem law(v h:ℝ≥0)(hvh:v+h≤H)(Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    ∀ᵐp∂μ.map Z,∀n (a:Fin n→ι),
      FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=ι) h)
        (condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ p) h
        (fun i=>CanonicalStateDriverFiltration.coordinate h (a i))
        (fun i j=>if a i=a j then 1 else 0):=by
  filter_upwards[CanonicalConditionalGaussianLaws.finite_laws 𝓕 μ H U hc X hd hU hX hBrown
      v h hvh Z hZ,
    CanonicalConditionalBrownianFiltration.all_clocks 𝓕 μ H U hc X hd hU hX hBrown
      v h hvh Z hZ] with p hp hi
  intro n a
  constructor
  · intro t ht
    let tt:Fin n→Icc (0:ℝ) (h:ℝ):=fun i=>⟨t i,(t i).property,by exact_mod_cast ht i⟩
    have hclock(i:Fin n):CanonicalStateDriverFiltration.clock h (t i)=tt i:=by
      apply Subtype.ext
      exact min_eq_left (by exact_mod_cast ht i)
    have hh:=hp n a tt

    convert! hh using 1
    · funext r
      apply PiLp.ext
      intro i
      simp only[CanonicalStateDriverFiltration.coordinate,hclock,CanonicalConditionalGaussianLaws.vector]
    · congr 1
      ext i j
      simp only[BrownianFiniteCovariance.matrix,tt,Real.toNNReal_coe]

  · intro s t hst ht
    have hclock:CanonicalStateDriverFiltration.clock h s≤CanonicalStateDriverFiltration.clock h t:=by
      change min (s:ℝ) (h:ℝ)≤min (t:ℝ) (h:ℝ)
      exact min_le_min_right _ (by exact_mod_cast hst)
    exact (hi n a (CanonicalStateDriverFiltration.clock h s)
      (CanonicalStateDriverFiltration.clock h t) hclock).symm
end SHE.CanonicalConditionalBrownianLaw
