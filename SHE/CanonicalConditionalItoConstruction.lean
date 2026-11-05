module
public import SHE.CanonicalConditionalBrownianLaw
public import SHE.StandardBrownianItoConstruction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.CanonicalConditionalItoConstruction
open MeasureTheory ProbabilityTheory PredictableL2 Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P E C ι:Type*}[MeasurableSpace Ω][MeasurableSpace P][Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][CompleteSpace C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(U:ℝ≥0→Ω→E) (hc:∀ω,Continuous (fun t=>U t ω))
variable(X:ι→ℝ≥0→Ω→ℝ) (hd:∀i ω,Continuous (fun t=>X i t ω))
variable(hU:∀t,Measurable[𝓕 t] (U t)) (hX:∀i t,Measurable[𝓕 t] (X i t))
variable(hBrown:∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>X (a i))
  (fun i j=>if a i=a j then 1 else 0))
variable(v h:ℝ≥0) (Z:Ω→P)

abbrev Future:=CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h

def kernel:Kernel P (Future (E:=E) (ι:=ι) h):=
  condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ

instance kernel_markov:IsMarkovKernel (kernel μ U hc X hd v h Z):=by
  unfold kernel
  infer_instance

include hU hX hBrown in
/-- Instantiation of ordinary package1 on the INTERNALLY RECOGNIZED
canonical conditional Brownian driver. The only construction input is
noise-only; no conditional SPDE equation or restart law is assumed. -/
theorem exists_integral(hvh:v+h≤H) (hZ:Measurable[𝓕 v] Z) (e:HilbertBasis ι ℝ C)
    (hConstruct:∀p,StandardBrownianItoConstruction
      (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=ι) h)
      (kernel μ U hc X hd v h Z p) h e (CanonicalStateDriverFiltration.coordinate h)):
    ∀ᵐp∂μ.map Z,∃J:StandardTerminalIto (C:=C) (E:=ℝ)
      (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=ι) h) (kernel μ U hc X hd v h Z p) h,
      StandardTerminalPastLocality J ∧ StandardHilbertItoLift J ∧
      ∀i (t:ℝ≥0),t≤h→
        (J.integral (StoppedItoInputs.stop _ _ _ t
          (RawCylindricalCoordinates.row _ _ _ (e:ι→C) i)))=ᵐ[kernel μ U hc X hd v h Z p]
            CanonicalStateDriverFiltration.coordinate h i t:=by
  filter_upwards[CanonicalConditionalBrownianLaw.law 𝓕 μ H U hc X hd hU hX hBrown
    v h hvh Z hZ] with p hp
  exact hConstruct p (fun i r=>CanonicalStateDriverFiltration.coordinate_continuous h i r)
    (fun i t=>CanonicalStateDriverFiltration.coordinate_adapted h i t) hp
end SHE.CanonicalConditionalItoConstruction
