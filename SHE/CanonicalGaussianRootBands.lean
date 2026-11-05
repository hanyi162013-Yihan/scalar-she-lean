module
public import SHE.ScalarHeatRootBands
public import SHE.ScalarApproximationDiscrepancy
public import SHE.SmoothComparisonParameters
public import SHE.RemainderBandSpans
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.CanonicalGaussianRootBands
open Set MeasureTheory SmoothCylinders UniformSmooth WordRecursion
open scoped Topology
variable {X:Type}[MeasurableSpace X]
variable (D:SmoothApproximation.ScalarData)

def test(n:ℕ)(ψ:X→ℝ)(j:ℕ):X→State 1→ℝ:=
  ScalarHeatRootBands.test (D.smoothCoefficient n) ψ j

def amplitude(W:ℝ)(depth:ℕ):ℝ:=
  W*ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta depth

theorem amplitude_nonneg {W:ℝ}(hW:0≤W)(depth:ℕ):0≤amplitude D W depth:=
  mul_nonneg hW (ScalarHeatBandBernstein.amplitude_nonneg D.holderConstant_nonneg depth)

theorem uniform(n:ℕ)(ψ:X→ℝ){W:ℝ}(hW:0≤W)(hψ:∀x,|ψ x|≤W)(j:ℕ):
    UniformBoundedSmooth (test D n ψ j):=
  ScalarHeatRootBands.test_uniform (D.smooth_boundedSmooth n)
    (ScalarApproximationDiscrepancy.smooth_abs_bound D n) ψ hW hψ j

theorem measurable(n:ℕ)(ψ:X→ℝ)(hψ:Measurable ψ)(j:ℕ):
    Measurable (fun z:X×State 1=>test D n ψ j z.1 z.2):=
  ScalarHeatRootBands.test_measurable (D.smooth_boundedSmooth n)
    (ScalarApproximationDiscrepancy.smooth_abs_bound D n) ψ hψ j

/-- One amplitude is fixed before BOTH the approximation index and the
Gaussian frequency; no derivative of the smooth companion enters it. -/
theorem jets(n:ℕ)(ψ:X→ℝ){W:ℝ}(hW:0≤W)(hψ:∀x,|ψ x|≤W)
    (depth j:ℕ)(x:X)(l:ℕ)(hl:l≤depth)(z:State 1):
    ‖iteratedFDeriv ℝ l (test D n ψ j x) z‖≤
      (amplitude D W depth*((2:ℝ)^j)^(-D.beta))*((2:ℝ)^j)^l:=
  ScalarHeatRootBands.test_jets (D.smooth_boundedSmooth n)
    (ScalarApproximationDiscrepancy.smooth_abs_bound D n) D.holderConstant_nonneg
    D.beta_pos.le D.beta_le_one (D.smooth_holder n) ψ hW hψ depth j x l hl z

theorem root_cutoff(n:ℕ)(ψ:X→ℝ)(J:ℕ)(x:X)(z:State 1):
    (∑j∈Finset.range (J+1),test D n ψ j x z)=
      ψ x*ScalarHeatBands.smooth (D.smoothCoefficient n) J (z 0):=
  ScalarHeatRootBands.rootSum_eq _ _ _ _ _

theorem cutoff_error(n:ℕ)(ψ:X→ℝ){W:ℝ}(hW:0≤W)(hψ:∀x,|ψ x|≤W)
    (J:ℕ)(x:X)(z:State 1):
    |(∑j∈Finset.range (J+1),test D n ψ j x z)-ψ x*D.smoothCoefficient n (z 0)|≤
      W*D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta*CompactMollifier.radius J^D.beta:=
  ScalarHeatRootBands.cutoff_error (D.smooth_boundedSmooth n)
    (ScalarApproximationDiscrepancy.smooth_abs_bound D n) D.holderConstant_nonneg D.beta_pos.le
    (D.smooth_holder n) ψ hW hψ J x z

/-- All finitely many actual analytic window restrictions are met by
one root-frequency cutoff, chosen independently of smoothing. -/
theorem windows (N:ℕ)(c:Fin N→ℝ)(hc:∀i,0<c i):
    ∃J:ℕ,∀j,J≤j→∀i,(RemainderBandSpans.span D.beta j:ℝ)≤c i:=by
  have hall:∀ᶠj:ℕ in Filter.atTop,∀i,(RemainderBandSpans.span D.beta j:ℝ)≤c i:=by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨J,hJ⟩:=RemainderBandSpans.eventually_small D.beta_pos (hc i)
    exact Filter.eventually_atTop.mpr ⟨J,hJ⟩
  exact Filter.eventually_atTop.mp hall
end SHE.CanonicalGaussianRootBands
