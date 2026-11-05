module

public import SHE.FirstGammaAffine
public import SHE.DampedEndpointAffine
public import SHE.SmoothTimeTestSubtraction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.FirstGammaGaussianTest
open Set MeasureTheory GaussianIncrement SmoothCylinders GaussianAffineFields
variable {n : ℕ}

def currentValue (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (target : Fin n→ℝ) :=
  value W.path F (FirstGammaAffine.current n Λ θ target) (fun _=>0)

def currentDerivative (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (target : Fin n→ℝ) :=
  GaussianEndpointAffine.derivative W F (FirstGammaAffine.current n Λ θ target)
    (FirstGammaAffine.currentDerivative n Λ θ) (fun _=>0) (fun _=>0)

def referenceValue (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (target : Fin n→ℝ) :=
  value W.path F (fun _=>FirstGammaAffine.reference n Λ θ target) (fun _=>0)

def referenceDerivative (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (target : Fin n→ℝ) :=
  GaussianEndpointAffine.derivative W F (fun _=>FirstGammaAffine.reference n Λ θ target)
    (fun _=>0) (fun _=>0) (fun _=>0)

def test (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (target : Fin n→ℝ) (t : ℝ) (z : FirstGammaAffine.Space n) : ℝ :=
  currentValue W F Λ θ target t z-referenceValue W F Λ θ target t z

def testDerivative (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (target : Fin n→ℝ) (t : ℝ) (z : FirstGammaAffine.Space n) : ℝ :=
  currentDerivative W F Λ θ target t z-referenceDerivative W F Λ θ target t z

/-- The true corrected current/frozen-reference comparison is an actual
localized finite-dimensional Itô test, through zero terminal reserve.
Its current time derivative retains the control drift. -/
theorem smoothTimeTest (W : CovarianceEndpoint.EndpointWindow n) (hleft : 0≤W.left)
    {F : State n→ℝ} (hF : BoundedSmooth F) {Λ : ℝ} (hΛ : 0≤Λ)
    (θ : ℝ) (target : Fin n→ℝ) :
    LocalizedItoTest.SmoothTimeTest W.left W.right (test W F Λ θ target) (testDerivative W F Λ θ target) := by
  have hc:=DampedEndpointAffine.smoothTimeTest W hleft hF hΛ θ
    (FirstGammaAffine.baseCurrent n Λ θ target) (FirstGammaAffine.dynamic n) 0 0
  have hr:=DampedEndpointAffine.smoothTimeTest W hleft hF hΛ θ
    (FirstGammaAffine.reference n Λ θ target) 0 0 0
  have hs : DampedAffineGaussian.shift Λ θ (0:State n) 0=(fun _=>0) := by
    funext t
    simp [DampedAffineGaussian.shift]
  have hds : DampedAffineGaussian.shiftDerivative Λ θ (0:State n)=(fun _=>0) := by
    funext t
    simp [DampedAffineGaussian.shiftDerivative]
  have hl : DampedAffineGaussian.linear Λ θ (FirstGammaAffine.reference n Λ θ target) 0=
      (fun _=>FirstGammaAffine.reference n Λ θ target) := by
    funext t
    change FirstGammaAffine.reference n Λ θ target+_ • (0:FirstGammaAffine.Space n→L[ℝ]State n)=_
    ext z i
    simp only [add_apply,smul_apply,zero_apply,PiLp.add_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero,add_zero]
  have hdl : DampedAffineGaussian.linearDerivative Λ θ (0:FirstGammaAffine.Space n→L[ℝ]State n)=(fun _=>0) := by
    funext t
    change _ • (0:FirstGammaAffine.Space n→L[ℝ]State n)=0
    ext z i
    simp only [smul_apply,zero_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero]
  rw [hs,hds] at hc
  rw [hs,hds,hl,hdl] at hr
  exact hc.sub hr

end SHE.FirstGammaGaussianTest
