module

public import SHE.FiniteComparisonTest
public import SHE.DampedAffineGaussian
public import SHE.ObservationBlockMaps

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FirstGammaAffine
open GaussianIncrement
variable (n : ℕ)

abbrev Space := State ((n+n)+(n+n))

def currentU : Space n→L[ℝ]State n :=
  (ObservationBlockMaps.first n).comp (FiniteComparisonTest.left (n+n))
def currentD : Space n→L[ℝ]State n :=
  (ObservationBlockMaps.second n).comp (FiniteComparisonTest.left (n+n))
def frozenU : Space n→L[ℝ]State n :=
  (ObservationBlockMaps.first n).comp (FiniteComparisonTest.right (n+n))
def pastD : Space n→L[ℝ]State n :=
  (ObservationBlockMaps.second n).comp (FiniteComparisonTest.right (n+n))

def terminalDamping (Λ : ℝ) (target : Fin n→ℝ) : State n→L[ℝ]State n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i=>Real.exp (-Λ*target i) • PiLp.proj 2 (fun _ : Fin n=>ℝ) i))

@[simp] theorem terminalDamping_apply (Λ : ℝ) (target : Fin n→ℝ) (z : State n) (i : Fin n) :
    terminalDamping n Λ target z i=Real.exp (-Λ*target i)*z i := rfl

def baseCurrent (Λ θ : ℝ) (target : Fin n→ℝ) : Space n→L[ℝ]State n :=
  currentU n+θ • (terminalDamping n Λ target).comp (pastD n)

def dynamic : Space n→L[ℝ]State n := currentD n-pastD n

def current (Λ θ : ℝ) (target : Fin n→ℝ) : ℝ→Space n→L[ℝ]State n :=
  DampedAffineGaussian.linear Λ θ (baseCurrent n Λ θ target) (dynamic n)

def currentDerivative (Λ θ : ℝ) : ℝ→Space n→L[ℝ]State n :=
  DampedAffineGaussian.linearDerivative Λ θ (dynamic n)

def reference (Λ θ : ℝ) (target : Fin n→ℝ) : Space n→L[ℝ]State n :=
  frozenU n+θ • (terminalDamping n Λ target).comp (pastD n)

/-- The old rescaled difference is a frozen FINITE coordinate. This is
the corrected future mean, retaining its original target damping. -/
theorem current_apply (Λ θ : ℝ) (target : Fin n→ℝ) {t : ℝ} (ht : 0≤t)
    (z : Space n) (i : Fin n) :
    current n Λ θ target t z i=currentU n z i+θ*Real.exp (-Λ*t)*currentD n z i+
      θ*(Real.exp (-Λ*target i)-Real.exp (-Λ*t))*pastD n z i := by
  simp only [current,DampedAffineGaussian.linear,baseCurrent,dynamic,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
    terminalDamping_apply,ClippedExponential.coefficient,ClippedExponential.damping_eq ht]
  ring

theorem reference_apply (Λ θ : ℝ) (target : Fin n→ℝ) (z : Space n) (i : Fin n) :
    reference n Λ θ target z i=frozenU n z i+θ*Real.exp (-Λ*target i)*pastD n z i := by
  simp only [reference,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,terminalDamping_apply]
  ring

/-- The genuine remaining control drift is retained; no current joint
martingale is substituted for this time-dependent affine current. -/
theorem currentDerivative_apply (Λ θ : ℝ) {t : ℝ} (ht : 0≤t) (z : Space n) (i : Fin n) :
    currentDerivative n Λ θ t z i= -Λ*θ*Real.exp (-Λ*t)*(currentD n z i-pastD n z i) := by
  simp only [currentDerivative,DampedAffineGaussian.linearDerivative,dynamic,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,PiLp.smul_apply,PiLp.sub_apply,
    smul_eq_mul,ClippedExponential.coefficient,ClippedExponential.damping_eq ht]
  ring

end SHE.FirstGammaAffine
