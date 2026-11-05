module

public import SHE.PastBaselineTime
public import SHE.PastMeanDampedTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastBaselineTime
open Set MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain PastMeanTimeFactors
variable {R : ReferenceData} (L : Level R HeatCircle 1)

theorem density_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q A0 ν : ℝ) : Measurable (restoredDensity L P ell C k q A0 ν) :=
  (totalIntegrand_measurable L P ell C k q (3/4:ℝ) A0 ν).const_mul _

theorem density_nonneg (P : CanonicalCovariance.ProfileParameters) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) :
    0≤restoredDensity L P ell C k q A0 ν p :=
  mul_nonneg (BaselineOriginalGain.unitCoefficient_nonneg P)
    (totalIntegrand_nonneg L P hell C hC k q (3/4:ℝ) A0 ν p)

theorem density_of_active (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) (hp : StrictHistory L k p)
    (hq : q<(carrier L k).terminal p) :
    restoredDensity L P ell C k q A0 ν p=
      timeWeight L ell C k p*BaselineOriginalGain.unitCoefficient P*
        PastWordTimeFields.total L P k p A0 ν*((carrier L k).terminal p-q)^(-(1/4:ℝ)) := by
  have hact : StrictHistory L k p ∧ q<(carrier L k).terminal p:=⟨hp,hq⟩
  simp only [restoredDensity,totalIntegrand,ite_eq_left hact]
  norm_num
  ring

end SHE.PastBaselineTime
