module

public import SHE.ScalarApproximationDiscrepancy
public import SHE.ControlledSmoothLimit
public import SHE.ApproximationDiagonal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ScalarApproximationDiagonal
open Filter MeasureTheory SmoothApproximation ScalarData ScalarApproximationDiscrepancy
open scoped Topology
local instance scalarApproximationDiagonal_realSigma : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance scalarApproximationDiagonal_realBorel : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
variable (D : ScalarData)

/-- The deterministic diagonal is attached to the ACTUAL two-state
nonlinear fields and original squared-diffusion roots. No continuity of
an independently postulated rough recursive word is required here. -/
theorem actual_coefficient_diagonal (damp : ℕ→ℝ) (hdamp : ∀k,0<damp k) (A : ℝ)
    {T : ℝ} (hT : 0<T) (hT1 : T≤1)
    (hsmall : GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2) :
    ∃ index : ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀k, SmoothReferenceLimit.error D (index k)<(damp k)^(-A) ∧
        (∀x y,|((D.coefficient x)^2-(D.coefficient y)^2)-
          (D.smoothCoefficient (index k) x-D.smoothCoefficient (index k) y)|≤(damp k)^(-A)) ∧
        (∀U V:DyadicApproximation.RealL2,
          ‖differenceError D (index k) U V‖≤(damp k)^(-A)) ∧
        (∀Λ u d θ z,
          |ControlledProfile.profile (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall (index k))
              Λ u d (θ,z)-
            ControlledProfile.profile (ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall)
              Λ u d (θ,z)|≤(damp k)^(-A)) := by
  obtain ⟨index,hi,ht,herr⟩ := SHE.common_approximation_diagonal_tendsto
    (Finset.univ : Finset Unit) (fun (_:Unit) n (_:ℝ)=>SmoothReferenceLimit.error D n)
    damp (fun k=>(damp k)^(-A)) (fun k=>Real.rpow_pos_of_pos (hdamp k) _)
    (fun _ _ _=>SmoothReferenceLimit.error_tendsto D)
  refine ⟨index,hi,ht,?_⟩
  intro k
  have he : SmoothReferenceLimit.error D (index k)<(damp k)^(-A) := by
    simpa only [abs_of_nonneg (SmoothReferenceLimit.error_nonneg D (index k))] using herr k () (by simp)
  refine ⟨he,fun x y=>(original_difference_error D (index k) x y).trans he.le,
    fun U V=>(difference_field_error D (index k) U V).trans he.le,?_⟩
  intro Λ u d θ z
  exact (ControlledSmoothLimit.total_profile_error D hT hT1 hsmall (index k) Λ u d θ z).trans he.le

/-- Genuine finite-measure sample/time energy of the original nonlinear
discrepancy. In particular an unsquared error `Λ⁻²` costs at most `Λ⁻⁴`
in the actual squared field energy. -/
theorem actual_energy_of_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (n : ℕ) (U V : X→DyadicApproximation.RealL2)
    (hU : Measurable U) (hV : Measurable V) {L A : ℝ} (hL : 0<L)
    (he : SmoothReferenceLimit.error D n≤L^(-A)) :
    Integrable (fun x=>‖differenceError D n (U x) (V x)‖^2) ν ∧
      (∫x,‖differenceError D n (U x) (V x)‖^2 ∂ν)≤L^(-2*A)*(ν Set.univ).toReal := by
  obtain ⟨hi,hb⟩ := differenceError_energy D ν n U V hU hV
  refine ⟨hi,hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  calc
    SmoothReferenceLimit.error D n^2≤(L^(-A))^2 :=
      pow_le_pow_left₀ (SmoothReferenceLimit.error_nonneg D n) he 2
    _=L^(-2*A) := by rw [←Real.rpow_mul_natCast hL.le]; congr 1; norm_num; ring

end SHE.ScalarApproximationDiagonal
