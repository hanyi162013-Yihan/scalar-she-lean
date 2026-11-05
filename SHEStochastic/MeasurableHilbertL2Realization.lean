module

public import SHE.MeasurableL2Field

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MeasurableHilbertL2Realization
open MeasureTheory SHE
open scoped Topology

variable {P X E : Type*} [MeasurableSpace P] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure X} [SFinite ν]
  [SecondCountableTopology (Lp E 2 ν)]
  [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]

/-- Joint measurable representatives give Borel maps into the actual
separable vector `L²` space. This reuses the scalar metric criterion,
and requires no uniform bound across the parameter space. -/
theorem measurable (F : P × X → E) (hF : Measurable F) (K : P → Lp E 2 ν)
    (hK : ∀ p, ⇑(K p) =ᵐ[ν] fun x => F (p,x)) : Measurable K := by
  apply MeasurableL2Field.measurable_of_dist
  intro g
  have hm : Measurable (fun p : P × X => ‖F p-g p.2‖^2) :=
    (hF.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).norm.pow_const (2 : ℕ)
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable.sqrt
  have he (p : P) : dist (K p) g=Real.sqrt (∫ x, ‖F (p,x)-g x‖^2 ∂ν) := by
    have hsq : ‖K p-g‖^2=∫ x, ‖F (p,x)-g x‖^2 ∂ν := by
      calc
        _ = ∫ x, ‖(K p-g) x‖^2 ∂ν := by
          simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) (K p-g) (K p-g))
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (K p) g, hK p] with x hs hk
          rw [hs, Pi.sub_apply, hk]
    rw [dist_eq_norm, ← hsq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [← he] using hi

end SHEStochastic.MeasurableHilbertL2Realization
