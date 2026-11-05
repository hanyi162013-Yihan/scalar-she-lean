module

public import SHE.GaussianReferenceLeafMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianShiftedReferenceMoments
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianCenteredLeafMoments
  GaussianReferenceLeafMoments RoughLeafOffsetMoments
open scoped NNReal

/-- A current/future mean need not equal the profile mean. Its genuine
random displacement is retained as a separate moment, even when it is
dependent on the Gaussian increment. The full reference baseline stays
fixed and the reduced Gaussian variance is allowed to be smaller. -/
theorem shifted_reference_even_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X m : Ω → ℝ)
    (hXm : Measurable X) (hm : Measurable m) {v full : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) (hv : v ≤ full)
    (a : ℝ → ℝ) (ha : Measurable a) (M H β : ℝ) (hM : ∀ z, |a z| ≤ M)
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β)
    (referenceMean : ℝ) (p : ℕ)
    (hi : Integrable (fun ω => |m ω-referenceMean|^(((2*p : ℕ) : ℝ)*β)) μ) :
    Integrable (fun ω => |a (m ω+X ω)-GaussianProfile.gaussianAverage a referenceMean full|^(2*p)) μ ∧
      (∫ ω, |a (m ω+X ω)-GaussianProfile.gaussianAverage a referenceMean full|^(2*p) ∂μ) ≤
        (2 : ℝ)^(2*p-1)*
          (H^(2*p)*(∫ ω, |m ω-referenceMean|^(((2*p : ℕ) : ℝ)*β) ∂μ) +
            leafMomentConstant p β*(H*(full : ℝ)^(β/2))^(2*p)) := by
  have hbase := reference_baseline_even_moment μ X hXm hX hv a ha M H β hM hH hβ hholder referenceMean p
  have hh := offset_even_moment μ a ha (fun ω => referenceMean+X ω)
    (fun ω => m ω-referenceMean) (fun _ => GaussianProfile.gaussianAverage a referenceMean full)
    (measurable_const.add hXm) (hm.sub_const _) measurable_const hH hβ hholder p hi hbase.1
  have he (ω : Ω) : referenceMean+X ω+(m ω-referenceMean) = m ω+X ω := by ring
  simp only [he] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hbase.2) (by positivity)

end SHE.GaussianShiftedReferenceMoments
