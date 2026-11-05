module

public import SHE.SuppressedGaussianLaw
public import SHE.GaussianShiftedReferenceMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.SuppressedShiftedReference
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCenteredLeafMoments SuppressedGaussianLaw
open scoped BigOperators NNReal
variable {n r : ℕ}

/-- The retained Gaussian covariance need only be dominated by the full
reference variance; the latter may also include pre-window history. -/
theorem even_moment_of_full_variance {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (is : List (Fin r))
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) (i : Fin n)
    (full : ℝ≥0) (hv : covariance is A B i i≤(full:ℝ))
    (a : ℝ→ℝ) (ha : Measurable a) (M H β : ℝ) (hM : ∀ z,|a z|≤M)
    (hH : 0≤H) (hβ : 0≤β) (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (m : Ω×((Fin r→State n)×State n)→ℝ) (hm : Measurable m)
    (referenceMean : ℝ) (p : ℕ) :
    let ν := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun z => |m z-referenceMean|^(((2*p:ℕ):ℝ)*β)) (ρ.prod ν) →
    Integrable (fun z => |a (m z+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
      GaussianProfile.gaussianAverage a referenceMean full|^(2*p)) (ρ.prod ν) ∧
      (∫ z,|a (m z+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
        GaussianProfile.gaussianAverage a referenceMean full|^(2*p) ∂ρ.prod ν) ≤
      (2 : ℝ)^(2*p-1)*(H^(2*p)*
        (∫ z,|m z-referenceMean|^(((2*p:ℕ):ℝ)*β) ∂ρ.prod ν)+
        leafMomentConstant p β*(H*(full:ℝ)^(β/2))^(2*p)) := by
  intro ν hi
  have hv' : (covariance is A B i i).toNNReal≤full := Real.toNNReal_le_iff_le_coe.mpr hv
  have hl := (coordinate_hasLaw is A hA B hB i).fun_comp
    ((measurePreserving_snd (μ:=ρ) (ν:=ν)).hasLaw)
  have hXm : Measurable (fun z : Ω×((Fin r→State n)×State n) =>
      ((∑ j,suppress is z.2.1 j)+z.2.2) i) := by
    simp_rw [suppress_apply]
    fun_prop
  exact GaussianShiftedReferenceMoments.shifted_reference_even_moment (ρ.prod ν)
    _ m hXm hm hl hv' a ha M H β hM hH hβ hholder referenceMean p hi

/-- Actual suppressed old/residual coordinates, combined with arbitrary
outer randomness, retain the full reference baseline. The displaced mean
may depend on every coordinate; its displacement moment stays explicit. -/
theorem even_moment {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (is : List (Fin r))
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) (i : Fin n)
    (a : ℝ→ℝ) (ha : Measurable a) (M H β : ℝ) (hM : ∀ z,|a z|≤M)
    (hH : 0≤H) (hβ : 0≤β) (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (m : Ω×((Fin r→State n)×State n)→ℝ) (hm : Measurable m)
    (referenceMean : ℝ) (p : ℕ) :
    let full := ((∑ j,A j)+B) i i
    let ν := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun z => |m z-referenceMean|^(((2*p:ℕ):ℝ)*β)) (ρ.prod ν) →
    Integrable (fun z => |a (m z+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
      GaussianProfile.gaussianAverage a referenceMean full|^(2*p)) (ρ.prod ν) ∧
      (∫ z,|a (m z+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
        GaussianProfile.gaussianAverage a referenceMean full|^(2*p) ∂ρ.prod ν) ≤
      (2 : ℝ)^(2*p-1)*(H^(2*p)*
        (∫ z,|m z-referenceMean|^(((2*p:ℕ):ℝ)*β) ∂ρ.prod ν)+
        leafMomentConstant p β*(H*full^(β/2))^(2*p)) := by
  intro full ν hi
  have hfull : 0≤full := ((Matrix.posSemidef_sum _ (fun j _ => hA j)).add hB).diag_nonneg
  have hv : (covariance is A B i i).toNNReal≤full.toNNReal :=
    Real.toNNReal_le_toNNReal (coordinate_domination is A hA B i)
  have hl := (coordinate_hasLaw is A hA B hB i).fun_comp
    ((measurePreserving_snd (μ:=ρ) (ν:=ν)).hasLaw)
  have hXm : Measurable (fun z : Ω×((Fin r→State n)×State n) =>
      ((∑ j,suppress is z.2.1 j)+z.2.2) i) := by
    simp_rw [suppress_apply]
    fun_prop
  have hh := GaussianShiftedReferenceMoments.shifted_reference_even_moment (ρ.prod ν)
    _ m hXm hm hl hv a ha M H β hM hH hβ hholder referenceMean p hi
  simpa only [Real.coe_toNNReal _ hfull] using hh

end SHE.SuppressedShiftedReference
