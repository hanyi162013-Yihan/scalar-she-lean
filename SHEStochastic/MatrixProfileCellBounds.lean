module

public import SHEStochastic.MatrixProfileNorms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixProfileCellBounds
open MeasureTheory MatrixProfileHilbert MatrixPhysicalColumnMap MatrixProfileNorms SHE
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- Exact localized Frobenius energy of the actual cell restriction. -/
theorem restriction_energy (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (u : Space d) :
    ‖restriction s hs u‖^2=∫ x in s, ‖u x‖^2 ∂μ := by
  have hn := L2.inner_def (𝕜 := ℝ) (restriction s hs u) (restriction s hs u)
  simp only [real_inner_self_eq_norm_sq] at hn
  rw [hn, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [restriction_ae s hs u] with x hx
  rw [hx]
  by_cases hxs : x∈s <;> simp [hxs]

/-- A normalized interval mass has exactly the Cauchy--Schwarz length
gain needed by the one-`L²`-input vector column estimate. -/
theorem mass_bound (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (u : Space d) :
    MatrixFrobeniusNorm.size (mass d s u) ≤ Real.sqrt ((μ).real s)*‖restriction s hs u‖ := by
  have hu : MemLp u 2 ((μ).restrict s) := (Lp.memLp u).mono_measure Measure.restrict_le_self
  have hh := ProfileL2.integral_mul_normTwo_bound hu.norm
    (memLp_const (1 : ℝ) : MemLp (fun _ : AddCircle (1 : ℝ) => (1 : ℝ)) 2 ((μ).restrict s))
  simp only [mul_one] at hh
  have he : ProfileL2.normTwo ((μ).restrict s) (fun x => ‖u x‖)=‖restriction s hs u‖ := by
    rw [ProfileL2.normTwo, ← restriction_energy s hs u, Real.sqrt_sq (norm_nonneg _)]
  have hOne : ProfileL2.normTwo ((μ).restrict s) (fun _ : AddCircle (1 : ℝ) => (1 : ℝ))=
      Real.sqrt ((μ).real s) := by
    simp [ProfileL2.normTwo, Measure.real]
  calc
    _ = ‖∫ x in s, u x ∂μ‖ := mass_size s u
    _ ≤ ∫ x in s, ‖u x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ |∫ x in s, ‖u x‖ ∂μ| := le_abs_self _
    _ ≤ ProfileL2.normTwo ((μ).restrict s) (fun x => ‖u x‖)*
        ProfileL2.normTwo ((μ).restrict s) (fun _ : AddCircle (1 : ℝ) => (1 : ℝ)) := hh
    _ = _ := by rw [he, hOne, mul_comm]

theorem mass_bounded (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s)
    (u : Space d) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) :
    MatrixFrobeniusNorm.size (mass d s u) ≤ (μ).real s*B := by
  calc
    _ ≤ Real.sqrt ((μ).real s)*‖restriction s hs u‖ := mass_bound s hs u
    _ ≤ Real.sqrt ((μ).real s)*(B*Real.sqrt ((μ).real s)) :=
      mul_le_mul_of_nonneg_left (restriction_bounded s hs u B hB hu) (Real.sqrt_nonneg _)
    _ = _ := by
      calc
        _ = B*(Real.sqrt ((μ).real s))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt measureReal_nonneg]; ring

end SHEStochastic.MatrixProfileCellBounds
