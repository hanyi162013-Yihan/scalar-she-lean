module

public import SHEStochastic.MatrixCanonicalProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixPhysicalProfile
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance MatrixProfileUpdate
  MatrixProfileFixedPoint MatrixCanonicalProfile
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ} (G : Coefficient (Fin n))
local instance : SecondCountableTopology (VectorHeat.Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (VectorHeat.Physical (d := Fin n)) := borel _
local instance : BorelSpace (VectorHeat.Physical (d := Fin n)) := ⟨rfl⟩

/-- One common horizon for profile construction and one-input stability. -/
theorem exists_parameters {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) :
    ∃ P : Parameters G, P.holder=K ∧ P.exponent=β ∧
      MatrixProfileStability.memoryConstant G P.holder P.exponent*
        SHE.ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4) ≤ 1/2 := by
  let C := contractionConstant G K β
  let B := MatrixProfileStability.memoryConstant G K β*SHE.ProfileVolterra.powerConstant ((β-1)/4)
  have hC : 0 ≤ C := contractionConstant_nonneg G hK
  have hB : 0 ≤ B := mul_nonneg (MatrixProfileStability.memoryConstant_nonneg G hK)
    (SHE.ProfileVolterra.powerConstant_pos (by linarith : -1 < (β-1)/4)).le
  obtain ⟨h,hh,hh1,hs⟩ := SHE.ProfileVolterra.exists_absorption_horizon (a := 0)
    (B := max C B/6) (θ := β/4) (by norm_num)
    (div_nonneg (le_max_of_le_left hC) (by norm_num)) (by positivity)
  norm_num [SHE.ProfileVolterra.powerConstant] at hs
  have hc : C*h^(β/4) ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right (le_max_left C B) (Real.rpow_nonneg hh.le _)).trans hs
  have hb : B*h^(β/4) ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right (le_max_right C B) (Real.rpow_nonneg hh.le _)).trans hs
  exact ⟨⟨K,β,h,hK,hβ,hβ1,hh,hh1,hG,hc⟩,rfl,rfl,hb⟩

variable {G} (P : Parameters G)

/-- The canonical coupled profile as an actual input to the infinite
unit-circle matrix Haar construction. The circle rescaling is explicit. -/
def profile (u : VectorHeat.Physical (d := Fin n)) (r : ℝ) : MatrixInfiniteHaar.Profile (Fin n) where
  value x := P.field (u,(r,SHE.CircleNormalization.scale 1 (2*Real.pi) x))
  measurable := P.field_measurable.comp
    (measurable_const.prodMk (measurable_const.prodMk (SHE.CircleNormalization.continuous_scale _ _).measurable))
  bound := ⟨upper G,by unfold upper; positivity⟩
  norm_bound := Filter.Eventually.of_forall fun x => (P.field_mem _).2
  lower := G.lower
  lower_pos := G.lower_pos
  lower_bound := Filter.Eventually.of_forall fun x => (P.field_mem _).1.1
  upper := upper G
  upper_pos := by unfold upper; positivity
  upper_bound := Filter.Eventually.of_forall fun x => (P.field_mem _).1.2

theorem profile_measurable :
    Measurable (fun p : (VectorHeat.Physical (d := Fin n) × ℝ) × AddCircle (1 : ℝ) =>
      (profile P p.1.1 p.1.2).value p.2) := by
  have hp : Measurable (fun p : (VectorHeat.Physical (d := Fin n) × ℝ) × AddCircle (1 : ℝ) =>
      (p.1.1,(p.1.2,SHE.CircleNormalization.scale 1 (2*Real.pi) p.2))) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
      ((SHE.CircleNormalization.continuous_scale _ _).measurable.comp measurable_snd))
  exact P.field_measurable.comp hp

end SHEStochastic.MatrixPhysicalProfile
