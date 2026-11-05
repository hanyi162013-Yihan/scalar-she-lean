module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.SquareSummableColumns
open scoped ENNReal

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def normSequence (u : I → E) (hu : Summable (fun i => ‖u i‖^2)) : lp (fun _ : I => ℂ) 2 :=
  ⟨fun i => (‖u i‖:ℂ), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hu)⟩

theorem series_summable (u : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (a : lp (fun _ : I => ℂ) 2) : Summable (fun i => a i • u i) := by
  have hh : (2:ENNReal).toReal.HolderConjugate (2:ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  apply Summable.of_norm_bounded (lp.summable_mul hh a (normSequence u hu))
  intro i
  change ‖a i • u i‖ ≤ ‖a i‖*‖(‖u i‖:ℂ)‖
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact le_rfl

omit [CompleteSpace E] in
theorem series_norm_bound (u : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (a : lp (fun _ : I => ℂ) 2) :
    ‖∑' i, a i • u i‖ ≤ ‖normSequence u hu‖*‖a‖ := by
  have hh : (2:ENNReal).toReal.HolderConjugate (2:ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := lp.tsum_mul_le_mul_norm hh a (normSequence u hu)
  calc
    _ ≤ ∑' i, ‖a i‖*‖(normSequence u hu) i‖ :=
      tsum_of_norm_bounded h.1.hasSum (fun i => by
        change ‖a i • u i‖ ≤ ‖a i‖*‖(‖u i‖:ℂ)‖
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] )
    _ ≤ ‖a‖*‖normSequence u hu‖ := h.2
    _ = _ := mul_comm _ _

/-- A square-summable family of genuine Hilbert-space columns defines
a bounded operator on all of ℓ², by an absolutely convergent series. -/
def linearMap (u : I → E) (hu : Summable (fun i => ‖u i‖^2)) :
    lp (fun _ : I => ℂ) 2 →ₗ[ℂ] E where
  toFun a := ∑' i, a i • u i
  map_add' a b := by
    simpa only [lp.coeFn_add,Pi.add_apply,add_smul] using
      (series_summable u hu a).tsum_add (series_summable u hu b)
  map_smul' c a := by
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,← smul_smul]
    exact Summable.tsum_const_smul c (series_summable u hu a)

def operator (u : I → E) (hu : Summable (fun i => ‖u i‖^2)) :
    lp (fun _ : I => ℂ) 2 →L[ℂ] E :=
  (linearMap u hu).mkContinuous ‖normSequence u hu‖ (series_norm_bound u hu)

theorem operator_single [DecidableEq I] (u : I → E) (hu : Summable (fun i => ‖u i‖^2)) (i : I) :
    operator u hu (lp.single (E:=fun _ : I => ℂ) 2 i (1:ℂ)) = u i := by
  change (∑' j, (lp.single (E:=fun _ : I => ℂ) 2 i (1:ℂ)) j • u j)=u i
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply,hj]

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem normSequence_norm_sq (u : I → E) (hu : Summable (fun i => ‖u i‖^2)) :
    ‖normSequence u hu‖^2 = ∑' i, ‖u i‖^2 := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) (normSequence u hu)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,normSequence,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hh

theorem operator_norm_sq_le (u : I → E) (hu : Summable (fun i => ‖u i‖^2)) :
    ‖operator u hu‖^2 ≤ ∑' i, ‖u i‖^2 := by
  have hnorm : ‖operator u hu‖ ≤ ‖normSequence u hu‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (series_norm_bound u hu)
  rw [← normSequence_norm_sq u hu]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end SHE.SquareSummableColumns
