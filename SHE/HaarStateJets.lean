module

public import SHE.HaarMassJets
public import SHE.HaarCellEnergy
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE
open Set Finset
open scoped ContDiff

def positiveMasses : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2}

theorem isOpen_positiveMasses : IsOpen positiveMasses :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

theorem contDiffOn_massCoefficient (b : Bool) : ContDiffOn ℝ ∞ (massCoefficient b) positiveMasses :=
  fun z hz => (contDiffAt_massCoefficient b z hz ∞).contDiffWithinAt

abbrev ColumnState (E : Type*) := (ℝ × ℝ) × (E × E)

section State
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def stateMassProjection : ColumnState E →L[ℝ] ℝ × ℝ := ContinuousLinearMap.fst ℝ _ _

def stateChildProjection (b : Bool) : ColumnState E →L[ℝ] E :=
  (if b then ContinuousLinearMap.snd ℝ E E else ContinuousLinearMap.fst ℝ E E).comp
    (ContinuousLinearMap.snd ℝ _ _)

def statePositive : Set (ColumnState E) := stateMassProjection ⁻¹' positiveMasses

theorem isOpen_statePositive : IsOpen (statePositive (E := E)) :=
  isOpen_positiveMasses.preimage stateMassProjection.continuous

def stateColumn (z : ColumnState E) : E :=
  massCoefficient false z.1 • z.2.1 + massCoefficient true z.1 • z.2.2

theorem contDiffAt_stateCoefficient (b : Bool) (z : ColumnState E) (hz : z ∈ statePositive) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (fun x : ColumnState E => massCoefficient b x.1) z :=
  (contDiffAt_massCoefficient b z.1 hz k).comp z contDiffAt_fst

theorem contDiffAt_stateColumn (z : ColumnState E) (hz : z ∈ statePositive) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k stateColumn z := by
  exact ((contDiffAt_stateCoefficient false z hz k).smul (stateChildProjection false).contDiff.contDiffAt).add
    ((contDiffAt_stateCoefficient true z hz k).smul (stateChildProjection true).contDiff.contDiffAt)

theorem stateCoefficient_jet_bound (m U : ℝ) (hm : 0 < m) (j : ℕ) (b : Bool) (z : ColumnState E)
    (hz : z.1 ∈ massRectangle m U) :
    ‖iteratedFDeriv ℝ j (fun x : ColumnState E => massCoefficient b x.1) z‖ ≤ massJetBound m U hm j := by
  have hp : z ∈ statePositive := ⟨hm.trans_le hz.1.1, hm.trans_le hz.1.2⟩
  have he := (stateMassProjection (E := E)).iteratedFDerivWithin_comp_right
    (contDiffOn_massCoefficient b) isOpen_positiveMasses.uniqueDiffOn
    isOpen_statePositive.uniqueDiffOn hp (i := j) (by simp)
  change iteratedFDerivWithin ℝ j (fun x : ColumnState E => massCoefficient b x.1) statePositive z =
    (iteratedFDerivWithin ℝ j (massCoefficient b) positiveMasses z.1).compContinuousLinearMap
      (fun _ => stateMassProjection) at he
  rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      (contDiffAt_stateCoefficient b z hp j) hp,
    iteratedFDerivWithin_eq_iteratedFDeriv (s := positiveMasses) isOpen_positiveMasses.uniqueDiffOn
      (contDiffAt_massCoefficient b z.1 hp j) hp] at he
  rw [he]
  have hn := (iteratedFDeriv ℝ j (massCoefficient b) z.1).norm_compContinuousLinearMap_le
    (fun _ => stateMassProjection (E := E))
  have hP : ‖stateMassProjection (E := E)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  have hprod : (∏ _ : Fin j, ‖stateMassProjection (E := E)‖) ≤ 1 :=
    prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hP)
  exact hn.trans ((mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans
    (by simpa only [mul_one] using massJetBound_le m U hm j b z.1 hz))

theorem linear_jet_bound {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : D →L[ℝ] F) (x : D) (j : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hL : ‖L‖ ≤ B) (hx : ‖L x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j L x‖ ≤ B := by
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hx
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ => L := funext (fun y => L.fderiv)
    rw [he]
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hL
    | succ j => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hB

theorem stateChildProjection_norm (b : Bool) : ‖stateChildProjection (E := E) b‖ ≤ 1 := by
  unfold stateChildProjection
  cases b <;> exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (by first | exact ContinuousLinearMap.norm_fst_le _ _ _ | exact ContinuousLinearMap.norm_snd_le _ _ _)
      (ContinuousLinearMap.norm_snd_le _ _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

def stateJetBound (m U : ℝ) (hm : 0 < m) (j : ℕ) : ℝ :=
  2 * ∑ i ∈ range (j + 1), (j.choose i : ℝ) * massJetBound m U hm i * max U 1

theorem stateJetBound_nonneg (m U : ℝ) (hm : 0 < m) (j : ℕ) : 0 ≤ stateJetBound m U hm j := by
  unfold stateJetBound
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (massJetBound_pos m U hm i).le)
    (zero_le_one.trans (le_max_right _ _))

theorem stateColumn_jet_bound (m U : ℝ) (hm : 0 < m) (j : ℕ) (z : ColumnState E)
    (hz : z.1 ∈ massRectangle m U) (hv : ‖z.2‖ ≤ U) :
    ‖iteratedFDeriv ℝ j stateColumn z‖ ≤ stateJetBound m U hm j := by
  have hp : z ∈ statePositive := ⟨hm.trans_le hz.1.1, hm.trans_le hz.1.2⟩
  have hcoef (b : Bool) : ContDiffOn ℝ ∞ (fun x : ColumnState E => massCoefficient b x.1) statePositive :=
    fun x hx => (contDiffAt_stateCoefficient b x hx ∞).contDiffWithinAt
  have hside (b : Bool) : ‖iteratedFDeriv ℝ j (fun x : ColumnState E =>
      massCoefficient b x.1 • stateChildProjection b x) z‖ ≤
      ∑ i ∈ range (j + 1), (j.choose i : ℝ) * massJetBound m U hm i * max U 1 := by
    have hs := norm_iteratedFDerivWithin_smul_le (hcoef b) (stateChildProjection b).contDiff.contDiffOn
      isOpen_statePositive.uniqueDiffOn hp (n := j) (by simp : (j : WithTop ℕ∞) ≤ ∞)
    have hsm := ((contDiffAt_stateCoefficient b z hp j).smul (stateChildProjection b).contDiff.contDiffAt)
    change ContDiffAt ℝ j (fun x : ColumnState E => massCoefficient b x.1 • stateChildProjection b x) z at hsm
    rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      hsm hp] at hs
    apply hs.trans
    apply sum_le_sum
    intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
        (contDiffAt_stateCoefficient b z hp i) hp,
      iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
        (stateChildProjection b).contDiff.contDiffAt hp]
    have hvb : ‖stateChildProjection b z‖ ≤ max U 1 := by
      cases b
      · exact ((norm_fst_le z.2).trans hv).trans (le_max_left _ _)
      · exact ((norm_snd_le z.2).trans hv).trans (le_max_left _ _)
    have hjet := linear_jet_bound (stateChildProjection b) z (j-i) (max U 1)
      (zero_le_one.trans (le_max_right _ _))
      ((stateChildProjection_norm b).trans (le_max_right _ _)) hvb
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (stateCoefficient_jet_bound m U hm i b z hz) (by positivity)) hjet
      (norm_nonneg _) (mul_nonneg (by positivity) (massJetBound_pos m U hm i).le)
  have he : stateColumn (E := E) = (fun x => massCoefficient false x.1 • stateChildProjection false x) +
      (fun x => massCoefficient true x.1 • stateChildProjection true x) := rfl
  have h0 := ((contDiffAt_stateCoefficient false z hp j).smul (stateChildProjection false).contDiff.contDiffAt)
  have h1 := ((contDiffAt_stateCoefficient true z hp j).smul (stateChildProjection true).contDiff.contDiffAt)
  change ContDiffAt ℝ j (fun x : ColumnState E => massCoefficient false x.1 • stateChildProjection false x) z at h0
  change ContDiffAt ℝ j (fun x : ColumnState E => massCoefficient true x.1 • stateChildProjection true x) z at h1
  rw [he, iteratedFDeriv_add_apply h0 h1]
  exact (norm_add_le _ _).trans ((add_le_add (hside false) (hside true)).trans_eq (by unfold stateJetBound; ring))

end State
end SHE
