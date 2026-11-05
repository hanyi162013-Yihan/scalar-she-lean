module

public import SHE.OmittedTimeFactor
public import SHE.FiniteMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.BaselineAssignmentScale
open Set MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianAssignmentBlocks PhysicalChainArrays CoveredControlledLaw GaussianCoordinates ProjectedUncutWord
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

abbrev Index (k : ℕ) := Fin k×Fin (assignments (m:=k+1) (List.finRange k)).length

def choices (k : ℕ) (i : Index k) : List (Fin k×Fin (k+1)) :=
  (assignments (m:=k+1) (List.finRange k)).get i.2

def scale (L : Level R X n) (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (p : History X k) (A0 ν : ℝ) (db : Fin k→ℝ) (i : Index k) : ℝ :=
  if block (choices k i) i.1.succ=[] then
    |db i.1| *|OmittedTimeFactor.factor L P k p (choices k i) i.1 A0 ν| else 0

def total (L : Level R X n) (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (p : History X k) (A0 ν : ℝ) (db : Fin k→ℝ) : ℝ := ∑ i : Index k,scale L P k p A0 ν db i

theorem scale_nonneg (L : Level R X n) (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (p : History X k) (A0 ν : ℝ) (db : Fin k→ℝ) (i : Index k) : 0≤scale L P k p A0 ν db i := by
  unfold scale
  split_ifs <;> positivity

theorem total_nonneg (L : Level R X n) (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (p : History X k) (A0 ν : ℝ) (db : Fin k→ℝ) : 0≤total L P k p A0 ν db :=
  Finset.sum_nonneg (fun i _=>scale_nonneg L P k p A0 ν db i)

theorem scale_le_total (L : Level R X n) (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (p : History X k) (A0 ν : ℝ) (db : Fin k→ℝ) (i : Index k) :
    scale L P k p A0 ν db i≤total L P k p A0 ν db := by
  exact Finset.single_le_sum (fun j _=>scale_nonneg L P k p A0 ν db j) (Finset.mem_univ i)

theorem sum_eq (k : ℕ) (f : Fin k→List (Fin k×Fin (k+1))→ℝ) :
    (∑ i : Index k,f i.1 (choices k i))=
      ∑ j : Fin k,((assignments (m:=k+1) (List.finRange k)).map (f j)).sum := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [choices] using (FiniteAssignmentMoments.map_sum_eq_fin
    (assignments (m:=k+1) (List.finRange k)) (f j)).symm

/-- Summing deleted-leaf profile gains restores the ORIGINAL full word
degree, including Holder constant zero. No lower-order degree replaces it. -/
theorem restored_total_gain (L : Level R X n) (P : CanonicalCovariance.ProfileParameters)
    (d : CircleL2) (k : ℕ) (p : History X k) (q A0 ν : ℝ) {gap : ℝ}
    (hgap : 0<gap) (hga : ∀ j : Fin k,gap≤targets L k p (leafIndex k (fun i=>i) j)) :
    total L P k p A0 ν (fun j=>ControlledScoreRates.sharpConstant P d*
      (targets L k p (leafIndex k (fun i=>i) j))^((P.exponent-1)/4))≤
      (Fintype.card (Index k):ℝ)*BaselineOriginalGain.unitSharp P d*
        SharpWordTimeScale.total L P k p q A0 ν*gap^(-(1/4:ℝ)) := by
  have hpoint (i : Index k) : scale L P k p A0 ν (fun j=>ControlledScoreRates.sharpConstant P d*
      (targets L k p (leafIndex k (fun i=>i) j))^((P.exponent-1)/4)) i≤
      BaselineOriginalGain.unitSharp P d*SharpWordTimeScale.total L P k p q A0 ν*gap^(-(1/4:ℝ)) := by
    unfold scale
    split_ifs with hb
    · have hs : 0≤ControlledScoreRates.sharpConstant P d*
        (targets L k p (leafIndex k (fun i=>i) i.1))^((P.exponent-1)/4) :=
        mul_nonneg (ControlledScoreRates.sharpConstant_nonneg P d) (rpow_nonneg (hgap.le.trans (hga i.1)) _)
      rw [abs_of_nonneg hs]
      have hh := OmittedTimeFactor.restored_gain L P d k p (choices k i) i.1 hb q A0 ν hgap (hga i.1)
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (SharpWordTimeScale.factor_le_total L P k p q A0 ν (choices k i)
          (List.get_mem _ _)) (BaselineOriginalGain.unitSharp_nonneg P d)) (rpow_nonneg hgap.le _))
    · exact mul_nonneg (mul_nonneg (BaselineOriginalGain.unitSharp_nonneg P d)
        (SharpWordTimeScale.total_nonneg L P k p q A0 ν)) (rpow_nonneg hgap.le _)
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hpoint i)
  simpa only [total,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh

end SHE.BaselineAssignmentScale
