module

public import SHE.RowSpatialHistoryMoments
public import SHE.QuarterKernelTimes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.HistoryQuarterFields
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry HistoryProductMeasure ActualMeanKernel
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- This is a Borel function on the actual history, chosen before any
history exceptional sets are disintegrated. -/
def rowTime (k : ℕ) (q : ℝ) (p : History P k) : ℝ :=
  q+max ((carrier L k).terminal p-q) 0/4

theorem rowTime_measurable (k : ℕ) (q : ℝ) : Measurable (rowTime L k q) :=
  measurable_const.add (((((carrier L k).terminal_measurable.sub_const q).max measurable_const)).div_const 4)

theorem rowTime_replaceSpace (k : ℕ) (q : ℝ) (p : History P k) (x : Fin k → HeatCircle) :
    rowTime L k q (replaceSpace k p x)=rowTime L k q p := by
  simp only [rowTime,replaceSpace_terminal]

theorem le_rowTime (k : ℕ) (q : ℝ) (p : History P k) : q ≤ rowTime L k q p := by
  unfold rowTime
  linarith [le_max_right ((carrier L k).terminal p-q) 0]

theorem rowTime_lt_iff (k : ℕ) (q : ℝ) (p : History P k) :
    rowTime L k q p < (carrier L k).terminal p ↔ q < (carrier L k).terminal p := by
  constructor
  · exact fun h => (le_rowTime L k q p).trans_lt h
  · intro hq
    simp only [rowTime,max_eq_left (sub_pos.mpr hq).le]
    linarith

theorem rowTime_separated (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ) (q : ℝ)
    (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle) :
    rowTime L k q (separated k (p,t,x))=quarterRowTime (R:=R) T k q t := by
  simp only [rowTime,terminal_separated L T hT,quarterRowTime,quarterGap]

/-- The actual fresh score factor multiplied by an arbitrary preserved
old root/rough time sum. The inverse gap remains a displayed time factor. -/
def freshAmplitude (k : ℕ) (q Cf ell : ℝ) (D : History P k → ℝ) (p : History P k) : ℝ :=
  Real.sqrt (Cf/(ell*((carrier L k).terminal p-rowTime L k q p)))*D p

theorem freshAmplitude_measurable (k : ℕ) (q Cf ell : ℝ)
    (D : History P k → ℝ) (hD : Measurable D) :
    Measurable (freshAmplitude L k q Cf ell D) :=
  (Real.continuous_sqrt.measurable.comp (measurable_const.div
    (((carrier L k).terminal_measurable.sub (rowTime_measurable L k q)).const_mul ell))).mul hD

theorem freshAmplitude_nonneg (k : ℕ) (q Cf ell : ℝ)
    (D : History P k → ℝ) (hD : ∀ p,0 ≤ D p) (p : History P k) :
    0 ≤ freshAmplitude L k q Cf ell D p := mul_nonneg (Real.sqrt_nonneg _) (hD p)

theorem freshAmplitude_replaceSpace (k : ℕ) (q Cf ell : ℝ)
    (D : History P k → ℝ) (hD : ∀ p x,D (replaceSpace k p x)=D p)
    (p : History P k) (x : Fin k → HeatCircle) :
    freshAmplitude L k q Cf ell D (replaceSpace k p x)=freshAmplitude L k q Cf ell D p := by
  simp only [freshAmplitude,replaceSpace_terminal,rowTime_replaceSpace,hD]

end SHE.HistoryQuarterFields
