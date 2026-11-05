module

public import SHE.OmittedTimeFields
public import SHE.FiniteForestLeafInput
public import SHE.ControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.BaselineScaleParentInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2
  ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates OrderedHeatForests
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays CoveredControlledLaw
  GaussianAssignmentBlocks BaselineAssignmentScale
open scoped BigOperators
local instance baselineScaleParentInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

def coefficient (L : Level R X n) (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (p : History X k) (A0 ν : ℝ) (i : Index k) : ℝ :=
  if block (choices k i) i.1.succ=[] then
    |OmittedTimeFactor.factor L P k p (choices k i) i.1 A0 ν| else 0

def averagedScale (L : Level R X n) (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (k : ℕ) (p : History X k) (A0 ν κ : ℝ) (hκ : 0<κ)
    (t : Fin (n+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin n→HeatCircle) (x : HeatCircle) : ℝ :=
  ∑ i : Index k,coefficient L P k p A0 ν i*∫ w : Fin k→HeatCircle,
    parentDensity κ hκ k t ht (values aRoot k w)*
      |ControlledProfile.derivative P Λ u d
        ((targets L k p (leafIndex k (fun j=>j) i.1),x+values aRoot k w (leafIndex k (fun j=>j) i.1)),θ)|
      ∂Measure.pi (fun _=>haarAddCircle)

/-- Actual profile baseline inputs preserve every original leaf age and
minimum-gap time factor after positive forest averaging. The sharp
profile estimate used here is supplied on its genuine AE time set below. -/
theorem actual_parent_scale_of_sharp (L : Level R X n) (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ : ℝ) (k : ℕ) (p : History X k) {q : ℝ} (hq0 : 0≤q) (hq : q<(carrier L k).terminal p)
    (A0 ν κ : ℝ) (hκ : 0<κ) (t : Fin (n+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin n→HeatCircle)
    (hsharp : ∀ j : Fin k,normTwo haarAddCircle (fun x=>ControlledProfile.derivative P Λ u d
        ((targets L k p (leafIndex k (fun i=>i) j),x),θ))≤
      sharpConstant P d*(targets L k p (leafIndex k (fun i=>i) j))^((P.exponent-1)/4)) :
    MemLp (averagedScale L P Λ u d θ k p A0 ν κ hκ t ht aRoot) 2 haarAddCircle ∧
    normTwo haarAddCircle (averagedScale L P Λ u d θ k p A0 ν κ hκ t ht aRoot)≤
      (Fintype.card (Choices n k):ℝ)*(Fintype.card (Index k):ℝ)*BaselineOriginalGain.unitSharp P d*
        SharpWordTimeScale.total L P k p q A0 ν*((carrier L k).terminal p-q)^(-(1/4:ℝ)) := by
  classical
  let age := fun j : Fin k=>targets L k p (leafIndex k (fun i=>i) j)
  have hage (j : Fin k) : 0<age j :=
    (sub_pos.mpr hq).trans_le (OmittedTimeFactor.fresh_gap_le_leaf_age L k p q hq0 j)
  let f := fun (i : Index k) x=>ControlledProfile.derivative P Λ u d ((age i.1,x),θ)
  let B := fun i : Index k=>coarseConstant P d*(age i.1)^((P.exponent-2)/4)
  have hf (i : Index k) : Measurable (f i) := by
    convert! (derivative_measurable P hΛ u d hsmallPoint).comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const) using 1
  have hB (i : Index k) : 0≤B i :=
    mul_nonneg (coarseConstant_nonneg P d) (rpow_nonneg (hage i.1).le _)
  have hfb (i : Index k) (x : HeatCircle) : |f i x|≤B i :=
    derivative_coarse_power P hΛ u d hsmallPoint θ (age i.1,x) (hage i.1).le
  have ha (i : Index k) : 0≤coefficient L P k p A0 ν i := by
    unfold coefficient
    split_ifs <;> positivity
  have hmem := memLp_finsetSum Finset.univ (fun (i : Index k) _=>
    (FiniteForestLeafInput.parent_leaf_memLp κ hκ t ht aRoot (leafIndex k (fun j=>j) i.1)
      (f i) (hf i) (hB i) (hfb i)).const_mul (coefficient L P k p A0 ν i))
  refine ⟨hmem,?_⟩
  have hh := FiniteForestLeafInput.parent_leaf_sum_normTwo κ hκ t ht aRoot
    (fun i : Index k=>leafIndex k (fun j=>j) i.1) (coefficient L P k p A0 ν) ha f hf B hB hfb
  have hs : (∑ i : Index k,coefficient L P k p A0 ν i*normTwo haarAddCircle (f i))≤
      ∑ i : Index k,coefficient L P k p A0 ν i*(sharpConstant P d*(age i.1)^((P.exponent-1)/4)) :=
    Finset.sum_le_sum (fun (i : Index k) _=>mul_le_mul_of_nonneg_left (hsharp i.1) (ha i))
  have he : (∑ i : Index k,coefficient L P k p A0 ν i*(sharpConstant P d*(age i.1)^((P.exponent-1)/4)))=
      BaselineAssignmentScale.total L P k p A0 ν (fun j=>sharpConstant P d*(age j)^((P.exponent-1)/4)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hs0 : 0≤sharpConstant P d*(age i.1)^((P.exponent-1)/4) :=
      mul_nonneg (sharpConstant_nonneg P d) (rpow_nonneg (hage i.1).le _)
    simp only [coefficient,BaselineAssignmentScale.scale]
    split_ifs <;> simp only [abs_of_nonneg hs0,zero_mul] <;> ring
  have hp := BaselineAssignmentScale.restored_total_gain L P d k p q A0 ν (sub_pos.mpr hq)
    (fun j=>OmittedTimeFactor.fresh_gap_le_leaf_age L k p q hq0 j)
  have hb := hh.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [he] at hb
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Fintype.card (Choices n k))))
  convert! hfinal using 1 <;> simp only [averagedScale,f,age,mul_assoc]

end SHE.BaselineScaleParentInput
