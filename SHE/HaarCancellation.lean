module

public import SHE.HaarHigherColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat Filter Topology
open scoped ContDiff
local instance haarCancellation_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def circleOne : CircleL2 := gridStep 0 (fun _ => 1)

theorem circleOne_ae : circleOne =ᵐ[haarAddCircle] (fun _ => (1 : ℂ)) := by
  simpa only [circleOne, Complex.ofReal_one] using gridStep_ae_cellIndex 0 (fun _ => (1 : ℝ))

theorem cellRestriction_one (n : ℕ) (x : Grid n) : cellRestriction n x circleOne = cellIndicator n x := by
  apply Lp.ext
  filter_upwards [cellRestriction_ae n x circleOne, circleOne_ae, cellIndicator_ae n x] with y hr ho hi
  rw [hr, hi]
  by_cases hy : y ∈ cellSet n x
  · simp only [Set.indicator_of_mem hy, ho]
  · simp only [Set.indicator_of_notMem hy]

theorem inner_one_cellRestriction (n : ℕ) (x : Grid n) (f : CircleL2)
    (hf : ∀ᵐ y ∂haarAddCircle, (f y).im = 0) :
    inner ℂ circleOne (cellRestriction n x f) = ((((2 ^ n : ℕ) : ℝ))⁻¹ * localAverage n f x : ℝ) := by
  rw [cellRestriction_inner, cellRestriction_one]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    unfold localAverage cellIndicator
    have hN : (((2 ^ n : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  · simp only [Complex.ofReal_im]
    exact inner_real_fields_im _ _ (gridStep_real_ae n (Pi.single x 1)) hf

theorem inner_real_smul_right (r : ℝ) (u v : CircleL2) :
    inner ℂ u (r • v) = (r : ℂ) * inner ℂ u v := by
  change inner ℂ u ((r : ℂ) • v) = _
  exact inner_smul_right _ _ _

/-- Zero mean uses exactly the true two child masses and requires only
their positivity, rather than global pointwise ellipticity. -/
theorem globalHaarColumn_mean_zero (p : List Bool) (f : CircleL2)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hL : 0 < localAverage (p.length+1) f (bottomLeaf p false))
    (hR : 0 < localAverage (p.length+1) f (bottomLeaf p true)) :
    inner ℂ circleOne (globalHaarColumn (some p) f) = 0 := by
  rw [globalHaarColumn_two_children, inner_add_right, inner_real_smul_right, inner_real_smul_right,
    inner_one_cellRestriction _ _ f hfreal, inner_one_cellRestriction _ _ f hfreal]
  have he := haar_cancellation hL hR
  have he' :
      (Real.sqrt (((2 ^ (p.length+1) : ℕ) : ℝ)) *
        haarLeft (localAverage (p.length+1) f (bottomLeaf p false)) (localAverage (p.length+1) f (bottomLeaf p true))) *
          ((((2 ^ (p.length+1) : ℕ) : ℝ))⁻¹ * localAverage (p.length+1) f (bottomLeaf p false)) +
      (Real.sqrt (((2 ^ (p.length+1) : ℕ) : ℝ)) *
        haarRight (localAverage (p.length+1) f (bottomLeaf p false)) (localAverage (p.length+1) f (bottomLeaf p true))) *
          ((((2 ^ (p.length+1) : ℕ) : ℝ))⁻¹ * localAverage (p.length+1) f (bottomLeaf p true)) = 0 := by
    calc
      _ = Real.sqrt (((2 ^ (p.length+1) : ℕ) : ℝ)) * (((2 ^ (p.length+1) : ℕ) : ℝ))⁻¹ *
        (localAverage (p.length+1) f (bottomLeaf p false) *
          haarLeft (localAverage (p.length+1) f (bottomLeaf p false)) (localAverage (p.length+1) f (bottomLeaf p true)) +
        localAverage (p.length+1) f (bottomLeaf p true) *
          haarRight (localAverage (p.length+1) f (bottomLeaf p false)) (localAverage (p.length+1) f (bottomLeaf p true))) := by ring
      _ = 0 := by rw [he, mul_zero]
  exact_mod_cast he'

theorem realEmbed_real (f : DyadicApproximation.RealL2) :
    ∀ᵐ y ∂haarAddCircle, (DyadicApproximation.realEmbed f y).im = 0 := by
  filter_upwards [DyadicApproximation.realEmbed_ae f] with y hy
  rw [hy]
  exact Complex.ofReal_im _

theorem globalHaarColumn_jet_real_comp (p : List Bool) (f : DyadicApproximation.RealL2)
    (hf : ∀ x, 0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x)
    (j : ℕ) (v : Fin j → DyadicApproximation.RealL2) :
    iteratedFDeriv ℝ j (globalHaarColumn (some p) ∘ DyadicApproximation.realEmbed) f v =
      iteratedFDeriv ℝ j (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)) := by
  let B := (normalizedState p).comp DyadicApproximation.realEmbed
  have hp : B f ∈ statePositive := ⟨hf _, hf _⟩
  have he := B.iteratedFDerivWithin_comp_right
    (fun z hz => (contDiffAt_stateColumn z hz ∞).contDiffWithinAt)
    isOpen_statePositive.uniqueDiffOn (isOpen_statePositive.preimage B.continuous).uniqueDiffOn
    hp (i := j) (by simp : (j : WithTop ℕ∞) ≤ ∞)
  have hfun : stateColumn ∘ B = globalHaarColumn (some p) ∘ DyadicApproximation.realEmbed :=
    funext (fun z => (globalHaarColumn_state p (DyadicApproximation.realEmbed z)).symm)
  have hG : ContDiffAt ℝ j (globalHaarColumn (some p) ∘ DyadicApproximation.realEmbed) f :=
    (contDiffAt_globalHaarColumn (some p) (DyadicApproximation.realEmbed f) hf j).comp f
      DyadicApproximation.realEmbed.contDiff.contDiffAt
  rw [hfun, iteratedFDerivWithin_eq_iteratedFDeriv
      (isOpen_statePositive.preimage B.continuous).uniqueDiffOn hG hp,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      (contDiffAt_stateColumn (B f) hp j) hp] at he
  have hv := congrArg (fun A => A v) he
  rw [globalHaarColumn_jet_state p (DyadicApproximation.realEmbed f) hf]
  exact hv

/-- All actual higher derivative detail columns retain zero spatial
integral, for literal real coefficient fields and real directions. -/
theorem globalHaarColumn_jet_mean_zero (p : List Bool) (f : DyadicApproximation.RealL2)
    (hf : ∀ x, 0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x)
    (j : ℕ) (v : Fin j → DyadicApproximation.RealL2) :
    inner ℂ circleOne (iteratedFDeriv ℝ j (globalHaarColumn (some p))
      (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i))) = 0 := by
  let G := globalHaarColumn (some p) ∘ DyadicApproximation.realEmbed
  let H : DyadicApproximation.RealL2 → ℂ := fun z => inner ℂ circleOne (G z)
  have hc (b : Bool) : Continuous (fun z : DyadicApproximation.RealL2 =>
      localAverage (p.length+1) (DyadicApproximation.realEmbed z) (bottomLeaf p b)) :=
    ((continuous_apply (bottomLeaf p b)).comp (continuous_localAverage (p.length+1))).comp
      DyadicApproximation.realEmbed.continuous
  have hevent : H =ᶠ[𝓝 f] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const (hc false)).mem_nhds (hf (bottomLeaf p false)),
      (isOpen_lt continuous_const (hc true)).mem_nhds (hf (bottomLeaf p true))] with z hL hR
    exact globalHaarColumn_mean_zero p (DyadicApproximation.realEmbed z) (realEmbed_real z) hL hR
  have hzero : iteratedFDeriv ℝ j H f = 0 := by
    have he := (hevent.iteratedFDeriv ℝ j).eq_of_nhds
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using he
  have hG : ContDiffAt ℝ j G f :=
    (contDiffAt_globalHaarColumn (some p) (DyadicApproximation.realEmbed f) hf j).comp f
      DyadicApproximation.realEmbed.contDiff.contDiffAt
  have he := ((innerSL ℂ circleOne).restrictScalars ℝ).iteratedFDeriv_comp_left hG (i := j) le_rfl
  change iteratedFDeriv ℝ j H f = ((innerSL ℂ circleOne).restrictScalars ℝ).compContinuousMultilinearMap
    (iteratedFDeriv ℝ j G f) at he
  rw [hzero] at he
  have hv := congrArg (fun A => A v) he
  change 0 = inner ℂ circleOne (iteratedFDeriv ℝ j G f v) at hv
  rw [globalHaarColumn_jet_real_comp p f hf j v] at hv
  exact hv.symm

end SHE.FiniteHaar
