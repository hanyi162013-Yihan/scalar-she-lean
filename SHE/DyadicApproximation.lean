module

public import SHE.SignedPrefix
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Group.AddCircle

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.DyadicApproximation
open MeasureTheory AddCircle CircleHeat FiniteHaar Finset Set
open scoped ENNReal NNReal Topology
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Inner ℝ CircleL2 := Inner.rclikeToReal ℂ CircleL2
local instance : InnerProductSpace ℝ CircleL2 := InnerProductSpace.rclikeToReal ℂ CircleL2

/-- Literal dyadic cell averaging, rather than an abstract approximating
sequence supplied as a convergence premise. -/
def average (n : ℕ) (f : CircleL2) : CircleL2 := gridStep n (localAverage n f)

theorem gridStep_expansion (n : ℕ) (a : Grid n → ℝ) :
    gridStep n a = ∑ x : Grid n, a x • gridStep n (Pi.single x 1) := by
  have hc : a = ∑ x : Grid n, a x • (Pi.single x (1:ℝ) : Grid n → ℝ) := by
    ext y
    simp [Pi.single_apply]
  calc
    _ = gridStepLinear n (∑ x : Grid n, a x • (Pi.single x (1:ℝ) : Grid n → ℝ)) :=
      congrArg (gridStep n) hc
    _ = _ := by rw [map_sum]; simp only [map_smul]; rfl

theorem gridStep_pairing (n : ℕ) (a : Grid n → ℝ) (f : CircleL2) :
    inner ℝ (gridStep n a) f = (((2 ^ n : ℕ):ℝ))⁻¹ * ∑ x, a x * localAverage n f x := by
  have hp : (0:ℝ) < (2 ^ n : ℕ) := by positivity
  have hc (x : Grid n) : inner ℝ (gridStep n (Pi.single x 1)) f =
      (((2 ^ n : ℕ):ℝ))⁻¹ * localAverage n f x := by
    change (inner ℂ (gridStep n (Pi.single x 1)) f).re =
      (((2 ^ n : ℕ):ℝ))⁻¹ * ((((2 ^ n : ℕ):ℝ)) * (inner ℂ (gridStep n (Pi.single x 1)) f).re)
    rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have hs (x : Grid n) : inner ℝ (a x • gridStep n (Pi.single x 1)) f =
      a x * inner ℝ (gridStep n (Pi.single x 1)) f := by
    change (inner ℂ ((a x:ℂ) • gridStep n (Pi.single x 1)) f).re =
      a x * (inner ℂ (gridStep n (Pi.single x 1)) f).re
    rw [inner_smul_left, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [gridStep_expansion, sum_inner (𝕜:=ℝ)]
  simp_rw [hs, hc]
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

theorem localAverage_sub (n : ℕ) (f g : CircleL2) :
    localAverage n (f-g) = localAverage n f-localAverage n g := by
  funext x
  simp only [localAverage, inner_sub_right, Complex.sub_re, mul_sub, Pi.sub_apply]

theorem average_projection (n : ℕ) (f : CircleL2) :
    (StepInput.stepSpace (2 ^ n)).starProjection f = average n f := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨fun j => localAverage n f ((gridCellEquiv n).symm j), rfl⟩
  · intro w hw
    obtain ⟨z, hz⟩ := hw
    change stepLp (2 ^ n) z = w at hz
    have he : stepLp (2 ^ n) z = gridStep n (fun x => z (gridCellEquiv n x)) := by
      unfold gridStep
      simp only [Equiv.apply_symm_apply]
    rw [← hz, he, real_inner_comm, gridStep_pairing]
    unfold average
    rw [localAverage_sub, localAverage_gridStep, sub_self]
    simp

theorem average_norm_le (n : ℕ) (f : CircleL2) : ‖average n f‖ ≤ ‖f‖ := by
  rw [← average_projection]
  exact Submodule.norm_starProjection_apply_le _ _

theorem average_error_le (n : ℕ) (f : CircleL2) (a : Grid n → ℝ) :
    ‖average n f-f‖ ≤ ‖gridStep n a-f‖ := by
  have hm : gridStep n a ∈ StepInput.stepSpace (2 ^ n) :=
    ⟨fun j => a ((gridCellEquiv n).symm j), rfl⟩
  rw [norm_sub_rev, ← average_projection]
  have hmin := Submodule.starProjection_minimal (U := StepInput.stepSpace (2 ^ n)) f
  rw [hmin]
  have hh := ciInf_le (show BddBelow (Set.range (fun v : StepInput.stepSpace (2 ^ n) =>
    ‖f-(v:CircleL2)‖)) from ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩)
      (⟨gridStep n a, hm⟩ : StepInput.stepSpace (2 ^ n))
  rw [norm_sub_rev] at hh
  exact hh

def cellLeft (n : ℕ) (j : ZMod (2 ^ n)) : AddCircle (1:ℝ) :=
  ((((j.val:ℝ) / (((2 ^ n : ℕ):ℝ))) : ℝ) : AddCircle (1:ℝ))

/-- The actual ceil-cell selector is always within one cell width of its
left endpoint, including the circle identification at zero. -/
theorem cellLeft_distance (n : ℕ) (y : AddCircle (1:ℝ)) :
    dist y (cellLeft n (cellIndex n y)) ≤ (((2 ^ n : ℕ):ℝ))⁻¹ := by
  let D : ℝ := ((2 ^ n : ℕ):ℝ)
  let r : ℝ := AddCircle.equivIoc (1:ℝ) 0 y
  have hD : 0 < D := by dsimp [D]; positivity
  have hr : r ∈ Ioc (0:ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIoc (1:ℝ) 0 y).property
  let k : ℤ := ⌈D*r⌉-1
  have hk0 : 0 ≤ k := by
    have hp := Int.ceil_pos.mpr (mul_pos hD hr.1)
    dsimp only [k]
    omega
  have hkN : k < (2 ^ n : ℕ) := by
    have hp : ⌈D*r⌉ ≤ ((2 ^ n : ℕ):ℤ) :=
      Int.ceil_le.mpr (by dsimp [D]; exact mul_le_of_le_one_right hD.le hr.2)
    dsimp only [k]
    omega
  have hkcast : (k.toNat:ℤ) = k := Int.toNat_of_nonneg hk0
  have hj : (cellIndex n y).val = k.toNat := by
    have he : cellIndex n y = (k.toNat : ZMod (2 ^ n)) := by
      change ((k:ℤ) : ZMod (2 ^ n)) = (k.toNat : ZMod (2 ^ n))
      calc
        (k : ZMod (2 ^ n)) = ((k.toNat:ℤ) : ZMod (2 ^ n)) :=
          congrArg (fun z : ℤ => (z : ZMod (2 ^ n))) hkcast.symm
        _ = (k.toNat : ZMod (2 ^ n)) := Int.cast_natCast _
    rw [he, ZMod.val_natCast_of_lt (by omega)]
  have hjr : ((cellIndex n y).val:ℝ) = (k:ℝ) := by rw [hj]; exact_mod_cast hkcast
  have hceil := Int.ceil_eq_iff.mp (rfl : ⌈D*r⌉ = ⌈D*r⌉)
  have hkr : (k:ℝ) = (⌈D*r⌉:ℝ)-1 := by dsimp only [k]; push_cast; rfl
  have hlo : 0 ≤ r-((cellIndex n y).val:ℝ)/D := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hD).mpr
    rw [hjr, hkr]
    linarith [hceil.1]
  have hhi : r-((cellIndex n y).val:ℝ)/D ≤ D⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hD).mpr
    have he : (r-((cellIndex n y).val:ℝ)/D)*D = D*r-((cellIndex n y).val:ℝ) := by
      field_simp
    rw [he, hjr, hkr]
    linarith [hceil.2]
  have hy : ((r:ℝ) : AddCircle (1:ℝ)) = y := AddCircle.coe_equivIoc
  calc
    _ = dist (r:AddCircle (1:ℝ)) (cellLeft n (cellIndex n y)) :=
      congrArg (fun z => dist z (cellLeft n (cellIndex n y))) hy.symm
    _ = ‖((r-((cellIndex n y).val:ℝ)/D : ℝ) : AddCircle (1:ℝ))‖ := by
      rw [dist_eq_norm]
      change ‖(r:AddCircle (1:ℝ))-(((cellIndex n y).val:ℝ)/D : AddCircle (1:ℝ))‖ = _
      rw [← QuotientAddGroup.mk_sub]
    _ ≤ ‖r-((cellIndex n y).val:ℝ)/D‖ := QuotientAddGroup.norm_mk_le_norm
    _ = r-((cellIndex n y).val:ℝ)/D := by rw [Real.norm_eq_abs, abs_of_nonneg hlo]
    _ ≤ _ := hhi

abbrev RealL2 := Lp ℝ 2 (haarAddCircle (T := (1:ℝ)))

/-- The real coefficient field inside the complex Fourier Hilbert space. -/
def realEmbed : RealL2 →L[ℝ] CircleL2 :=
  Complex.ofRealCLM.compLpL 2 (haarAddCircle (T := (1:ℝ)))

theorem realEmbed_norm_le (g : RealL2) : ‖realEmbed g‖ ≤ ‖g‖ := by
  have h := Complex.ofRealCLM.norm_compLp_le (p := 2) g
  change ‖Complex.ofRealCLM.compLp g‖ ≤ ‖g‖
  calc
    _ ≤ ‖Complex.ofRealCLM‖ * ‖g‖ := h
    _ = _ := by simp [Complex.ofRealCLM]

theorem realEmbed_ae (g : RealL2) :
    realEmbed g =ᵐ[haarAddCircle (T := (1:ℝ))] fun y => (g y : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL g

theorem realEmbed_continuous_ae (h : C(AddCircle (1:ℝ),ℝ)) :
    realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h)
      =ᵐ[haarAddCircle (T := (1:ℝ))] fun y => (h y : ℂ) := by
  filter_upwards [realEmbed_ae (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (haarAddCircle (T := (1:ℝ))) h] with y hy hh
  rw [hy, hh]

theorem mesh_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (((2 ^ n : ℕ):ℝ))⁻¹) Filter.atTop (𝓝 (0:ℝ)) := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

def samples (n : ℕ) (h : C(AddCircle (1:ℝ),ℝ)) : Grid n → ℝ :=
  fun x => h (cellLeft n (gridCellEquiv n x))

theorem samples_error_le (n : ℕ) (h : C(AddCircle (1:ℝ),ℝ)) (ε : ℝ)
    (hε : 0 ≤ ε)
    (he : ∀ y : AddCircle (1:ℝ), dist y (cellLeft n (cellIndex n y)) ≤
      (((2 ^ n : ℕ):ℝ))⁻¹ → dist (h (cellLeft n (cellIndex n y))) (h y) ≤ ε) :
    ‖gridStep n (samples n h) -
      realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h)‖ ≤ ε := by
  have hae : ∀ᵐ y ∂haarAddCircle (T := (1:ℝ)),
      ‖(gridStep n (samples n h) -
      realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h)) y‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub (gridStep n (samples n h))
        (realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h)),
      gridStep_ae_cellIndex n (samples n h), realEmbed_continuous_ae h] with y hy hs hh
    rw [hy]
    simp only [Pi.sub_apply, hs, hh]
    simp only [samples, Equiv.apply_symm_apply]
    change ‖((h (cellLeft n (cellIndex n y)):ℝ):ℂ) - (h y:ℂ)‖ ≤ ε
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact he y (cellLeft_distance n y)
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hε hae

theorem samples_tendsto (h : C(AddCircle (1:ℝ),ℝ)) :
    Filter.Tendsto (fun n => gridStep n (samples n h)) Filter.atTop
      (𝓝 (realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,huniform⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous h.continuous)
    (ε/2) (by positivity)
  have hevent := mesh_tendsto_zero.eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (samples_error_le n h (ε/2) (by positivity) ?_) (by linarith)
  intro y hy
  exact (huniform (by rw [dist_comm]; exact lt_of_le_of_lt hy (hN n hn))).le

theorem average_realEmbed_tendsto (g : RealL2) :
    Filter.Tendsto (fun n => average n (realEmbed g)) Filter.atTop (𝓝 (realEmbed g)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hdense := ContinuousMap.toLp_denseRange (α := AddCircle (1:ℝ)) (E := ℝ)
    (p := 2) (haarAddCircle (T := (1:ℝ))) ℝ (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  obtain ⟨h,hh⟩ := hdense.exists_dist_lt g (by positivity : 0 < ε/2)
  have hsample := Metric.tendsto_atTop.mp (samples_tendsto h) (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := hsample
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (average_error_le n (realEmbed g) (samples n h))
  calc
    _ ≤ ‖gridStep n (samples n h) -
        realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h)‖ +
      ‖realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h) - realEmbed g‖ :=
      by simpa only [dist_eq_norm] using (dist_triangle (gridStep n (samples n h))
        (realEmbed (ContinuousMap.toLp 2 (haarAddCircle (T := (1:ℝ))) ℝ h)) (realEmbed g))
    _ < ε/2 + ε/2 := by
      apply add_lt_add
      · simpa only [dist_eq_norm] using hN n hn
      · rw [← map_sub]
        apply lt_of_le_of_lt (realEmbed_norm_le _)
        simpa only [dist_eq_norm, norm_sub_rev] using hh
    _ = ε := by ring

/-- Actual dyadic averages converge for every real `L²` coefficient field.
No regularity or convergence premise is imposed on the coefficient. -/
theorem average_tendsto_of_real (f : CircleL2)
    (hf : ∀ᵐ y ∂haarAddCircle (T := (1:ℝ)), (f y).im = 0) :
    Filter.Tendsto (fun n => average n f) Filter.atTop (𝓝 f) := by
  let g : RealL2 := Complex.reCLM.compLp f
  have he : realEmbed g = f := by
    apply Lp.ext
    filter_upwards [realEmbed_ae g, Complex.reCLM.coeFn_compLp f, hf] with y hy hg him
    rw [hy]
    change g y = (f y).re at hg
    rw [hg]
    apply Complex.ext <;> simp [him]
  rw [← he]
  exact average_realEmbed_tendsto g

def realPart (f : CircleL2) : RealL2 := Complex.reCLM.compLp f

def imagPart (f : CircleL2) : RealL2 := Complex.imCLM.compLp f

theorem real_imag_decomposition (f : CircleL2) :
    realEmbed (realPart f) + Complex.I • realEmbed (imagPart f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (realEmbed (realPart f)) (Complex.I • realEmbed (imagPart f)),
    Lp.coeFn_smul Complex.I (realEmbed (imagPart f)), realEmbed_ae (realPart f),
    realEmbed_ae (imagPart f), Complex.reCLM.coeFn_compLp f,
    Complex.imCLM.coeFn_compLp f] with y ha hs hr hi hrf hif
  rw [ha]
  change realEmbed (realPart f) y + (Complex.I • realEmbed (imagPart f)) y = f y
  rw [hs]
  change realEmbed (realPart f) y + Complex.I * realEmbed (imagPart f) y = f y
  rw [hr,hi]
  change realPart f y = (f y).re at hrf
  change imagPart f y = (f y).im at hif
  rw [hrf,hif]
  apply Complex.ext <;> simp

/-- Complex dyadic step fields are built from two literal real step
fields, keeping the original real Haar synthesis interface available. -/
def complexGridStep (n : ℕ) (a b : Grid n → ℝ) : CircleL2 :=
  gridStep n a + Complex.I • gridStep n b

def complexAverage (n : ℕ) (f : CircleL2) : CircleL2 :=
  complexGridStep n (localAverage n (realEmbed (realPart f)))
    (localAverage n (realEmbed (imagPart f)))

/-- The actual complex dyadic step approximations converge for every
complex `L²` test field, by separate real and imaginary approximation. -/
theorem complexAverage_tendsto (f : CircleL2) :
    Filter.Tendsto (fun n => complexAverage n f) Filter.atTop (𝓝 f) := by
  have hh := (average_realEmbed_tendsto (realPart f)).add
    ((average_realEmbed_tendsto (imagPart f)).const_smul Complex.I)
  rw [real_imag_decomposition] at hh
  exact hh

end SHE.DyadicApproximation
