module

public import SHEStochastic.NativeRandomInitialKernel
public import SHEStochastic.NativeContinuationKernel
public import SHEStochastic.NativeContinuationCharacteristics
public import SHEStochastic.CanonicalMildFourierCharacteristics
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.ScalarVarianceNormalization
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open GaussianItoTest JointFourierCylinderGenerator
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

abbrev Noise := Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))

theorem square_holder {G : ℝ → ℝ} {C β : ℝ≥0} (hG : HolderWith C β G)
    (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) : HolderWith (2*B*C) β (fun z ↦ (G z)^2) := by
  apply PositiveScalarApproximation.holder_of_bound
  intro x y
  have hd : |G x-G y| ≤ C*|x-y|^(β : ℝ) := by simpa only [Real.dist_eq] using hG.dist_le x y
  have hx : |G x| ≤ B := by simpa only [Real.norm_eq_abs] using hb x
  have hy : |G y| ≤ B := by simpa only [Real.norm_eq_abs] using hb y
  have hs : |G x+G y| ≤ 2*(B : ℝ) := (abs_add_le _ _).trans (by linarith)
  calc
    _ = |G x-G y| * |G x+G y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (C*|x-y|^(β : ℝ))*(2*(B : ℝ)) :=
      mul_le_mul hd hs (abs_nonneg _) (by positivity)
    _ = _ := by push_cast; ring

theorem constant_sign {G : ℝ → ℝ} (hc : Continuous G) (hne : ∀ z, G z ≠ 0) :
    (∀ z, 0 < G z) ∨ (∀ z, G z < 0) := by
  by_cases h0 : 0 < G 0
  · left
    intro z
    by_contra hz
    obtain ⟨w, hw⟩ := mem_range_of_exists_le_of_exists_ge hc ⟨z, le_of_not_gt hz⟩ ⟨0, h0.le⟩
    exact hne w hw
  · right
    intro z
    by_contra hz
    obtain ⟨w, hw⟩ := mem_range_of_exists_le_of_exists_ge hc ⟨0, le_of_not_gt h0⟩ ⟨z, le_of_not_gt hz⟩
    exact hne w hw

def signMap (σ : ℝ) (hσ : σ^2 = 1) : Noise ≃ₗᵢ[ℝ] Noise where
  toFun u := σ • u
  invFun u := σ • u
  left_inv u := by change σ • (σ • u) = u; rw [smul_smul, ← pow_two, hσ, one_smul]
  right_inv u := by change σ • (σ • u) = u; rw [smul_smul, ← pow_two, hσ, one_smul]
  map_add' u v := smul_add _ _ _
  map_smul' r u := smul_comm _ _ _
  norm_map' u := by
    change ‖σ • u‖ = ‖u‖
    have hs : |σ| = 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
    rw [norm_smul, Real.norm_eq_abs, hs, one_mul]

def signBasis {ι : Type*} (q : HilbertBasis ι ℝ Noise) (σ : ℝ) (hσ : σ^2 = 1) :
    HilbertBasis ι ℝ Noise := HilbertBasis.ofRepr ((signMap σ hσ).symm.trans q.repr)

theorem signBasis_apply {ι : Type*} (q : HilbertBasis ι ℝ Noise) (σ : ℝ) (hσ : σ^2 = 1) (i : ι) :
    signBasis q σ hσ i = σ • q i := by
  classical
  change ((signMap σ hσ).symm.trans q.repr).symm (lp.single 2 i (1 : ℝ)) = _
  simp only [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, q.repr_symm_single]
  rfl

variable {G K : ℝ → ℝ} {C D β : ℝ≥0} (hG : HolderWith C β G) (hK : HolderWith D β K)
  (hβ : 0 < β) (hβ1 : β ≤ 1) (σ : ℝ) (hσ : σ^2 = 1) (hcoeff : ∀ z, K z = σ*G z)
  {s d : ℕ} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  (b c : Fin d → Noise) (hdir : ∀ j, c j = σ • b j)

include hcoeff in
theorem state_row (u : RealL2) (aa : ℂ →L[ℝ] ℝ) (nn : ℤ) :
    StateNoiseCovariance.row haarAddCircle hβ hβ1 hK (NativeFourierHeatCoordinate.weight aa nn)
        (NativePhysicalState.push u) =
      σ • StateNoiseCovariance.row haarAddCircle hβ hβ1 hG (NativeFourierHeatCoordinate.weight aa nn)
        (NativePhysicalState.push u) := by
  apply Lp.ext
  filter_upwards [StateNoiseCovariance.row_ae haarAddCircle hβ hβ1 hK
    (NativeFourierHeatCoordinate.weight aa nn) (NativePhysicalState.push u),
    StateNoiseCovariance.row_ae haarAddCircle hβ hβ1 hG
      (NativeFourierHeatCoordinate.weight aa nn) (NativePhysicalState.push u),
    Lp.coeFn_smul σ (StateNoiseCovariance.row haarAddCircle hβ hβ1 hG
      (NativeFourierHeatCoordinate.weight aa nn) (NativePhysicalState.push u))] with x hk hg hs
  rw [hs, hk]
  simp only [Pi.smul_apply]
  rw [hg, hcoeff]
  simp only [smul_eq_mul]
  ring

include hcoeff hdir in
theorem rows (u : RealL2) (i : Fin (s+d)) :
    JointFourierCylinderGenerator.rows hK hβ hβ1 a n c u i =
      σ • JointFourierCylinderGenerator.rows hG hβ hβ1 a n b u i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [JointFourierCylinderGenerator.rows, Fin.addCases_left]
    exact state_row hG hK hβ hβ1 σ hcoeff u (a j) (n j)
  · intro j
    simpa only [JointFourierCylinderGenerator.rows, Fin.addCases_right] using hdir j

include hσ hcoeff in
theorem diagonal (hβlt : β < 1) (B A : ℝ≥0)
    (hb : ∀ z, ‖G z‖ ≤ B) (hc : ∀ z, ‖K z‖ ≤ A) (aa : ℂ →L[ℝ] ℝ) (nn : ℤ) :
    NativeFourierCompensatorValue.diagonal hK hβ hβlt A hc aa nn =
      NativeFourierCompensatorValue.diagonal hG hβ hβlt B hb aa nn := by
  ext u
  rw [NativeFourierCompensatorValue.diagonal_apply, NativeFourierCompensatorValue.diagonal_apply,
    state_row hG hK hβ hβlt.le σ hcoeff, norm_smul, mul_pow]
  have hs : ‖σ‖^2 = 1 := by simpa only [Real.norm_eq_abs, sq_abs] using hσ
  rw [hs, one_mul]

include hσ hcoeff in
theorem mixed_covariance (hβlt : β < 1) (B A : ℝ≥0)
    (hb : ∀ z, ‖G z‖ ≤ B) (hc : ∀ z, ‖K z‖ ≤ A) (aa : ℂ →L[ℝ] ℝ) (nn : ℤ) (bb : Noise) :
    NativeFourierCompensatorValue.mixed hK hβ hβlt A hc aa nn (σ • bb) =
      NativeFourierCompensatorValue.mixed hG hβ hβlt B hb aa nn bb := by
  ext u
  change inner ℝ (StateNoiseCovariance.row haarAddCircle hβ hβlt.le hK
      (NativeFourierHeatCoordinate.weight aa nn) (NativePhysicalState.push u)) (σ • bb) =
    inner ℝ (StateNoiseCovariance.row haarAddCircle hβ hβlt.le hG
      (NativeFourierHeatCoordinate.weight aa nn) (NativePhysicalState.push u)) bb
  rw [state_row hG hK hβ hβlt.le σ hcoeff, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, ← pow_two, hσ, one_mul]

include hσ hcoeff in
theorem fourier_holds {ι : Type*} [Countable ι] [DecidableEq ι]
    (hβlt : β < 1) (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (hc : ∀ z, ‖K z‖ ≤ B)
    (q r : HilbertBasis ι ℝ Noise) (hr : ∀ i, r i = σ • q i)
    (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
    (h : CanonicalMildFourierCharacteristics.Holds H Q hK hβ hβlt B hc r) :
    CanonicalMildFourierCharacteristics.Holds H Q hG hβ hβlt B hb q := by
  intro aa nn
  obtain ⟨hm, hs, hx, hmom⟩ := h aa nn
  refine ⟨hm, ?_, ?_, hmom⟩
  · have he : CanonicalFourierDisintegration.square (ι := ι) H hK hβ hβlt B hc aa nn =
        CanonicalFourierDisintegration.square H hG hβ hβlt B hb aa nn := by
      funext t x
      unfold CanonicalFourierDisintegration.square
      rw [diagonal hG hK hβ σ hσ hcoeff hβlt B B hb hc aa nn]
    rwa [he] at hs
  · intro i
    have he : CanonicalFourierDisintegration.mixed H hK hβ hβlt B hc aa nn (r i) i =
        CanonicalFourierDisintegration.mixed H hG hβ hβlt B hb aa nn (q i) i := by
      funext t x
      unfold CanonicalFourierDisintegration.mixed
      rw [hr i, mixed_covariance hG hK hβ σ hσ hcoeff hβlt B B hb hc aa nn (q i)]
    simpa only [he] using hx i

include hσ hcoeff hdir in
theorem generator (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hb : ∀ z, ‖G z‖ ≤ B) (hc : ∀ z, ‖K z‖ ≤ A)
    {ι : Type*} (driver : Fin d → ι) (f : State (s+d) → ℝ)
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    JointFourierCylinderGenerator.generator hK hβ hβ1 A hA hc a n c driver f hf hs =
      JointFourierCylinderGenerator.generator hG hβ hβ1 B hB hb a n b driver f hf hs := by
  ext q
  rw [generator_apply, generator_apply]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [rows hG hK hβ hβ1 σ hcoeff a n b c hdir,
    rows hG hK hβ hβ1 σ hcoeff a n b c hdir,
    real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc σ σ, ← pow_two, hσ, one_mul]

include hσ hcoeff in
/-- Changing the sign of the coefficient and its spatial noise basis
together preserves the literal joint martingale problem. -/
theorem problem (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hb : ∀ z, ‖G z‖ ≤ B) (hc : ∀ z, ‖K z‖ ≤ A)
    {ι : Type*} [Countable ι] (q r : HilbertBasis ι ℝ Noise) (hr : ∀ i, r i = σ • q i)
    (H : ℝ≥0) (ν : Measure (StoppedPathPasting.Path H (RealL2 × (ι → ℝ))))
    (h : JointFourierProblem.Holds hK hβ hβ1 A hA hc H r ν) :
    JointFourierProblem.Holds hG hβ hβ1 B hB hb H q ν := by
  intro s d a n driver f hf hSmooth hs
  rw [← generator hG hK hβ hβ1 σ hσ hcoeff a n (fun j ↦ q (driver j))
    (fun j ↦ r (driver j)) (fun j ↦ hr (driver j)) B A hB hA hb hc driver f hf hs]
  exact h a n driver f hf hSmooth hs

/-- Construct continuation for a bounded nondegenerate scalar
coefficient of either sign, using smooth approximations of its variance.
The sign is absorbed into a fixed spatial noise basis. -/
theorem exists_kernel {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (P : FiniteScalarIto.Family F μ H ι) (q : HilbertBasis ι ℝ Noise)
    (hβlt : β < 1) (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
    (ell : ℝ) (hell : 0 < ell) (helliptic : ∀ z, ell ≤ (G z)^2)
    (hH : 0 < H) (hH1 : H ≤ 1)
    (ρ : Measure RealL2) [IsProbabilityMeasure ρ] (hρ : MemLp (id : RealL2 → RealL2) 2 ρ) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H),
      CanonicalInitialKernel.initialLaw H Q.toMeasure = ρ ∧
      NativeContinuationCharacteristics.BrownianInput H Q.toMeasure ∧
      ∀ᵐ u ∂ρ,
        CanonicalMildFourierCharacteristics.Holds H (CanonicalInitialKernel.kernel H Q.toMeasure u)
          hG hβ hβlt B hb q ∧ ∀ v : ι → ℝ,
        (∀ᵐ y ∂NativeContinuationKernel.joint H Q.toMeasure (u,v),
          y (StoppedPathPasting.origin H) = (u,v)) ∧
        JointFourierProblem.Holds hG hβ hβlt.le B B.property hb H q
          (NativeContinuationKernel.joint H Q.toMeasure (u,v)) := by
  have hv := square_holder hG B hb
  have hbounds (z : ℝ) : ell ≤ (G z)^2 ∧ (G z)^2 ≤ (B : ℝ)^2 := by
    refine ⟨helliptic z, ?_⟩
    have hz : |G z| ≤ B := by simpa only [Real.norm_eq_abs] using hb z
    nlinarith [sq_abs (G z), abs_nonneg (G z), B.property]
  have hne (z : ℝ) : G z ≠ 0 := by
    intro hz
    have h := helliptic z
    rw [hz] at h
    nlinarith
  obtain ⟨σ, hσ, he⟩ : ∃ σ : ℝ, σ^2 = 1 ∧
      ∀ z, PositiveScalarApproximation.root (a := fun z ↦ (G z)^2) z = σ*G z := by
    rcases constant_sign (hG.continuous hβ) hne with hp | hn
    · refine ⟨1, by norm_num, ?_⟩
      intro z
      simp [PositiveScalarApproximation.root, Real.sqrt_sq (hp z).le]
    · refine ⟨-1, by norm_num, ?_⟩
      intro z
      simp [PositiveScalarApproximation.root, Real.sqrt_sq_eq_abs, abs_of_neg (hn z)]
  let r := signBasis q σ hσ
  let hr := PositiveScalarApproximation.root_holder hv hβ ell ((B : ℝ)^2) hell hbounds
  let A := PositiveScalarApproximation.bound ((B : ℝ)^2)
  let hbRoot := PositiveScalarApproximation.root_bound ell ((B : ℝ)^2) hbounds
  have hA : A = B := NNReal.eq (Real.sqrt_sq B.property)
  have hbRootB : ∀ z, ‖PositiveScalarApproximation.root (a := fun z ↦ (G z)^2) z‖ ≤ B := by
    intro z
    have hz : ‖PositiveScalarApproximation.root (a := fun z ↦ (G z)^2) z‖ ≤ A := hbRoot z
    rw [hA] at hz
    exact hz
  obtain ⟨Q, hQ, hs⟩ := NativeRandomInitialKernel.exists_kernel F μ H P r hv hβ hβlt
    ell ((B : ℝ)^2) hell hbounds hH hH1 ρ hρ
  refine ⟨Q, hQ, hs.mono (fun _ hu ↦ hu.choose), ?_⟩
  have hp := NativeContinuationKernel.properties H Q.toMeasure hr hβ hβlt A hbRoot r hH hH1 hs
  rw [hQ] at hp
  have hSupport := hs
  unfold NativeFourierLimitKernel.Supports at hSupport
  rw [hQ] at hSupport
  filter_upwards [hp, hSupport] with u hu hsu
  obtain ⟨hBrown, hMild⟩ := hsu
  have hRoot := CanonicalMildFourierCharacteristics.holds H (CanonicalInitialKernel.kernel H Q.toMeasure u)
    hr hβ hβlt A hbRoot r hBrown hH1 hMild
  have hRootB : CanonicalMildFourierCharacteristics.Holds H (CanonicalInitialKernel.kernel H Q.toMeasure u)
      hr hβ hβlt B hbRootB r := by simpa only [hA] using hRoot
  refine ⟨fourier_holds hG hr hβ σ hσ he hβlt B hb hbRootB q r
    (signBasis_apply q σ hσ) H _ hRootB, ?_⟩
  intro v
  refine ⟨(hu v).1, ?_⟩
  intro s d a n driver f hf hSmooth hs
  exact problem hG hr hβ hβlt.le σ hσ he B A B.property A.property hb hbRoot q r
    (signBasis_apply q σ hσ) H _ (hu v).2 a n driver f hf hSmooth hs

end SHEStochastic.ScalarVarianceNormalization
