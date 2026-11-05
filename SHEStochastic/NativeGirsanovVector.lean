module

public import SHEStochastic.NativeGirsanovFullPast
public import SHEStochastic.HilbertGaussianVector

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeGirsanovVector
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal
open HilbertGaussianVector NativeGirsanovTilt NativeCrossEnergy

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

theorem energy_of_profile (v : Lp C 2 νin) (q : ℝ≥0 → ℝ)
    (hq : ∀ᵐ p ∂νin, ‖v p‖ ^ 2 = q p.1) :
    NativeEnergy.energy v =ᵐ[μ] fun _ ↦ ∫ r, q r ∂νt := by
  have hp : (fun p : ℝ≥0 × Ω ↦ ‖v p‖ ^ 2) =ᵐ[(νt).prod μ] (fun p ↦ q p.1) :=
    ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hq
  have hs := (Measure.measurePreserving_swap (μ := μ)
    (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact integral_congr_ae hω

theorem cross_combination (S : Fin n → Lp C 2 νin) (x : EuclideanSpace ℝ (Fin n))
    (u : Lp C 2 νin) : cross (combination S x) u =ᵐ[μ]
      (fun ω ↦ ∑ i, x i * cross (S i) u ω) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let z : Lp C 2 νin := combination S x
  have hsource : z =ᵐ[νin] (fun p ↦ ∑ i, x i • S i p) := coe_combination S x
  have hrep : ∀ᵐ ω ∂μ, ∀ᵐ r ∂νt,
      z (r, ω) = ∑ i, x i • S i (r, ω) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := Prod.instMeasurableSpace
    have hp : (z : ℝ≥0 × Ω → C) =ᵐ[(νt).prod μ]
        (fun p ↦ ∑ i, x i • S i p) :=
      ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hsource
    exact Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := μ)
      (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp)
  have hint : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      Integrable (fun r ↦ inner ℝ (S i (r, ω)) (u (r, ω))) νt :=
    ae_all_iff.mpr (fun i ↦ (NativeCrossEnergy.product_integrable (S i) u).prod_left_ae)
  filter_upwards [hrep, hint] with ω hr hi
  change (∫ r, inner ℝ (combination S x (r, ω)) (u (r, ω)) ∂νt) = _
  calc
    _ = ∫ r, inner ℝ (∑ i, x i • S i (r, ω)) (u (r, ω)) ∂νt :=
      integral_congr_ae (hr.mono fun r h ↦ congrArg (fun z : C ↦ inner ℝ z (u (r, ω))) h)
    _ = ∫ r, ∑ i, x i * inner ℝ (S i (r, ω)) (u (r, ω)) ∂νt := by
      simp only [sum_inner, real_inner_smul_left]
    _ = ∑ i, ∫ r, x i * inner ℝ (S i (r, ω)) (u (r, ω)) ∂νt :=
      integral_finsetSum _ (fun i _ ↦ (hi i).const_mul (x i))
    _ = _ := by simp only [integral_const_mul, cross]

def vector (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (S : Fin n → Lp C 2 νin) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ shift P e u (S i) ω)

theorem linear_projection (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (S : Fin n → Lp C 2 νin) (x : EuclideanSpace ℝ (Fin n)) :
    shift P e u (combination S x) =ᵐ[μ] (fun ω ↦ inner ℝ (vector P e u S ω) x) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hJ : FiniteCylindricalIto.rawIntegral P.toCoordinates e (combination S x) =
      combination (fun i ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i)) x := by
    simp only [combination, map_sum, map_smul]
  have hI : (FiniteCylindricalIto.rawIntegral P.toCoordinates e (combination S x) : Ω → ℝ) =ᵐ[μ]
      (fun ω ↦ ∑ i, x i * FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i) ω) := by
    rw [hJ]
    exact coe_combination _ x
  filter_upwards [hI, cross_combination S x u] with ω hIω hCω
  change FiniteCylindricalIto.rawIntegral P.toCoordinates e (combination S x) ω + cross (combination S x) u ω = _
  rw [hIω, hCω]
  simp only [vector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    WithLp.ofLp_toLp, Pi.star_apply, star_trivial, shift]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ ↦ (mul_add _ _ _).symm)

/-- Joint Gaussian law and full-past independence of the actual shifted
observations. Singular covariances and repeated rows are retained. -/
theorem law_and_independent (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (s : ℝ≥0) (hsH : s ≤ H) (S : Fin n → Lp C 2 νin)
    (hSa : ∀ i, ∀ᵐ p ∂νin, p.1 ≤ s → S i p = 0)
    (hprofiles : ∀ x : EuclideanSpace ℝ (Fin n), ∃ q : ℝ≥0 → ℝ,
      Integrable q νt ∧ (∀ r, 0 ≤ q r) ∧
      StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1) ∧
      (∀ᵐ p ∂νin, ‖combination S x p‖ ^ 2 = q p.1)) :
    HasLaw (vector P e u S) (multivariateGaussian 0 (gram ℝ S)) (measure P e u) ∧
    Indep (MeasurableSpace.comap (vector P e u S) (borel (EuclideanSpace ℝ (Fin n))))
      (F s) (measure P e u) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : IsProbabilityMeasure (measure P e u) := probability P e u K hK hu
  have hX : Measurable (vector P e u S) :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr
      fun i ↦ (shift_stronglyMeasurable P e u (S i)).measurable)
  apply ConditionalCharacteristic.law_and_independent (F s) (F.le s) hX
  intro x A hA
  obtain ⟨q, hq, hq0, hqp, hprofile⟩ := hprofiles x
  have hvs : ∀ᵐ p ∂νin, p.1 ≤ s → combination S x p = 0 := by
    filter_upwards [coe_combination S x, ae_all_iff.mpr hSa] with p hp hpa ht
    rw [hp]
    exact Finset.sum_eq_zero (fun i _ ↦ by rw [hpa i ht, smul_zero])
  let qN : ℝ≥0 := Real.toNNReal (∫ r, q r ∂νt)
  have hqN : (qN : ℝ) = ∫ r, q r ∂νt := Real.coe_toNNReal _ (integral_nonneg hq0)
  have henergy : NativeEnergy.energy (combination S x) =ᵐ[μ] fun _ ↦ (qN : ℝ) := by
    rw [hqN]
    exact energy_of_profile (combination S x) q hprofile
  have hh := NativeGirsanovFullPast.characteristic_on_event P e s hsH u (combination S x)
    K hK hu hvs qN henergy A hA
  have hnorm : (qN : ℝ) = ‖combination S x‖ ^ 2 := by
    calc
      _ = ∫ ω, NativeEnergy.energy (combination S x) ω ∂μ := by
        rw [integral_congr_ae henergy]
        simp
      _ = _ := NativeEnergy.mean_eq _
  have hquad : (x ⬝ᵥ (gram ℝ S) *ᵥ x : ℝ) = ‖combination S x‖ ^ 2 := by
    simpa only [star_trivial, combination, real_inner_self_eq_norm_sq] using
      star_dotProduct_gram_mulVec S (fun i ↦ x i) (fun i ↦ x i)
  have hchar : charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (gram ℝ S)) x =
      (Real.exp (-(qN : ℝ) / 2) : ℂ) := by
    rw [charFun_multivariateGaussian (posSemidef_gram ℝ S), hquad, ← hnorm]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [neg_div]
  have hac : measure P e u ≪ μ := by
    unfold NativeGirsanovTilt.measure
    exact withDensity_absolutelyContinuous μ _
  have hlinear := hac.ae_eq (linear_projection P e u S x)
  calc
    _ = ∫ ω in A, Complex.exp ((shift P e u (combination S x) ω : ℂ) * Complex.I)
        ∂measure P e u :=
      integral_congr_ae ((hlinear.symm.mono fun ω hω ↦ congrArg
        (fun r : ℝ ↦ Complex.exp ((r : ℂ) * Complex.I)) hω).filter_mono ae_restrict_le)
    _ = _ := by rw [hh, hchar]

end SHEStochastic.NativeGirsanovVector
