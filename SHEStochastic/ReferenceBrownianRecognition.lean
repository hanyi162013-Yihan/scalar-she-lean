module

public import SHEStochastic.FiniteCharacteristicRecognition
public import SHEStochastic.FiniteIncrementLawComparison
public import SHEStochastic.NativeRandomInitialKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.ReferenceBrownianRecognition
open MeasureTheory ProbabilityTheory SHE Matrix
open scoped NNReal InnerProductSpace

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (W : ι → ℝ≥0 → Ω → ℝ)

def shortFiltration : Filtration (Set.Iic H) ‹MeasurableSpace Ω› :=
  ⟨fun t ↦ F t.val, fun _ _ h ↦ F.mono h, fun t ↦ F.le t.val⟩

variable {Ξ : Type*} [MeasurableSpace Ξ]
  (G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›) (ν : Measure Ξ) [IsProbabilityMeasure ν]
  (P : FiniteScalarIto.Family G ν H ι)

include P in
/-- A reference Brownian family supplies the finite Gaussian laws; the
comparison uses only equal increment laws and full-past independence.
In the unbounded argument this is the original given driver. -/
theorem finiteLaw (hW : ∀ i t, Measurable[F t] (W i t))
    (hzero : ∀ i, W i 0 =ᵐ[μ] fun _ ↦ (0 : ℝ))
    (hstep : ∀ n (a : Fin n → ι) (s t : ℝ≥0), s ≤ t → t ≤ H →
      HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ W (a i) t ω-W (a i) s ω))
        (multivariateGaussian (0 : WordRecursion.State n)
          (BrownianFiniteCovariance.matrix a (fun _ ↦ t-s))) μ ∧
      Indep (MeasurableSpace.comap (fun ω ↦ WithLp.toLp 2 (fun i ↦ W (a i) t ω-W (a i) s ω))
        (borel (WordRecursion.State n))) (F s) μ)
    {n : ℕ} (a : Fin n → ι) (times : Fin n → ℝ≥0) (htimes : ∀ i, times i ≤ H) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ W (a i) (times i) ω))
      (multivariateGaussian (0 : WordRecursion.State n) (BrownianFiniteCovariance.matrix a times)) μ := by
  classical
  let X := fun (t : Set.Iic H) ω ↦ WithLp.toLp 2 (fun i : Fin n ↦ W (a i) t.val ω)
  let Y := fun (t : Set.Iic H) ξ ↦ WithLp.toLp 2 (fun i : Fin n ↦ P.W (a i) t.val ξ)
  have hX (t : Set.Iic H) : Measurable[shortFiltration F H t] (X t) := by
    have hw (i : Fin n) := hW (a i) t.val
    letI : MeasurableSpace Ω := F t.val
    exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr hw)
  have hY (t : Set.Iic H) : Measurable[shortFiltration G H t] (Y t) := by
    have hw (i : Fin n) := P.adapted (a i) t.val
    letI : MeasurableSpace Ξ := G t.val
    exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr hw)
  have hzX : ∀ᵐ ω ∂μ, X ⊥ ω = 0 := by
    filter_upwards [ae_all_iff.mpr fun i : Fin n ↦ hzero (a i)] with ω hω
    exact PiLp.ext fun i ↦ hω i
  have hzY : ∀ᵐ ξ ∂ν, Y ⊥ ξ = 0 := by
    filter_upwards [ae_all_iff.mpr fun i : Fin n ↦ FiniteScalarIto.zero_ae P.toCoordinates (a i)] with ξ hξ
    exact PiLp.ext fun i ↦ hξ i
  have hRef (s t : Set.Iic H) (hst : s ≤ t) :
      HasLaw (fun ξ ↦ Y t ξ-Y s ξ)
        (multivariateGaussian (0 : WordRecursion.State n)
          (BrownianFiniteCovariance.matrix a (fun _ ↦ t.val-s.val))) ν := by
    have hh := BrownianShiftedFiniteLaw.law G ν H P.W P.law s.val (t.val-s.val)
      (by rw [add_tsub_cancel_of_le (show s.val ≤ t.val from hst)]; exact t.property)
      a (fun _ ↦ t.val-s.val) (fun _ ↦ le_rfl)
    simp only [add_tsub_cancel_of_le (show s.val ≤ t.val from hst)] at hh
    simpa only [Y, ← WithLp.toLp_sub, Pi.sub_def] using hh
  have hInc (s t : Set.Iic H) (hst : s ≤ t) :
      IdentDistrib (fun ω ↦ X t ω-X s ω) (fun ξ ↦ Y t ξ-Y s ξ) μ ν := by
    have hx := (hstep n a s.val t.val hst t.property).1
    have hy := hRef s t hst
    exact ⟨hx.aemeasurable, hy.aemeasurable, hx.map_eq.trans hy.map_eq.symm⟩
  let ti : Fin n → Set.Iic H := fun i ↦ ⟨times i, htimes i⟩
  let I := Finset.univ.image ti
  have hl := FiniteIncrementLawComparison.restrict_law μ (shortFiltration F H) X
    ν (shortFiltration G H) Y hX hY hzX hzY hInc
    (fun s t hst ↦ by
      simpa only [X, ← WithLp.toLp_sub, Pi.sub_def, shortFiltration, BorelSpace.measurable_eq] using
        (hstep n a s.val t.val hst t.property).2)
    (fun s t hst ↦ by
      simpa only [Y, ← WithLp.toLp_sub, Pi.sub_def, shortFiltration] using
        (P.law n a).2 s.val t.val hst t.property) I
  let obs : (I → WordRecursion.State n) → WordRecursion.State n :=
    fun f ↦ WithLp.toLp 2 (fun i ↦ f ⟨ti i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ i)
  have ho : Measurable obs := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply measurable_pi_iff.mpr
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp (measurable_pi_apply _)
  have he := hl.comp ho
  have href := (P.law n a).1 times htimes
  exact ⟨he.aemeasurable_fst, he.map_eq.trans href.map_eq⟩

/-- Assemble a complete native Brownian family from characteristic
martingales, using the original driver as the reference law only. -/
def family (hW : ∀ i t, Measurable[F t] (W i t))
    (hc : ∀ i ω, Continuous (fun t ↦ W i t ω))
    (hzero : ∀ i, W i 0 =ᵐ[μ] fun _ ↦ (0 : ℝ))
    (hChar : ∀ n (a : Fin n → ι) (r : WordRecursion.State n),
      Martingale (fun t ω ↦ Complex.exp
        (((FiniteCharacteristicRecognition.phase W a r (min t H) ω-
          FiniteCharacteristicRecognition.phase W a r 0 ω : ℝ) : ℂ)*Complex.I +
            (GaussianCharacteristicMartingale.variance a r * (min t H : ℝ≥0) : ℝ))) F μ) :
    FiniteScalarIto.Family F μ H ι := by
  refine ⟨⟨W, hW, ?_⟩, hc⟩
  intro n a
  refine ⟨fun times ht ↦ finiteLaw F μ H W G ν P hW hzero
    (fun n a s t hst ht ↦ FiniteCharacteristicRecognition.step F μ H W hW hChar a s t hst ht) a times ht, ?_⟩
  intro s t hst ht
  simpa only [BorelSpace.measurable_eq] using
    (FiniteCharacteristicRecognition.step F μ H W hW hChar a s t hst ht).2

end SHEStochastic.ReferenceBrownianRecognition
