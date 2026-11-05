module

public import SHEStochastic.SimplePullback
public import SHEStochastic.FiniteCylindricalSimple

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FilteredPullback
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω Ξ E E' : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ) (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π)

theorem input_lift (L : E →ₗᵢ[ℝ] E') (f : Lp E 2 (FiniteScalarIto.inputMeasure F μ H)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
    input π hπ hfil (L2HilbertSum.lift (FiniteScalarIto.inputMeasure F μ H) L f) =
      L2HilbertSum.lift (FiniteScalarIto.inputMeasure G ν H) L (input π hπ hfil f) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  apply Lp.ext
  filter_upwards [input_ae π hπ hfil (L2HilbertSum.lift (FiniteScalarIto.inputMeasure F μ H) L f),
    (input_preserving π hπ hfil).quasiMeasurePreserving.ae
      (L2HilbertSum.lift_ae (FiniteScalarIto.inputMeasure F μ H) L f),
    L2HilbertSum.lift_ae (FiniteScalarIto.inputMeasure G ν H) L (input π hπ hfil f),
    input_ae π hπ hfil f] with p h1 h2 h3 h4
  rw [h1, h2, h3, h4]

end SHEStochastic.FilteredPullback

namespace SHEStochastic.CylindricalPullback
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω Ξ ι κ C D : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}

theorem lift_unit {X : Type*} [MeasurableSpace X] (η : Measure X)
    (L : C →ₗᵢ[ℝ] D) (e : HilbertBasis ι ℝ C) (b : HilbertBasis κ ℝ D)
    (i : ι) (j : κ) (hb : L (e i) = b j) (f : Lp ℝ 2 η) :
    L2HilbertSum.lift η L (L2HilbertSum.lift η (ColumnsHilbertSum.unit e i) f) =
      L2HilbertSum.lift η (ColumnsHilbertSum.unit b j) f := by
  apply Lp.ext
  filter_upwards [L2HilbertSum.lift_ae η L (L2HilbertSum.lift η (ColumnsHilbertSum.unit e i) f),
    L2HilbertSum.lift_ae η (ColumnsHilbertSum.unit e i) f,
    L2HilbertSum.lift_ae η (ColumnsHilbertSum.unit b j) f] with x h1 h2 h3
  rw [h1, h2, h3]
  simp only [ColumnsHilbertSum.unit, LinearIsometry.toSpanSingleton_apply]
  rw [map_smul, hb]

/-- Cylindrical integral naturality for an isometric noise-channel
embedding and a probability/filtration pullback. One dense-simple proof
handles both channels of the independent product construction. -/
theorem integral_naturality
    (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ) (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π)
    (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H κ)
    (e : HilbertBasis ι ℝ C) (b : HilbertBasis κ ℝ D) (L : C →ₗᵢ[ℝ] D)
    (σ : ι → κ) (hb : ∀ i, L (e i) = b (σ i))
    (hW : ∀ i t ξ, Q.W (σ i) t ξ = P.W i t (π ξ))
    (v : Lp C 2 (FiniteScalarIto.inputMeasure F μ H)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
    FiniteCylindricalIto.rawIntegral Q.toCoordinates b
      (L2HilbertSum.lift (FiniteScalarIto.inputMeasure G ν H) L (FilteredPullback.input π hπ hfil v)) =
      FilteredPullback.output π hπ (FiniteCylindricalIto.rawIntegral P.toCoordinates e v) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  let A := (FiniteCylindricalIto.rawIntegral Q.toCoordinates b).comp
    ((L2HilbertSum.lift (FiniteScalarIto.inputMeasure G ν H) L).comp (FilteredPullback.input π hπ hfil))
  let B := (FilteredPullback.output π hπ).comp (FiniteCylindricalIto.rawIntegral P.toCoordinates e)
  have hs (V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
      A (FiniteCylindricalIto.simpleEmbedding e V) = B (FiniteCylindricalIto.simpleEmbedding e V) := by
    induction V using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add v u hv hu => rw [map_add, map_add, map_add, hv, hu]
    | single i V =>
        rw [FiniteCylindricalIto.simpleEmbedding_single]
        change FiniteCylindricalIto.rawIntegral Q.toCoordinates b
          (L2HilbertSum.lift (FiniteScalarIto.inputMeasure G ν H) L
            (FilteredPullback.input π hπ hfil
              (L2HilbertSum.lift (FiniteScalarIto.inputMeasure F μ H) (ColumnsHilbertSum.unit e i)
                (FiniteScalarIto.embedding F μ H V)))) =
          FilteredPullback.output π hπ (FiniteCylindricalIto.rawIntegral P.toCoordinates e
            (L2HilbertSum.lift (FiniteScalarIto.inputMeasure F μ H) (ColumnsHilbertSum.unit e i)
              (FiniteScalarIto.embedding F μ H V)))
        rw [FilteredPullback.input_lift, lift_unit _ L e b i (σ i) (hb i),
          FiniteCylindricalIto.rawIntegral_unit, FiniteCylindricalIto.rawIntegral_unit]
        exact FilteredPullback.rawIsometry_naturality π hfil hπ P Q i (σ i) (hW i) _
  exact congrFun (DenseRange.equalizer (FiniteCylindricalIto.simpleEmbedding_dense e)
    A.continuous B.continuous (funext hs)) v

end SHEStochastic.CylindricalPullback
