module

public import SHEStochastic.NativeProductIto
public import SHEStochastic.CylindricalProcessPullback
public import SHE.StandardIndependentProductIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeProductIto
open MeasureTheory SHE SHE.OrthogonalItoChannels
open scoped NNReal
variable {Ω Ξ ι C : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  [Countable ι] [DecidableEq ι] [Inhabited ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ} {H : ℝ≥0}

theorem fst_filtered (t : ℝ≥0) :
    @Measurable (IndependentNoiseCompletion.Space μ ν) Ω
      (IndependentNoiseCompletion.filtration μ ν F G t) (F t) Prod.fst :=
  (@measurable_fst Ω Ξ (F t) (G t)).mono le_sup_left le_rfl

theorem snd_filtered (t : ℝ≥0) :
    @Measurable (IndependentNoiseCompletion.Space μ ν) Ξ
      (IndependentNoiseCompletion.filtration μ ν F G t) (G t) Prod.snd :=
  (@measurable_snd Ω Ξ (F t) (G t)).mono le_sup_left le_rfl

variable (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
  (e : HilbertBasis ι ℝ C)

/-- Compatibility for every genuine original predictable L2 input,
expressed using exactly the old product-construction interface. -/
theorem firstCompatible : IndependentProductFirstCompatible F G μ ν H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (terminalIto P Q e) := by
  intro f g hg
  exact CylindricalPullback.process_naturality (Ξ := IndependentNoiseCompletion.Space μ ν) Prod.fst
    (IndependentNoiseCompletion.fst_preserving μ ν)
    (fun t ↦ fst_filtered (F := F) (G := G) (μ := μ) (ν := ν) t)
    P (ProductBrownianFiniteLaw.family P Q) e (ProductHilbertBasis.basis e)
    (left (C := C)) Sum.inl (fun i ↦ (ProductHilbertBasis.basis_inl e i).symm)
    (fun _ _ _ ↦ rfl) f g hg

theorem secondCompatible : IndependentProductSecondCompatible F G μ ν H
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e) (terminalIto P Q e) := by
  intro f g hg
  exact CylindricalPullback.process_naturality (Ξ := IndependentNoiseCompletion.Space μ ν) Prod.snd
    (IndependentNoiseCompletion.snd_preserving μ ν)
    (fun t ↦ snd_filtered (F := F) (G := G) (μ := μ) (ν := ν) t)
    Q (ProductBrownianFiniteLaw.family P Q) e (ProductHilbertBasis.basis e)
    (right (C := C)) Sum.inr (fun i ↦ (ProductHilbertBasis.basis_inr e i).symm)
    (fun _ _ _ ↦ rfl) f g hg

/-- The complete independent-product interface for the constructed native
cylindrical maps. The witness uses the actual completed product measure,
and both channels retain their original integrals for all L2 inputs. -/
theorem standardIndependentProductIto : StandardIndependentProductIto F G μ ν H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.terminalIto Q.toCoordinates e) :=
  ⟨terminalIto P Q e, firstCompatible P Q e, secondCompatible P Q e, pastLocality P Q e⟩

end SHEStochastic.NativeProductIto
