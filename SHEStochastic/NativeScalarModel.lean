module

public import SHEStochastic.NativeNoiseEquivalence
public import SHEStochastic.NativePredictableRotation
public import SHEStochastic.NativeProductIdentification
public import SHEStochastic.NativeScalarBDG
public import SHEStochastic.NativeScalarBDGAll
public import SHEStochastic.NativeFiniteIto
public import SHEStochastic.NativeTerminalLevy
public import SHEStochastic.NativeTerminalNovikov
public import SHEStochastic.NativeTerminalGirsanovTransport
public import SHEStochastic.FiniteCylindricalParameterVersions
public import SHEStochastic.CountableHilbertBasis

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.NativeScalarModel
open MeasureTheory SHE SHE.PredictableL2 SHE.OrthogonalItoChannels
open scoped NNReal ENNReal

variable {Ω C : Type} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- A chosen terminal integral is represented by an actual countable
Brownian family. This stores a representation, not an extra theorem. -/
structure Model (J : StandardTerminalIto (C := C) (E := ℝ) F μ H) where
  index : Type
  countable : Countable index
  decidable : DecidableEq index
  family : @FiniteScalarIto.Family Ω _ F μ H index decidable
  basis : HilbertBasis index ℝ C
  identifies : letI := countable; letI := decidable
    J = FiniteCylindricalIto.terminalIto family.toCoordinates basis

attribute [instance] Model.countable Model.decidable

variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {J : StandardTerminalIto (C := C) (E := ℝ) F μ H}

/-- The source representation is immediate for a native integral. -/
def ofFamily {ι : Type} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) :
    Model (FiniteCylindricalIto.terminalIto P.toCoordinates e) := ⟨ι, inferInstance, inferInstance, P, e, rfl⟩

/-- Exact recasting of filtration and horizon preserves the representation. -/
def recast (M : Model J) {G : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {K : ℝ≥0}
    (hF : G=F) (hH : K=H) (J' : StandardTerminalIto (C := C) (E := ℝ) G μ K)
    (hJ : HEq J' J) : Model J' := by
  subst G
  subst K
  cases eq_of_heq hJ
  exact M

variable {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

/-- A constant unitary only changes the stored noise basis. -/
def unitary (M : Model J) (L : A ≃ₗᵢ[ℝ] C) : Model (restrictNoise J L.toLinearIsometry) := by
  refine ⟨M.index, inferInstance, inferInstance, M.family, NativeNoiseEquivalence.basis L M.basis, ?_⟩
  exact (congrArg (fun K ↦ restrictNoise K L.toLinearIsometry) M.identifies).trans
    (NativeNoiseEquivalence.integral_eq M.family L M.basis)

/-- Predictable isometric rotation reuses the constructed rotated
Brownian family and the integral uniqueness theorem. -/
def rotated (M : Model J) (Φ : ℝ≥0 × Ω → A →ₗᵢ[ℝ] C)
    (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
      (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p ↦ Φ p.1 p.2))
    (hn : NullCompleteFiltration.ContainsNullSets F μ) :
    Model (PredictableItoRotation.integral F μ H Φ hΦ J) := by
  let hb := exists_hilbertBasis (𝕜 := ℝ) (E := A)
  let κ := Classical.choose hb
  let b : HilbertBasis κ ℝ A := Classical.choose (Classical.choose_spec hb)
  letI : Countable κ := hilbertBasis_countable b
  classical
  let hRot := NativePredictableRotation.exists_family M.family M.basis b Φ hΦ hn
  let Q := Classical.choose hRot
  have hQ := Classical.choose_spec hRot
  refine ⟨κ, inferInstance, inferInstance, Q, b, ?_⟩
  rw [M.identifies]
  apply StandardTerminalIto.ext_integral
  apply DFunLike.ext
  intro u
  exact (hQ u).symm

theorem index_nonempty [Nontrivial C] (M : Model J) : Nonempty M.index := by
  by_contra h
  letI : IsEmpty M.index := not_nonempty_iff.mp h
  obtain ⟨x, hx⟩ := exists_ne (0 : C)
  have he : M.basis.repr x = 0 := by ext i; exact isEmptyElim i
  exact hx (M.basis.repr.injective (he.trans (map_zero M.basis.repr).symm))

/-- An arbitrary coherent choice of self-product has the native product
representation, including the actual completed measure and filtration. -/
def selfProduct [Nontrivial C] (M : Model J)
    (B : IndependentProductItoData F F μ μ H J J) : Model B.integral := by
  letI : Nonempty M.index := index_nonempty M
  letI : Inhabited M.index := Classical.inhabited_of_nonempty (index_nonempty M)
  have hHelper {ι : Type} [Countable ι] [DecidableEq ι] [Inhabited ι]
      (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
      (K : StandardTerminalIto (C := C) (E := ℝ) F μ H)
      (he : K=FiniteCylindricalIto.terminalIto P.toCoordinates e)
      (B : IndependentProductItoData F F μ μ H K K) :
      B.integral = NativeProductIto.terminalIto P P e := by
    subst K
    exact NativeProductIdentification.integral_eq P P e B
  have hEq := hHelper M.family M.basis J M.identifies B
  refine ⟨Sum M.index M.index, inferInstance, inferInstance, ProductBrownianFiniteLaw.family M.family M.family,
    ProductHilbertBasis.basis M.basis, hEq⟩

theorem products [Nontrivial C] (M : Model J) : StandardIndependentProductIto F F μ μ H J J := by
  letI : Nonempty M.index := index_nonempty M
  letI : Inhabited M.index := Classical.inhabited_of_nonempty (index_nonempty M)
  rw [M.identifies]
  exact NativeProductIto.standardIndependentProductIto M.family M.family M.basis

theorem locality (M : Model J) : StandardTerminalPastLocality J := by
  rw [M.identifies]
  exact FiniteCylindricalIto.pastLocality M.family M.basis

theorem finiteIto (M : Model J) : StandardFiniteIto.Universal F μ H J := by
  rw [M.identifies]
  exact NativeFiniteIto.standardFiniteIto M.family M.basis

theorem fubini (M : Model J) : StandardItoStoppedParameterFubini J := by
  rw [M.identifies]
  exact FiniteCylindricalIto.stoppedParameterFubini M.family M.basis

theorem novikov (M : Model J) : StandardTerminalNovikov J := by
  rw [M.identifies]
  exact NativeTerminalNovikov.standardTerminalNovikov M.family M.basis

theorem girsanov (M : Model J) : StandardTerminalGirsanov J := by
  rw [M.identifies]
  exact NativeTerminalGirsanovTransport.standardTerminalGirsanov M.family M.basis

theorem levy (M : Model J) : StandardTerminalLevy J := by
  rw [M.identifies]
  exact NativeTerminalLevy.standardTerminalLevy M.family M.basis

theorem bdg16 (M : Model J) : StandardTerminalBDG16 J (NativeScalarBDG.constant 3) := by
  rw [M.identifies]
  exact NativeScalarBDG.scalarBDG16 M.family M.basis

theorem bdg (M : Model J) (p : ℕ) (hp : 0<p) :
    StandardTerminalBDGPower p J (NativeScalarBDGAll.constant p) := by
  rw [M.identifies]
  exact NativeScalarBDGAll.power M.family M.basis p hp

end SHEStochastic.NativeScalarModel
