module

public import SHEStochastic.BrownianCoordinateVersions
public import SHEStochastic.NativeChangedCoordinates
public import SHEStochastic.NativeRecognizedHilbertBDG
public import SHEStochastic.NativeIntegralUniqueness
public import SHEStochastic.TerminalItoExt
public import SHE.StandardChangedHilbertBDG
public import SHE.GirsanovRawCoordinates
public import SHE.GirsanovPastLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.NativeChangedHilbertBDG
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.OrthogonalItoChannels
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- Recast the already constructed drift-shifted coordinates on the
given equal changed measure, without changing their pointwise values. -/
def coordinates (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (hu : ∀ᵐ sample ∂μ, StochasticExponential.bracket F μ H u sample ≤ 1)
    (Q : Measure Ω) (hQ : Q = NativeChangedCoordinates.changedMeasure P e u) :
    FiniteScalarIto.Coordinates F Q H ι where
  W i := girsanovShift u (RawCylindricalCoordinates.row F μ H (e : ι → C) i) (P.W i)
  adapted := (NativeChangedCoordinates.coordinates P e u hu).adapted
  law n a := by
    have hh := (NativeChangedCoordinates.coordinates P e u hu).law n a
    change FiniteBrownianLawOn F (NativeChangedCoordinates.changedMeasure P e u) H
      (fun i ↦ girsanovShift u (RawCylindricalCoordinates.row F μ H (e : ι → C) (a i)) (P.W (a i)))
      (fun i j ↦ if a i = a j then 1 else 0) at hh
    rw [← hQ] at hh
    exact hh

/-- A supplied genuine Girsanov transport witness determines its
changed integral on every predictable L2 input. The changed Brownian
family and all Hilbert BDG estimates are derived from native tools. -/
theorem standard {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ (Both RealHaarInput)) :
    StandardChangedHilbertBDG F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  letI : SecondCountableTopology (Both RealHaarInput) := e.repr.toHomeomorph.secondCountableTopology
  intro Q hprob K T hac hrev hn hl hp hH1 hcap hQ
  have hnQ : NullCompleteFiltration.ContainsNullSets F Q := fun t A hA ↦ hn t A (hac hA)
  have heQ : Q = NativeChangedCoordinates.changedMeasure P e T.control := hQ
  let R := coordinates P e T.control hcap Q heQ
  let S := BrownianCoordinateVersions.family R hp hH1 hnQ
  have hJ := NativeScalarBDG.scalarBDG16 P e
  have hcoord (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
      RawCylindricalCoordinates.value F Q H (e : ι → Both RealHaarInput) K i t =ᵐ[Q] S.W i t := by
    have hh := GirsanovRawCoordinates.coordinate_ae F μ H (e : ι → Both RealHaarInput) e.orthonormal
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) Q K T hac hrev
      (NativeScalarBDG.constant 3) hJ hH1 hp i t
    have ho := (RawCylindricalCoordinates.continuous_ae F μ H (e : ι → Both RealHaarInput) e.orthonormal
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) (NativeScalarBDG.constant 3) hJ hH1 hp i t).trans
        (FiniteCylindricalIto.coordinate_integral P e i t ht)
    have hv := BrownianCoordinateVersions.version_ae R hp hH1 i t
    filter_upwards [hh, hrev.ae_le ho, hv] with sample hh ho hv
    rw [hh]
    change _ = BrownianCoordinateVersions.version R i t sample
    rw [hv, min_eq_left ht]
    change RawCylindricalCoordinates.continuous F μ H (e : ι → Both RealHaarInput)
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) i t sample + _ = P.W i t sample + _
    rw [ho]
  have hk := GirsanovPastLocality.locality F Q H μ
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) K T hac hrev hl
  have heK : K = FiniteCylindricalIto.terminalIto S.toCoordinates e := by
    apply StandardTerminalIto.ext_integral
    apply DFunLike.ext
    intro u
    exact NativeIntegralUniqueness.integral S e K hk hcoord u
  rw [heK]
  exact NativeRecognizedHilbertBDG.standardRecognizedHilbertBDG S e

end SHEStochastic.NativeChangedHilbertBDG
