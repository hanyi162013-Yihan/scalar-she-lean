module

public import SHEStochastic.NativeArbitraryLocalUniqueness
public import SHE.ConditionalCanonicalModelFamily
public import SHEStochastic.StandardBrownianItoConstruction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.NativeConditionalPacketModel
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩

variable (H : ℝ≥0) (D : SmoothApproximation.ScalarData)
  (ν : Measure (ConditionalCanonicalModelFamily.Space H)) [IsProbabilityMeasure ν] (u₀ : RealL2)
  (A : ConditionalCanonicalModelFamily.Packet H D ν u₀)
  (hLaw : ∀ n (a : Fin n → HaarNode), FiniteBrownianLawOn
    (ConditionalCanonicalModelFamily.filtration H) ν H
    (fun i ↦ CanonicalStateDriverFiltration.coordinate H (a i)) (fun i j ↦ if a i=a j then 1 else 0))

def family : FiniteScalarIto.Family (ConditionalCanonicalModelFamily.filtration H) ν H HaarNode where
  W := CanonicalStateDriverFiltration.coordinate H
  adapted := CanonicalStateDriverFiltration.coordinate_adapted H
  law := hLaw
  continuous := CanonicalStateDriverFiltration.coordinate_continuous H

/-- Retaining locality and the actual basis identities identifies every
possible conditional white-integral choice with the constructed native integral. -/
theorem white_eq : A.white = FiniteCylindricalIto.terminalIto (family H ν hLaw).toCoordinates NativeSingleNoiseBasis.basis := by
  apply StandardTerminalIto.ext_integral
  apply DFunLike.ext
  intro u
  exact NativeIntegralUniqueness.integral (family H ν hLaw) NativeSingleNoiseBasis.basis A.white A.locality A.basis_ids u

def whiteModel : NativeScalarModel.Model A.white :=
  ⟨HaarNode, inferInstance, inferInstance, family H ν hLaw, NativeSingleNoiseBasis.basis,
    white_eq H D ν u₀ A hLaw⟩

theorem physical_eq : NativeWhiteToPhysicalEquation.physical (ConditionalCanonicalModelFamily.filtration H) ν H A.white =
    restrictNoise A.white OriginalNativeFrozenRows.coordinates.symm.toLinearIsometry := by
  apply StandardTerminalIto.ext_integral
  apply DFunLike.ext
  intro u
  exact (NoiseRestrictionBounds.integral_eq_rotation A.white OriginalNativeFrozenRows.coordinates.symm.toLinearIsometry
    (OriginalNativeFrozenRows.coordinates.symm.continuous.measurable.comp measurable_snd) u).symm

/-- The original physical conditional equation has a native representation
without selecting another solution or another integral. -/
def physicalModel : NativeScalarModel.Model
    (NativeWhiteToPhysicalEquation.physical (ConditionalCanonicalModelFamily.filtration H) ν H A.white) := by
  rw [physical_eq H D ν u₀ A]
  exact NativeScalarModel.unitary (whiteModel H D ν u₀ A hLaw) OriginalNativeFrozenRows.coordinates.symm

end SHEStochastic.NativeConditionalPacketModel
