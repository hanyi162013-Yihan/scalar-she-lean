module

public import SHEStochastic.NativeUniformFourierMixed
public import SHEStochastic.NativeClippedBrownian
public import SHEStochastic.LinearHeatMaximumMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.NativeDriverPathMoments
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting PastedLinearHeatFunctional
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩


variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (K : ℝ≥0) (hK : K ≤ H) (X : Ω → Path K (JointStateDriverPath.State RealL2 ι)) (i : ι)
  (hread : ∀ (t : Time K) (ω : Ω), value K (NativeUniformFourierMixed.driverRow i) 0 (X ω) t =
    P.W i (AdaptedCanonicalPathTests.toNN K t) ω-P.W i 0 ω)

include hread in
theorem value_eq (q : ℝ≥0) (ω : Ω) :
    value K (NativeUniformFourierMixed.driverRow i) 0 (X ω) (AdaptedCanonicalPathTests.clock K q) =
      NativeClippedBrownian.value P K i q ω := by
  rw [hread, AdaptedCanonicalPathTests.toNN_clock]
  rfl

include hK hread e in
theorem martingale : Martingale
    (fun q ω ↦ value K (NativeUniformFourierMixed.driverRow i) 0 (X ω) (AdaptedCanonicalPathTests.clock K q)) F μ := by
  simpa only [value_eq F μ H P K X i hread] using NativeClippedBrownian.martingale P e K hK i

include hK hread in
theorem subgaussian (q : ℝ≥0) : HasSubgaussianMGF
    (fun ω ↦ value K (NativeUniformFourierMixed.driverRow i) 0 (X ω) (AdaptedCanonicalPathTests.clock K q)) (min q K) μ := by
  simpa only [value_eq F μ H P K X i hread] using NativeClippedBrownian.subgaussian P K hK i q

include hK hread e in
theorem fourth_bound : (∫⁻ ω, ENNReal.ofReal ((envelope K (NativeUniformFourierMixed.driverRow i) 0 (X ω))^4) ∂μ) ≤
    LinearHeatMaximumMoments.fourthConstant K := by
  apply LinearHeatMaximumMoments.fourth_bound K (NativeUniformFourierMixed.driverRow i) 0 μ F X
    (martingale F μ H P e K hK X i hread)
  · intro q
    simpa using (subgaussian F μ H P K hK X i hread q).memLp (4 : ℝ≥0)
  · simpa only [min_self] using subgaussian F μ H P K hK X i hread K

include hK hread e in
theorem envelope_memLp (hX : Measurable X) :
    MemLp (fun ω ↦ envelope K (NativeUniformFourierMixed.driverRow i) 0 (X ω)) 4 μ := by
  apply LinearHeatMaximumMoments.envelope_memLp K (NativeUniformFourierMixed.driverRow i) 0 μ F X hX
    (martingale F μ H P e K hK X i hread)
  · intro q
    simpa using (subgaussian F μ H P K hK X i hread q).memLp (4 : ℝ≥0)
  · simpa only [min_self] using subgaussian F μ H P K hK X i hread K

end SHEStochastic.NativeDriverPathMoments
