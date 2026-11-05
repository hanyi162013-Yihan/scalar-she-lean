module

public import SHEStochastic.ScalarLinearGrowthGirsanov
public import SHEStochastic.ScalarCanonicalDensityLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarReverseDensity
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (u : Lp C 2 (FiniteScalarIto.inputMeasure F μ H))

local notation "Q" => NativeGirsanovTilt.measure P e u

/-- Recover the original measure from the drift-free changed law.
The reciprocal likelihood is the positive stochastic integral under
the shifted driver minus half the same control energy. -/
theorem inverse [IsProbabilityMeasure Q] (R : FiniteScalarIto.Family F Q H ι)
    (w : Lp C 2 (FiniteScalarIto.inputMeasure F Q H))
    (hu : u =ᵐ[FiniteScalarIto.inputMeasure F μ H] w)
    (hIto : FiniteCylindricalIto.rawIntegral R.toCoordinates e w =ᵐ[Q]
      fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω+NativeCrossEnergy.cross u u ω) :
    μ = (Q).withDensity (fun ω => ENNReal.ofReal (NativeExponential.density R e 1 w ω)) := by
  let f (ω : Ω) := ENNReal.ofReal (NativeExponential.density P e (-1) u ω)
  have hQ : Q ≪ μ := withDensity_absolutelyContinuous μ f
  have hi : FiniteScalarIto.inputMeasure F Q H ≪ FiniteScalarIto.inputMeasure F μ H := by
    simp only [NativeRowRepresentatives.inputMeasure_eq,energyMeasure]
    exact ((Measure.AbsolutelyContinuous.rfl : PredictableL2.timeMeasure H ≪ PredictableL2.timeMeasure H).prod hQ).trim _
  have he : NativeEnergy.energy w =ᵐ[Q] NativeEnergy.energy u :=
    NativeEnergy.energy_ae_of_ae w u (hi.ae_eq hu).symm
  have hc (ω : Ω) : NativeCrossEnergy.cross u u ω=NativeEnergy.energy u ω := by
    simp only [NativeCrossEnergy.cross,NativeEnergy.energy,real_inner_self_eq_norm_sq]
  have hD : (fun ω => ENNReal.ofReal (NativeExponential.density R e 1 w ω)) =ᵐ[Q]
      (fun ω => (f ω)⁻¹) := by
    filter_upwards [hIto,he] with ω hI hE
    dsimp only [f,NativeExponential.density]
    rw [hI,hE,hc]
    rw [←ENNReal.ofReal_inv_of_pos (Real.exp_pos _),←Real.exp_neg]
    congr 2
    ring
  have hf := (NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal
  rw [withDensity_congr_ae hD]
  symm
  exact withDensity_inv_same₀ hf.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
    (ae_of_all _ fun _ => ENNReal.ofReal_ne_top)

end SHEStochastic.ScalarReverseDensity
