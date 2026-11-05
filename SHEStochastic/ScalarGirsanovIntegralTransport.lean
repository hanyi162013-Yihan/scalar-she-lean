module

public import SHEStochastic.ScalarGirsanovCoordinateShift
public import SHEStochastic.NativeTransportLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovIntegralTransport
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure η] {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

omit [CompleteSpace C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] in
private theorem cross_zero (u : Lp C 2 νin) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    NativeCrossEnergy.cross (0 : Lp C 2 νin) u =ᵐ[μ] (fun _ => 0) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [NativeSimpleTransport.path_ae _ _ (Lp.coeFn_zero C 2 νin)] with ω hω
  change (∫ r, inner ℝ ((0 : Lp C 2 νin) (r,ω)) (u (r,ω))
    ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = 0
  apply integral_eq_zero_of_ae
  exact hω.mono fun r hr => by
    change inner ℝ ((0 : Lp C 2 νin) (r,ω)) (u (r,ω)) = 0
    change (0 : Lp C 2 νin) (r,ω) = 0 at hr
    rw [hr,inner_zero_left]

private theorem cross_add (v w u : Lp C 2 νin) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    NativeCrossEnergy.cross (v+w) u =ᵐ[μ]
      (fun ω => NativeCrossEnergy.cross v u ω+NativeCrossEnergy.cross w u ω) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have h := NativeCrossEnergy.cross_sub (v+w) v u
  simp only [add_sub_cancel_left] at h
  exact h.mono fun ω hω => by linarith

variable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (u : Process (E := C) F μ H) (R : FiniteScalarIto.Coordinates F η H ι)

def Agrees : Prop :=
  ∀ (i : ι) (t : ℝ≥0),t≤H → ∀ᵐ ω ∂μ,
    R.W i t ω=ScalarGirsanovCoordinateShift.shift (F := F) (μ := μ) (H := H) P e u i t ω

variable (hac : η ≪ μ)

local notation "U" => FiniteCylindricalIto.processTransport u

include hac in
private theorem simple (hR : @Agrees Ω C ι _ _ _ _ _ _ F μ η _ H P e u R) (V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    FiniteCylindricalIto.rawIntegral R e (FiniteCylindricalIto.simpleEmbedding (μ := η) e V) =ᵐ[η]
      (fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e
        (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V) ω +
          NativeCrossEnergy.cross (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V) U ω) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  induction V using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 η,hac.ae_eq (Lp.coeFn_zero ℝ 2 μ),hac.ae_eq (cross_zero U)]
      with ω hr hp hc
    rw [hr,hp,hc,add_zero]
  | single i v =>
    simp only [FiniteCylindricalIto.simpleEmbedding_single,
      FiniteCylindricalIto.rawIntegral_unit,FiniteScalarIto.rawIsometry_simple]
    filter_upwards [(FiniteScalarIto.memLp_simpleValue R i v).coeFn_toLp,
      hac.ae_eq (FiniteScalarIto.memLp_simpleValue P.toCoordinates i v).coeFn_toLp,
      hac.ae_eq (ScalarGirsanovCoordinateShift.scalar_simple P e u R hR i v)] with ω hr hp hs
    change FiniteScalarIto.simpleLp R i v ω = _ at hr
    change FiniteScalarIto.simpleLp P.toCoordinates i v ω = _ at hp
    rw [hr,hp]
    exact hs
  | add V W hV hW =>
    simp only [map_add]
    filter_upwards [Lp.coeFn_add
        (FiniteCylindricalIto.rawIntegral R e (FiniteCylindricalIto.simpleEmbedding (μ := η) e V))
        (FiniteCylindricalIto.rawIntegral R e (FiniteCylindricalIto.simpleEmbedding (μ := η) e W)),
      hac.ae_eq (Lp.coeFn_add
        (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V))
        (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding (μ := μ) e W))),
      hac.ae_eq (cross_add (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V)
        (FiniteCylindricalIto.simpleEmbedding (μ := μ) e W) U),hV,hW] with ω hr hp hc hv hw
    simp only [Pi.add_apply] at hr hp
    rw [hr,hp,hc,hv,hw]
    ring

include hac in
/-- Exact transport for every row in the original and changed input
spaces, after identification of the actual shifted coordinates. -/
theorem integral (hR : @Agrees Ω C ι _ _ _ _ _ _ F μ η _ H P e u R) (f : Lp C 2 νin) (g : Lp C 2 (FiniteScalarIto.inputMeasure F η H))
    (he : f =ᵐ[νin] g) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    FiniteCylindricalIto.rawIntegral R e g =ᵐ[η]
      (fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e f ω +
        NativeCrossEnergy.cross f U ω) :=
  NativeTransportLimit.of_simple P.toCoordinates R e U hac (simple P e u R hac hR) f g he

end SHEStochastic.ScalarGirsanovIntegralTransport
