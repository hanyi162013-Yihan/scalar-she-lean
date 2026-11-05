module

public import SHE.OrthogonalItoChannels
public import SHE.RotatedItoAlgebra
public import SHE.StandardFiniteIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.TwoChannelItoRows
open MeasureTheory Set PredictableL2 PredictableItoRotation OrthogonalItoChannels StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
local instance : MeasurableSpace (Both C) := borel _
local instance : BorelSpace (Both C) := ⟨rfl⟩
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)

def block (v w : Process (E := C) 𝓕 μ h) : Process (E := Both C) 𝓕 μ h :=
  processIsometry 𝓕 μ h (fun _ => left (C := C)) (left_measurable 𝓕) v+
    processIsometry 𝓕 μ h (fun _ => right (C := C)) (right_measurable 𝓕) w

theorem block_ae (v w : Process (E := C) 𝓕 μ h) :
    block 𝓕 μ h v w=ᵐ[energyMeasure μ h] (fun p => WithLp.toLp 2 (v p,w p)) := by
  have ha := ae_eq_of_ae_eq_trim (Lp.coeFn_add
    (processIsometry 𝓕 μ h (fun _ => left (C := C)) (left_measurable 𝓕) v)
    (processIsometry 𝓕 μ h (fun _ => right (C := C)) (right_measurable 𝓕) w))
  filter_upwards [ha,processIsometry_ae 𝓕 μ h (fun _ => left (C := C)) (left_measurable 𝓕) v,
    processIsometry_ae 𝓕 μ h (fun _ => right (C := C)) (right_measurable 𝓕) w] with p hp hl hr
  dsimp only [block]
  rw [hp]
  change processIsometry 𝓕 μ h (fun _ => left (C := C)) (left_measurable 𝓕) v p+
    processIsometry 𝓕 μ h (fun _ => right (C := C)) (right_measurable 𝓕) w p=_
  rw [hl,hr]
  apply WithLp.ofLp_injective
  ext <;> simp [left,right]

theorem stop_add (t : ℝ) (v w : Process (E := C) 𝓕 μ h) :
    stop 𝓕 μ h t (v+w)=stop 𝓕 μ h t v+stop 𝓕 μ h t w := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hi := ae_eq_of_ae_eq_trim (Lp.coeFn_add v w)
  have ho := ae_eq_of_ae_eq_trim (Lp.coeFn_add (stop 𝓕 μ h t v) (stop 𝓕 μ h t w))
  filter_upwards [stop_ae 𝓕 μ h t (v+w),stop_ae 𝓕 μ h t v,stop_ae 𝓕 μ h t w,hi,ho] with p hp hv hw hvi hvo
  rw [hp,hvo]
  simp only [Pi.add_apply]
  rw [hv,hw]
  by_cases hm : p ∈ before (Ω := Ω) t
  · simp only [Set.indicator_of_mem hm,hvi,Pi.add_apply]
  · simp only [Set.indicator_of_notMem hm,zero_add]

theorem stop_block (t : ℝ) (v w : Process (E := C) 𝓕 μ h) :
    stop 𝓕 μ h t (block 𝓕 μ h v w)=block 𝓕 μ h (stop 𝓕 μ h t v) (stop 𝓕 μ h t w) := by
  rw [block,stop_add,← RotatedItoAlgebra.map_stop,← RotatedItoAlgebra.map_stop]
  rfl

theorem integral_block (J : StandardTerminalIto (C := Both C) (E := ℝ) 𝓕 μ h)
    (v w : Process (E := C) 𝓕 μ h) :
    J.integral (block 𝓕 μ h v w)=
      (leftIntegral 𝓕 μ h J).integral v+(rightIntegral 𝓕 μ h J).integral w := by
  rw [block,map_add]
  rfl

theorem integral_stop_block_ae (J : StandardTerminalIto (C := Both C) (E := ℝ) 𝓕 μ h)
    (t : ℝ) (v w : Process (E := C) 𝓕 μ h) :
    J.integral (stop 𝓕 μ h t (block 𝓕 μ h v w))=ᵐ[μ]
      (fun ω => (leftIntegral 𝓕 μ h J).integral (stop 𝓕 μ h t v) ω+
        (rightIntegral 𝓕 μ h J).integral (stop 𝓕 μ h t w) ω) := by
  rw [stop_block,integral_block]
  exact Lp.coeFn_add _ _

theorem rowCovariance_sum_ae_real [IsProbabilityMeasure μ] {n : ℕ}
    (R S : Fin n → Process (E := C) 𝓕 μ h) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ h (fun i => block 𝓕 μ h (R i) (S i)) ω t=
        StandardFiniteIto.rowCovariance 𝓕 μ h R ω t+StandardFiniteIto.rowCovariance 𝓕 μ h S ω t := by
  have hb : ∀ᵐ p ∂energyMeasure μ h,∀ i,block 𝓕 μ h (R i) (S i) p=WithLp.toLp 2 (R i p,S i p) :=
    ae_all_iff.mpr (fun i => block_ae 𝓕 μ h (R i) (S i))
  have hp : ∀ᵐ p ∂energyMeasure μ h,
      StandardFiniteIto.rowCovariance 𝓕 μ h (fun i => block 𝓕 μ h (R i) (S i)) p.2 (p.1:ℝ)=
        StandardFiniteIto.rowCovariance 𝓕 μ h R p.2 (p.1:ℝ)+
          StandardFiniteIto.rowCovariance 𝓕 μ h S p.2 (p.1:ℝ) := by
    filter_upwards [hb] with p hp
    ext i j
    simp only [Matrix.add_apply,StandardFiniteIto.rowCovariance,Real.toNNReal_coe]
    simp only [hp,WithLp.prod_inner_apply]
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  rw [← timeMeasure_map h]
  apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
  simpa only [Real.toNNReal_coe,Prod.swap] using hω

end SHE.TwoChannelItoRows
