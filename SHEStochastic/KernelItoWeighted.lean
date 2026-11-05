module

public import SHE.KernelItoLimit
public import SHE.PredictableExponential

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.KernelItoWeighted
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.KernelItoLimit SHE.HaarKernelL2Approximation
open scoped NNReal ENNReal Topology
variable {Ω C E A : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ] {H : ℝ≥0}
  (K : Model A C F μ H) (I : StandardTerminalIto (C := C) (E := E) F μ H)

/-- Exponential weighting is continuous in the original complete
predictable process norm, on every fixed finite horizon. -/
theorem scale_lipschitz (γ : ℝ) :
    LipschitzWith (Real.toNNReal (Real.exp (|γ| *(H : ℝ))))
      (PredictableExponential.scale (E := E) F μ H γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm,dist_eq_norm,← PredictableExponential.sub]
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(PredictableMultiplier.memLp F μ H (PredictableExponential.weight H γ)
    (PredictableExponential.predictable F H γ) (Real.exp (|γ| *(H : ℝ)))
    (PredictableExponential.bound H γ) (u-v)).coeFn_toLp] with p hp
  change ‖PredictableExponential.scale F μ H γ (u-v) p‖ ≤ _
  change PredictableExponential.scale F μ H γ (u-v) p=
    PredictableExponential.weight H γ p • (u-v) p at hp
  rw [hp,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (PredictableExponential.bound H γ p) (norm_nonneg _)

/-- Weighted finite-cell isometry, retaining the literal physical
observation time, even for two different adapted time grids. -/
theorem output_pair_energy (γ : ℝ) (a b : A) (n m : ℕ) :
    ENNReal.ofReal (‖PredictableExponential.scale F μ H γ
      (output K I a n-output K I b m)‖^2) =
      ∫⁻ p, ENNReal.ofReal (Real.exp (2*γ*(p.1 : ℝ))*
        ‖K.approx a n p-K.approx b m p‖^2) ∂measure μ H := by
  have hm : Measurable (fun p : ℝ≥0 × (ℝ≥0 × Ω) => ENNReal.ofReal
      (Real.exp (2*γ*(p.1 : ℝ))*‖K.approx a n p-K.approx b m p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((measurable_coe_nnreal_real.comp measurable_fst).const_mul (2*γ)).exp.mul
        (((K.approx_measurable a n).sub (K.approx_measurable b m)).norm.pow_const 2))
  rw [PredictableExponential.energy,triple_lintegral μ H hm]
  have hs := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim
    (Lp.coeFn_sub (output K I a n) (output K I b m)))
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem H,hs,
    PredictableItoCells.output_slice_ae I n (K.input a n) (K.input_stopped a n),
    PredictableItoCells.output_slice_ae I m (K.input b m) (K.input_stopped b m)] with t ht hs ha hb
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (2*γ*(t : ℝ))*
        ‖I.integral (K.input a n (ApproximationCells.index n t)) ω-
          I.integral (K.input b m (ApproximationCells.index m t)) ω‖^2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hs,ha,hb] with ω hs ha hb
      change output K I a n (t,ω)=_ at ha
      change output K I b m (t,ω)=_ at hb
      rw [hs,Pi.sub_apply,ha,hb]
    _ = ENNReal.ofReal (Real.exp (2*γ*(t : ℝ)))*
        ENNReal.ofReal (‖I.integral (K.input a n (ApproximationCells.index n t))-
          I.integral (K.input b m (ApproximationCells.index m t))‖^2) := by
      simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← LpEnergy.difference_energy]
    _ = ENNReal.ofReal (Real.exp (2*γ*(t : ℝ)))*
        (∫⁻ s, ∫⁻ ω, ENNReal.ofReal
          (‖K.input a n (ApproximationCells.index n t) (s,ω)-
            K.input b m (ApproximationCells.index m t) (s,ω)‖^2) ∂μ ∂timeMeasure H) := by
      rw [I.difference_energy]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [Measure.ae_ae_of_ae_prod (K.input_at a n t ht.1 ht.2),
        Measure.ae_ae_of_ae_prod (K.input_at b m t ht.1 ht.2)] with s hs hs'
      apply lintegral_congr_ae
      filter_upwards [hs,hs'] with ω hω hω'
      rw [hω,hω']

theorem pair_energy_tendsto (γ : ℝ) (a b : A) :
    Tendsto (fun n => ∫⁻ p, ENNReal.ofReal (Real.exp (2*γ*(p.1 : ℝ))*
      ‖K.approx a n p-K.approx b n p‖^2) ∂measure μ H) atTop
      (𝓝 (∫⁻ p, ENNReal.ofReal (Real.exp (2*γ*(p.1 : ℝ))*
        ‖K.raw a p-K.raw b p‖^2) ∂measure μ H)) := by
  let B : ℝ := Real.exp (2*|γ| *(H : ℝ))
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hm (a : A) : Measurable (fun p => ENNReal.ofReal (‖K.raw a p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((K.raw_measurable a).norm.pow_const 2)
  have hf : (∫⁻ p, ENNReal.ofReal (2*B)*
      (ENNReal.ofReal (‖K.raw a p‖^2)+ENNReal.ofReal (‖K.raw b p‖^2)) ∂measure μ H) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left (hm a)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
      ⟨(K.raw_energy_finite a).ne,(K.raw_energy_finite b).ne⟩)
  apply tendsto_lintegral_of_dominated_convergence
    (fun p => ENNReal.ofReal (2*B)*
      (ENNReal.ofReal (‖K.raw a p‖^2)+ENNReal.ofReal (‖K.raw b p‖^2)))
  · intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      (((measurable_coe_nnreal_real.comp measurable_fst).const_mul (2*γ)).exp.mul
        (((K.approx_measurable a n).sub (K.approx_measurable b n)).norm.pow_const 2))
  · intro n
    filter_upwards [K.approx_norm_le a n,K.approx_norm_le b n,
      Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p ha hb ht
    have htH : (p.1 : ℝ) ≤ H := by exact_mod_cast ht.2
    have hw : Real.exp (2*γ*(p.1 : ℝ)) ≤ B := Real.exp_le_exp.mpr
      ((mul_le_mul_of_nonneg_right (by linarith [le_abs_self γ] : 2*γ ≤ 2*|γ|) p.1.2).trans
        (mul_le_mul_of_nonneg_left htH (by positivity)))
    have hn : ‖K.approx a n p-K.approx b n p‖^2 ≤
        2*(‖K.raw a p‖^2+‖K.raw b p‖^2) := by
      nlinarith [norm_sub_le (K.approx a n p) (K.approx b n p),
        norm_nonneg (K.approx a n p-K.approx b n p),norm_nonneg (K.raw a p),
        norm_nonneg (K.raw b p),sq_nonneg (‖K.raw a p‖-‖K.raw b p‖)]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*B)]
    apply ENNReal.ofReal_le_ofReal
    exact ((mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right hw (by positivity))).trans_eq (by ring)
  · exact hf
  · filter_upwards [K.approx_tendsto a,K.approx_tendsto b] with p ha hb
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((ha.sub hb).norm.pow 2).const_mul (Real.exp (2*γ*(p.1 : ℝ))))

variable [CompleteSpace E]

/-- Exact weighted energy for any constructed predictable convolution.
The proof uses the existing cell approximation and ordinary Ito isometry;
it needs no continuous version, high moment assumption or extra input. -/
theorem difference_isometry (γ : ℝ) (a b : A) :
    ENNReal.ofReal (‖PredictableExponential.scale F μ H γ
      (convolution K I a-convolution K I b)‖^2) =
      ∫⁻ p, ENNReal.ofReal (Real.exp (2*γ*(p.1 : ℝ))*
        ‖K.raw a p-K.raw b p‖^2) ∂measure μ H := by
  have ht := (scale_lipschitz (F := F) (μ := μ) (H := H) (E := E) γ).continuous.tendsto
    (convolution K I a-convolution K I b)
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((ht.comp ((approximation_tendsto K I a).sub (approximation_tendsto K I b))).norm.pow 2)
  have hk := pair_energy_tendsto K γ a b
  have he (n : ℕ) := output_pair_energy K I γ a b n n
  simp_rw [← he] at hk
  exact tendsto_nhds_unique ho hk

end SHEStochastic.KernelItoWeighted
