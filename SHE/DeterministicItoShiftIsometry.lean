module
public import SHE.DeterministicItoShiftInput
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable{Ω C:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[SFinite μ]
variable(H v h:ℝ≥0)(hvh:v+h≤H)
include hvh

omit hvh in
theorem extend_add(f g:ℝ≥0×Ω→C):
    extend v h (fun p=>f p+g p)=(fun p=>extend v h f p+extend v h g p):=by
  funext p
  unfold extend
  split_ifs <;> simp

omit hvh in
theorem extend_smul(r:ℝ)(f:ℝ≥0×Ω→C):
    extend v h (fun p=>r • f p)=(fun p=>r • extend v h f p):=by
  funext p
  unfold extend
  split_ifs <;> simp

omit hvh in
theorem process_product_energy(f:Process (E:=C) 𝓕 μ H):
    ENNReal.ofReal (‖f‖^2)=∫⁻p,ENNReal.ofReal (‖f p‖^2) ∂energyMeasure μ H:=by
  rw [process_lintegral_energy]
  exact (lintegral_prod _ (ENNReal.measurable_ofReal.comp
    (((Lp.stronglyMeasurable f).mono (predictable_le_product 𝓕)).measurable.norm.pow_const 2)).aemeasurable).symm

theorem input_norm(f:Process (E:=C) (filtration 𝓕 v) μ h):
    ‖input 𝓕 μ H v h hvh f‖=‖f‖:=by
  have he:ENNReal.ofReal (‖input 𝓕 μ H v h hvh f‖^2)=ENNReal.ofReal (‖f‖^2):=by
    rw [process_product_energy 𝓕 μ H,process_product_energy (filtration 𝓕 v) μ h]
    calc
      _=∫⁻p,ENNReal.ofReal (‖extend v h f p‖^2) ∂energyMeasure μ H:=by
        apply lintegral_congr_ae
        filter_upwards [input_ae 𝓕 μ H v h hvh f] with p hp
        rw [hp]
      _=_:=extend_energy 𝓕 μ H v h hvh (Lp.stronglyMeasurable f).measurable
  have hs:‖input 𝓕 μ H v h hvh f‖^2=‖f‖^2:=
    (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp he
  nlinarith [norm_nonneg (input 𝓕 μ H v h hvh f),norm_nonneg f]

/-- The literal zero extension is an isometry of the ORIGINAL
predictable input spaces, with no conditional integral premise. -/
def inputIsometry:Process (E:=C) (filtration 𝓕 v) μ h→ₗᵢ[ℝ]Process (E:=C) 𝓕 μ H where
  toFun:=input 𝓕 μ H v h hvh
  map_add' f g:=by
    apply PastItoAlgebra.eq_of_ambient_ae
    have he:=extend_ae 𝓕 μ H v h hvh (Lp.stronglyMeasurable (f+g)).measurable
      ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)).measurable
      (ae_eq_of_ae_eq_trim (Lp.coeFn_add f g))
    filter_upwards [input_ae 𝓕 μ H v h hvh (f+g),input_ae 𝓕 μ H v h hvh f,
      input_ae 𝓕 μ H v h hvh g,ae_eq_of_ae_eq_trim (Lp.coeFn_add
        (input 𝓕 μ H v h hvh f) (input 𝓕 μ H v h hvh g)),he] with p ha hf hg ho hi
    rw [ha,ho]
    simp only [Pi.add_apply]
    rw [hf,hg,hi]
    exact congrFun (extend_add (v:=v) (h:=h) f g) p
  map_smul' r f:=by
    apply PastItoAlgebra.eq_of_ambient_ae
    have he:=extend_ae 𝓕 μ H v h hvh (Lp.stronglyMeasurable (r • f)).measurable
      ((Lp.stronglyMeasurable f).const_smul r).measurable
      (ae_eq_of_ae_eq_trim (Lp.coeFn_smul r f))
    filter_upwards [input_ae 𝓕 μ H v h hvh (r • f),input_ae 𝓕 μ H v h hvh f,
      ae_eq_of_ae_eq_trim (Lp.coeFn_smul r (input 𝓕 μ H v h hvh f)),he] with p ha hf ho hi
    simp only [RingHom.id_apply] at *
    rw [ha,ho]
    simp only [Pi.smul_apply]
    rw [hf,hi]
    exact congrFun (extend_smul (v:=v) (h:=h) r f) p
  norm_map':=input_norm 𝓕 μ H v h hvh

end SHE.DeterministicItoShift
