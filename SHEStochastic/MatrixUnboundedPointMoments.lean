module

public import SHEStochastic.MatrixUnboundedHeatRows
public import SHEStochastic.MatrixPointSquareEnergy
public import SHEStochastic.NativeMatrixEquation
public import SHEStochastic.SublinearHeatFiniteHorizon
public import SHEStochastic.NativeScalarBDGAll

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixUnboundedPointMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
variable {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)

/-- The actual nonlinear Haar observation row is bounded by its
original-square sublinear heat energy, with the exact native circle. -/
theorem row_energy (R : ℝ≥0) (p : ℝ≥0×Ω) (τ : ℝ) (x : HeatCircle) (i : Fin n) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row τ (NativeMatrixEquation.profile F (G_R R) U hU p) x i‖^2) ≤
      SublinearHeatIntegratedEnergy.rowEnergy (G_R R).value (VectorNativeHeatEndpoint.push (U p)) x τ := by
  have hb := MatrixPointSquareEnergy.native_bound (NativeMatrixEquation.data F (G_R R) U hU p)
    (G_R R).value (U p) (NativeMatrixEquation.coefficient_ae F (G_R R) U hU p) τ x i
  by_cases ht : 0<τ
  · apply hb.trans_eq
    simp only [SublinearHeatIntegratedEnergy.rowEnergy,dite_eq_left ht]
    apply lintegral_congr
    intro y
    rw [RealCausalHeatKernel.square ht x y]
  · simp only [SublinearHeatIntegratedEnergy.rowEnergy,dite_eq_right ht,MatrixPointHeatRows.row,if_neg ht,
      norm_zero,zero_pow (by norm_num : 2≠0),ENNReal.ofReal_zero,le_refl]

/-- Common finite-horizon bracket cap: no coefficient truncation radius
appears. K bounds the spatial L2 state along the localized history. -/
def cap (K : ℝ) (T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2*(‖G 0‖+(C : ℝ))^2*SublinearHeatFiniteHorizon.constant (T : ℝ)^(1+(β : ℝ)))*
    SublinearHeatIntegratedEnergy.stateFactor K β*
      ENNReal.ofReal ((T : ℝ)^((1-(β : ℝ))/2)/((1-(β : ℝ))/2))

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

include hβ1 in
/-- Uniform bracket bound for the literal full infinite-Haar rows of
the cutoff equation. It applies on every finite observation horizon. -/
theorem family_bracket (R T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n) {K : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H,‖U p‖≤K) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal (‖MatrixPointHeatRows.row ((T : ℝ)-(s : ℝ))
      (NativeMatrixEquation.profile F (G_R R) U hU (s,ω)) x i‖^2) ∂SHE.PredictableL2.timeMeasure H) ≤ cap G (C := C) (β := β) K T := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := SHE.PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae hbound
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hb := SublinearHeatFiniteHorizon.row_bound
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower R) hβ1 T H hTH x
    (fun s => VectorNativeHeatEndpoint.push (U (s,ω)))
    (hω.mono fun s hs => by
      change ‖U (s,ω)‖≤K at hs
      simpa only [LinearIsometry.norm_map] using hs)
  apply (lintegral_mono (fun s => row_energy G hG hβ ell hell hLower F U hU R (s,ω) ((T : ℝ)-(s : ℝ)) x i)).trans
  simpa only [cap,MatrixUnboundedHeatRows.zero] using hb

variable (hH : (H : ℝ)≤1)

def input (R T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n) : Process (E := Input (d := Fin n)) F μ H :=
  MatrixPointHeatInput.input F μ H hH (NativeMatrixEquation.cap (G_R R))
    (NativeMatrixEquation.cap_nonneg (G_R R)) (NativeMatrixEquation.profile F (G_R R) U hU)
    (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F (G_R R) U hU) T hTH x i

include hβ1 in
/-- The radius-independent bound survives passage to the selected
predictable L2 representative used by the actual stochastic integral. -/
theorem input_bracket (R T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n) {K : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H,‖U p‖≤K) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal (‖input G hG hβ ell hell hLower F U hU μ H hH R T hTH x i (s,ω)‖^2)
      ∂SHE.PredictableL2.timeMeasure H) ≤ cap G (C := C) (β := β) K T := by
  have he := MatrixPointHeatInput.input_ae F μ H hH (NativeMatrixEquation.cap (G_R R))
    (NativeMatrixEquation.cap_nonneg (G_R R)) (NativeMatrixEquation.profile F (G_R R) U hU)
    (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F (G_R R) U hU) T hTH x i
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := SHE.PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs,
    family_bracket G hG hβ hβ1 ell hell hLower F U hU μ H R T hTH x i hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun s hs => congrArg (fun z => ENNReal.ofReal (‖z‖^2)) hs)).trans_le hb

include hβ1 in
/-- Every positive even moment for the actual cutoff-equation point
convolution, with a bound independent of the artificial coefficient cap. -/
theorem native_moment (R T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n) {K : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H,‖U p‖≤K)
    (N : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode)) (p : ℕ) (hp : 0<p) :
    (∫⁻ ω,ENNReal.ofReal (‖(FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
      (input G hG hβ ell hell hLower F U hU μ H hH R T hTH x i) ω‖^(2*p)) ∂μ) ≤
      (NativeScalarBDGAll.constant p : ℝ≥0∞)*cap G (C := C) (β := β) K T^p := by
  apply (NativeScalarBDGAll.power N MatrixPredictableHaarRotation.basis p hp _).trans
  calc
    _ ≤ (NativeScalarBDGAll.constant p : ℝ≥0∞)*∫⁻ _ : Ω,cap G (C := C) (β := β) K T^p ∂μ :=
      mul_le_mul_right (lintegral_mono_ae ((input_bracket G hG hβ hβ1 ell hell hLower F U hU μ H hH
        R T hTH x i hbound).mono fun ω hω => pow_le_pow_left₀ zero_le hω p)) _
    _ = _ := by simp

end SHEStochastic.MatrixUnboundedPointMoments
