module

public import SHEStochastic.MatrixFixedApproximation
public import SHEStochastic.KernelItoVersion
public import SHEStochastic.LpSections
public import SHEStochastic.FamilyLpRepresentative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixKernelVersion
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ) ≤ 1) {U : ℝ} (hU : 0 ≤ U)
    (a : Fields (d := d) F U)

/-- The target is clamped only outside the declared horizon. -/
def input (t : ℝ≥0) : Process (E := MatrixHaarKernel.Columns (d := d)) F μ H :=
  MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable (min t H) (min_le_right _ _)

theorem input_stronglyMeasurable : StronglyMeasurable (input (μ := μ) hH hU a) := by
  let ν := (energyMeasure μ H).trim (predictable_le_product F)
  have : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  have : IsFiniteMeasure ν := inferInstance
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let r : ℝ≥0 × (ℝ≥0 × Ω) → MatrixHaarKernel.Columns (d := d) :=
    fun z => MatrixAnalyticKernel.kernel ((min z.1 H : ℝ)-(z.2.1 : ℝ)) (a.value z.2)
  have hclock : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) => (min z.1 H : ℝ)-(z.2.1 : ℝ)) :=
    (measurable_coe_nnreal_real.comp (measurable_fst.min measurable_const)).sub
      ((PredictableClock.real_time_measurable F).comp measurable_snd)
  have hr : StronglyMeasurable r :=
    (MatrixAnalyticKernel.measurable _ hclock (fun z => a.value z.2)
      (a.measurable.comp (measurable_fst.snd.prodMk measurable_snd))).stronglyMeasurable
  apply LpSections.stronglyMeasurable_of_joint ν (input hH hU a) r hr
  intro t
  exact (MatrixAnalyticConvolution.memLp F μ H hH U hU a.value a.upper a.measurable
    (min t H) (min_le_right _ _)).coeFn_toLp

variable (N : FiniteScalarIto.Family F μ H (d × HaarNode))

def fixedValue (t : ℝ≥0) : Lp (Physical (d := d)) 2 μ :=
  (NativeMatrixConvolution.terminalIto N).integral (input hH hU a t)

theorem fixedValue_stronglyMeasurable : StronglyMeasurable (fixedValue hH hU a N) :=
  (NativeMatrixConvolution.terminalIto N).integral.continuous.comp_stronglyMeasurable
    (input_stronglyMeasurable hH hU a)

/-- A joint measurable representative of the original fixed-time
native integrals, obtained from the already available L2-family tool. -/
def version : ℝ≥0 × Ω → Physical (d := d) :=
  FamilyLpRepresentative.representative μ (fixedValue hH hU a N)
    (fixedValue_stronglyMeasurable hH hU a N)

theorem version_measurable : Measurable (version hH hU a N) :=
  FamilyLpRepresentative.representative_measurable μ _ _

theorem version_ae (t : ℝ≥0) (ht : t ≤ H) :
    (fun ω => version hH hU a N (t,ω)) =ᵐ[μ]
      MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t ht := by
  have he := FamilyLpRepresentative.representative_ae μ (fixedValue hH hU a N)
    (fixedValue_stronglyMeasurable hH hU a N) t
  simpa only [version,fixedValue,input,min_eq_left ht,MatrixAnalyticConvolution.value] using he

/-- The complete predictable convolution is the literal original
native heat integral at almost every physical time and sample. -/
theorem convolution_ae_version :
    MatrixPredictableConvolution.convolution hH U hU N a =ᵐ[energyMeasure μ H] version hH hU a N := by
  exact KernelItoVersion.convolution_ae_version (model F μ H hH U hU)
    (NativeMatrixConvolution.terminalIto N) a
    (fun t ht => MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t ht)
    (fun t ht htH => MatrixFixedApproximation.integral_tendsto hH hU a N t ht htH)
    (version hH hU a N) (version_measurable hH hU a N).stronglyMeasurable
    (version_ae hH hU a N)

end SHEStochastic.MatrixKernelVersion
