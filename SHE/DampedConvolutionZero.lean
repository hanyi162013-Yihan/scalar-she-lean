module
public import SHE.DampedNonlinearConvolution
import all SHE.DampedKernelModel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.DampedConvolutionZero
open MeasureTheory PredictableL2 LowBands NonlinearHaarIntegrand Filter Topology
open HaarKernelApproximation
open scoped NNReal ENNReal
local instance :Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance :MeasurableSpace CircleHeat.CircleL2:=borel _
local instance :BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance :MeasurableSpace Columns:=borel _
local instance :BorelSpace Columns:=⟨rfl⟩
local instance :MeasurableSpace StateL2:=borel _
local instance :BorelSpace StateL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](h:ℝ≥0)
variable {ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable (f:ℝ≥0×Ω→FiniteHaar.EllipticField ell M)(hf:StronglyMeasurable[𝓕.predictable] f)

theorem input(n k:ℕ):DampedCellIntegrands.input 𝓕 μ h (Λ:=0) (by norm_num) hell hM f hf n k=
    HaarItoApproximation.input 𝓕 μ h hell hM f hf n k:=by
  have he:DampedCellIntegrands.kernel (Λ:=0) hell f n k=HaarCellIntegrands.kernel hell f n k:=by
    funext p
    simp only [DampedCellIntegrands.kernel,neg_zero,zero_mul,Real.exp_zero,one_smul]
  simp only [DampedCellIntegrands.input,HaarItoApproximation.input,HaarCellIntegrands.process,he]

/-- Zero damping gives exactly the original Haar convolution process,
because the actual finite predictable inputs and their limits agree. -/
theorem convolution(hh:(h:ℝ)≤1)(I:StandardTerminalIto (C:=Columns) (E:=StateL2) 𝓕 μ h):
    DampedStochasticConvolution.convolution 𝓕 μ h hh (Λ:=0) (by norm_num) hell hM I f hf=
      HaarStochasticConvolution.convolution 𝓕 μ h hell hM I f hf:=by
  unfold DampedStochasticConvolution.convolution KernelItoLimit.convolution HaarStochasticConvolution.convolution
  congr 1
  funext n
  change PredictableItoCells.output I n (DampedCellIntegrands.input 𝓕 μ h (Λ:=0) (by norm_num) hell hM f hf n) _=
    PredictableItoCells.output I n (HaarItoApproximation.input 𝓕 μ h hell hM f hf n) _
  have he:DampedCellIntegrands.input 𝓕 μ h (Λ:=0) (by norm_num) hell hM f hf n=
      HaarItoApproximation.input 𝓕 μ h hell hM f hf n:=funext (input 𝓕 μ h hell hM f hf n)
  simp only [he]

variable {a:ℝ→ℝ}(ha:Measurable a)(hb:∀z,ell≤a z ∧ a z≤M)
variable {β K:ℝ}(hβ:0<β)(hK:0≤K)(hholder:∀z w,|a z-a w|≤K*|z-w|^β)

/-- The map used in the full-horizon Bielecki iteration is the same
undamped map used to construct the actual continuous Picard versions. -/
theorem nonlinear(hh:(h:ℝ)≤1)(I:StandardTerminalIto (C:=Columns) (E:=StateL2) 𝓕 μ h)
    (u:Process (E:=StateL2) 𝓕 μ h):
    DampedNonlinearConvolution.map 𝓕 μ h hh (Λ:=0) (by norm_num) ha hell hb hβ hK hholder I u=
      NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hK hholder I u:=by
  exact convolution 𝓕 μ h hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (NonlinearConvolution.field 𝓕 μ h ha hell hb u)
    (NonlinearConvolution.field_predictable 𝓕 μ h ha hell hb hβ hK hholder u) hh I

end SHE.DampedConvolutionZero
