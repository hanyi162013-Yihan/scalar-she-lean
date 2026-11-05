module
public import SHE.NativeContinuousPath
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeZeroPathLaw
open MeasureTheory Set
open scoped NNReal
variable {Ω E:Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- An almost surely prescribed initial state determines the actual
zero-horizon continuous-path law, including for arbitrary source spaces. -/
theorem dirac (μ:Measure Ω) [IsProbabilityMeasure μ]
    (U:ℝ≥0→Ω→E) (hc:∀ω,Continuous (fun t=>U t ω)) (u₀:E)
    (hzero:U 0=ᵐ[μ] fun _=>u₀) :
    μ.map (NativeContinuousPath.path 0 U hc)=Measure.dirac (ContinuousMap.const (Icc (0:ℝ) 0) u₀) := by
  have he : NativeContinuousPath.path 0 U hc=ᵐ[μ]
      (fun _=>ContinuousMap.const (Icc (0:ℝ) 0) u₀) := by
    filter_upwards [hzero] with ω hω
    apply ContinuousMap.ext
    intro t
    have ht : t.val=0 := le_antisymm t.2.2 t.2.1
    change U t.val.toNNReal ω=u₀
    rw [ht,Real.toNNReal_zero]
    exact hω
  rw [Measure.map_congr he]
  simp
end SHE.NativeZeroPathLaw
