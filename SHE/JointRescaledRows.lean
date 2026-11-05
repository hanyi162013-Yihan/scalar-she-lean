module

public import SHE.InterpolatedPredictableRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SHE.JointRescaledRows
open MeasureTheory PredictableL2 OrthogonalItoChannels PredictableItoRotation
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
local instance jointRescaledRows_blockSigma : MeasurableSpace (Both C):=borel _
local instance jointRescaledRows_blockBorel : BorelSpace (Both C):=⟨rfl⟩
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) (H:ℝ≥0)

/-- The original integrating factor gives the true JOINT convex row,
with the remaining TARGET age. One event works for every scalar weight
and every original target, so no random-parameter AE substitution occurs. -/
theorem convex_ae {Λ:ℝ} (hΛ:0≤Λ) (b:ℝ≥0)
    (a u v:Process (E:=C) 𝓕 μ H) :
    ∀ᵐ p∂energyMeasure μ H,p.1≤b→∀θ T:ℝ,
      TwoChannelItoRows.block 𝓕 μ H a u p+(θ*Real.exp (-Λ*T)) •
        InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b u v p=
      WithLp.toLp 2 (a p,(1-θ*Real.exp (-Λ*(T-(p.1:ℝ)))) • u p+
        (θ*Real.exp (-Λ*(T-(p.1:ℝ)))) • v p) := by
  filter_upwards [InterpolatedPredictableRows.interpolated_ae 𝓕 μ H hΛ b 1 a u v,
    TwoChannelItoRows.block_ae 𝓕 μ H a u] with p hi hb hpb θ T
  have h1:=hi hpb
  have hcoef:ClippedExponential.coefficient Λ 1 (p.1:ℝ)=Real.exp (-Λ*(p.1:ℝ)):=by
    simp only [ClippedExponential.coefficient,ClippedExponential.damping_eq p.1.coe_nonneg,one_mul]
  rw [hcoef,hb] at h1
  simp only [sub_self,zero_smul,one_smul,zero_add] at h1
  have hd : Real.exp (-Λ*(p.1:ℝ)) •
      InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b u v p=
      WithLp.toLp 2 (0,v p-u p) := by
    apply add_left_cancel (a:=WithLp.toLp 2 (a p,u p))
    rw [h1]
    apply WithLp.ofLp_injective
    change (a p,v p)=(a p,u p)+(0,v p-u p)
    ext <;> simp
  have hexp : (θ*Real.exp (-Λ*(T-(p.1:ℝ))))*Real.exp (-Λ*(p.1:ℝ))=
      θ*Real.exp (-Λ*T) := by
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  rw [hb,←hexp,mul_smul,hd]
  apply WithLp.ofLp_injective
  change (a p,u p)+(θ*Real.exp (-Λ*(T-(p.1:ℝ)))) • (0,v p-u p)=_
  ext
  · simp
  · change u p+(θ*Real.exp (-Λ*(T-(p.1:ℝ)))) • (v p-u p)=_
    module

end SHE.JointRescaledRows
