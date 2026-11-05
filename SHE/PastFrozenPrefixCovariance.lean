module

public import SHE.PastFrozenPrefixRows
public import SHE.LocalTwoChannelIto
public import SHE.NonlinearTwoChannelStep
public import SHE.ControlledReferenceWindows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.PastFrozenPrefixCovariance
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier ControlledProfile
open GaussianItoTest CovarianceMatrix OrthogonalItoChannels
open scoped NNReal ENNReal
local instance pastFrozenPrefixCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance pastFrozenPrefixCovariance_sigma : MeasurableSpace CircleL2 := borel _
local instance pastFrozenPrefixCovariance_borel : BorelSpace CircleL2 := ⟨rfl⟩
local instance pastFrozenPrefixCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance pastFrozenPrefixCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance pastFrozenPrefixCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance pastFrozenPrefixCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ θ : ℝ) (hκ0 : 0<κ) (hκP : κ<P.lower)
variable (v : ℝ≥0) (data : Ω→Inputs) (hdata : Measurable[𝓕 v] data)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (c : ℝ≥0)
variable (hgap : ∀ i,(c:ℝ)<(Z i).target)

/-- The literal common additive/residual rows have TOTAL canonical
profile covariance after their actual random past, on the SAME drivers. -/
theorem density_sum_eq {t : ℝ} (htv : (v:ℝ)<t) (htc : t≤(c:ℝ)) (ω : Ω)
    {δ : ℝ} (hδ : 0<δ) (hg : ∀ i,δ≤(Z i).target-(c:ℝ)) :
    densityMatrix (NativeItoBracket.coefficient (fun _ : ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ0) ω) Z t+
      densityMatrix (NativeItoBracket.coefficient (FrozenReferenceFields.field P Λ κ θ hκP v data) ω) Z t=
    densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v (data ω)) Z t := by
  have ht0 : 0≤t:=v.2.trans htv.le
  have htvNN : v<t.toNNReal := by
    change (v:ℝ)<(t.toNNReal:ℝ)
    rw [Real.coe_toNNReal _ ht0]
    exact htv
  have h₀ : densityMatrix
      (NativeItoBracket.coefficient (fun _ : ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ0) ω) Z t=
      densityMatrix (fun _=>κ) Z t := by
    ext i j
    apply integral_congr_ae
    filter_upwards [NonlinearTwoChannelStep.constant_native_ae κ hκ0] with x hx
    change (CircleNormalization.push (AdditiveHaarForcing.constantField κ hκ0).val x).re*
      WordRecursion.heatRow Z t x i*WordRecursion.heatRow Z t x j=_
    rw [hx]
  have h₁ : densityMatrix
      (NativeItoBracket.coefficient (FrozenReferenceFields.field P Λ κ θ hκP v data) ω) Z t=
      densityMatrix (fun p=>ControlledReferenceWindows.coefficient P Λ θ v (data ω) p-κ) Z t := by
    ext i j
    apply integral_congr_ae
    filter_upwards [FrozenReferenceFields.field_ae P Λ κ θ hκP v data (t.toNNReal,ω) htvNN] with x hx
    simp only [Real.coe_toNNReal _ ht0] at hx
    change (CircleNormalization.push (FrozenReferenceFields.field P Λ κ θ hκP v data (t.toNNReal,ω)).val x).re*
      WordRecursion.heatRow Z t x i*WordRecursion.heatRow Z t x j=_
    rw [hx]
    rfl
  rw [h₀,h₁]
  have hm : Measurable (fun p=>ControlledReferenceWindows.coefficient P Λ θ v (data ω) p-κ):=
    (ControlledReferenceWindows.coefficient_section_measurable P Λ θ v (data ω)).sub_const κ
  have he:=NonlinearTwoChannelStep.densityMatrix_add (fun _=>κ)
    (fun p=>ControlledReferenceWindows.coefficient P Λ θ v (data ω) p-κ)
    measurable_const hm Z hδ hκ0.le (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) hg htc
    (fun _=>by rw [abs_of_pos hκ0]) (fun x=>by
      have hb:=ControlledReferenceWindows.coefficient_bounds P Λ θ v (data ω) (t,x)
      rw [abs_of_nonneg (by linarith : 0≤ControlledReferenceWindows.coefficient P Λ θ v (data ω) (t,x)-κ)]
      linarith)
  convert he using 1
  congr 1
  funext p
  ring

/-- Actual random frozen row Gram equals its actual conditional TOTAL
covariance density. This is one original sample/time event; no
parameterwise almost-everywhere substitution is used. -/
theorem rowCovariance_eq_profile (hcH : c≤H) {δ : ℝ} (hδ : 0<δ)
    (hg : ∀ i,δ≤(Z i).target-(c:ℝ)) :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ H
        (PastFrozenPrefixRows.rows 𝓕 μ H P Λ κ θ hκ0 hκP v data hdata Z c hgap) ω t=
      densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v (data ω)) Z t := by
  have hh:=LocalTwoChannelIto.rowCovariance_eq_sum 𝓕 μ H hκ0 hκ0.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ0) stronglyMeasurable_const
    (sub_pos.mpr hκP) (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ θ hκP v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v data hdata) Z c hδ hg hcH
  have hs : Ioc (v:ℝ) (c:ℝ)⊆Ioc (0:ℝ) (c:ℝ):=fun _ ht=>⟨v.2.trans_lt ht.1,ht.2⟩
  filter_upwards [hh] with ω hω
  have hω':=hω.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  filter_upwards [hω',ae_restrict_mem measurableSet_Ioc] with t ht htm
  exact ht.trans (density_sum_eq P Λ κ θ hκ0 hκP v data Z c htm.1 htm.2 ω hδ hg)

end SHE.PastFrozenPrefixCovariance
