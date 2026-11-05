module
public import SHE.NativeGammaAgeMeasure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeCurrentWindowMeasure
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω:Type*}[MeasurableSpace Ω]

/-- The SAME full-horizon stochastic energy measure on the physical
window is exactly relative current time s=q-v. The two endpoints are
removed solely by Lebesgue nullity. -/
theorem product(μ:Measure Ω)[SFinite μ](H v b:ℝ≥0)(hbH:b≤H)
    (F:(ℝ≥0×Ω)→ℝ≥0∞)(hF:Measurable F):
    (∫⁻p,(NativeGammaClock.window v b).indicator F p ∂energyMeasure μ H)=
      ∫⁻s in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,F (((v:ℝ)+s).toNNReal,ω) ∂μ:=by
  let h:ℝ:=(b:ℝ)-(v:ℝ)
  let G:ℝ→ℝ≥0∞:=fun τ=>∫⁻ω,F (((b:ℝ)-τ).toNNReal,ω) ∂μ
  have hp:MeasurePreserving (fun s:ℝ=>h-s)
      (volume.restrict (Ioo (0:ℝ) h)) (volume.restrict (Ioo (0:ℝ) h)):=by
    have hh:=((volume:Measure ℝ).measurePreserving_sub_left h).restrict_preimage
      (measurableSet_Ioo:MeasurableSet (Ioo (0:ℝ) h))
    have he:(fun s:ℝ=>h-s) ⁻¹' Ioo (0:ℝ) h=Ioo (0:ℝ) h:=by
      ext s
      simp only [mem_preimage,mem_Ioo]
      constructor <;> intro hs <;> constructor <;> linarith [hs.1,hs.2]
    rwa [he] at hh
  calc
    _=∫⁻τ in Ioc (0:ℝ) h,G τ:=NativeGammaAgeMeasure.product μ H v b hbH F hF
    _=∫⁻τ in Ioo (0:ℝ) h,G τ:=by rw [restrict_Ioo_eq_restrict_Ioc]
    _=∫⁻s in Ioo (0:ℝ) h,G (h-s):=
      (hp.lintegral_comp_emb (MeasurableEquiv.subLeft h).measurableEmbedding G).symm
    _=∫⁻s in Ioc (0:ℝ) h,∫⁻ω,F (((v:ℝ)+s).toNNReal,ω) ∂μ:=by
      rw [←restrict_Ioo_eq_restrict_Ioc]
      apply lintegral_congr
      intro s
      have he:(b:ℝ)-(h-s)=(v:ℝ)+s:=by dsimp only [h];ring
      simp only [G,he]

end SHE.NativeCurrentWindowMeasure
