module

public import SHE.MovingParameterFractional
public import SHE.OrderedGapCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.InitialGapCurrent
open Set MeasureTheory OrderedGapCoordinates
open scoped ENNReal BigOperators
local instance initialGapCurrent_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Ordered original old times become genuine positive gaps with the
newest current clock retained as T minus their sum. -/
theorem ordered_clock (k:ℕ) (T:ℝ) (K:(Fin k→ℝ)→ℝ≥0∞) (G:ℝ→ℝ≥0∞)
    (hK:Measurable K) (hG:Measurable G):
    (∫⁻t:Fin k→ℝ,if ordered 0 T k t then K (gaps T k t)*G (boundary T k t) else 0)=
      ∫⁻d:Fin k→ℝ,if (∀j,0<d j) ∧ (∑j,d j)<T then K d*G (T-∑j,d j) else 0:=by
  classical
  have hm:Measurable (fun d:Fin k→ℝ=>K d*G (T-∑j,d j)):=
    hK.mul (hG.comp (measurable_const.sub (Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j))))
  have he:=ordered_lintegral 0 T k (fun d:Fin k→ℝ=>K d*G (T-∑j,d j)) hm
  simpa only [sum_gaps,sub_sub_cancel,sub_zero] using he

/-- Initial output triangles count the TRUE newest-current energy
once by positive convolution. There is no moving-past evaluation at
zero and no pointwise input-energy substitute. -/
theorem energy_bound (k:ℕ) (K:(Fin k→ℝ)→ℝ≥0∞) (F:ℝ→ℝ≥0∞)
    (hK:Measurable K) (hF:Measurable F) {χ h H:ℝ}
    (hχ:0≤χ) (hχ1:χ≤1) (hhH:h≤H):
    (∫⁻T in Ioc (0:ℝ) h,∫⁻t:Fin k→ℝ,if ordered 0 T k t then
      K (gaps T k t)*MovingPastFractional.powerWindow H χ F (boundary T k t) else 0)≤
      (∫⁻d:Fin k→ℝ,K d)*((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)):=by
  classical
  let G:=MovingPastFractional.powerWindow H χ F
  have hG:Measurable G:=MovingPastFractional.powerWindow_measurable hF H χ
  have hq:Measurable (fun d:Fin k→ℝ=>-(∑j,d j)):=
    (Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j)).neg
  calc
    _=(∫⁻T in Ioc (0:ℝ) h,∫⁻d:Fin k→ℝ,if (∀j,0<d j) ∧ (∑j,d j)<T then K d*G (T-∑j,d j) else 0):=by
      apply lintegral_congr
      intro T
      exact ordered_clock k T K G hK hG
    _≤∫⁻T in Ioc (0:ℝ) h,∫⁻d:Fin k→ℝ,K d*G (T-∑j,d j):=by
      apply lintegral_mono
      intro T
      apply lintegral_mono
      intro d
      dsimp only
      split_ifs <;> first |exact le_rfl|exact bot_le
    _≤∫⁻T in Ioc (0:ℝ) H,∫⁻d:Fin k→ℝ,K d*G (T-∑j,d j):=
      lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hhH) le_rfl) le_rfl
    _≤_:=by
      convert! MovingParameterFractional.current (volume:Measure (Fin k→ℝ)) K
        (fun d:Fin k→ℝ=>-(∑j,d j)) F hK hq hF hχ hχ1 H using 1

end SHE.InitialGapCurrent
